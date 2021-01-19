# -*- coding: utf-8-*-
"""
A Speaker handles audio output from Dingdang to the user

Speaker methods:
    say - output 'phrase' as speech
    player - player the audio in 'filename'
    is_available - returns True if the platform supports this implementation
"""
from __future__ import print_function
from __future__ import absolute_import
import os
import platform
import tempfile
import logging
import requests
import datetime
import base64
import hmac
import hashlib
import json
import time
from dateutil import parser as dparser
from abc import ABCMeta, abstractmethod
from uuid import getnode as get_mac
try:
    import urllib.parse as parse
except ImportError:
    import urllib as parse

import argparse

from . import diagnose
from . import dingdangpath
from . import config
from . import player

try:
    import gtts
except ImportError:
    pass

try:
    reload         # Python 2
except NameError:  # Python 3
    from importlib import reload

import sys
reload(sys)
sys.setdefaultencoding('utf8')

# baidu new tts api
IS_PY3 = sys.version_info.major == 3
if IS_PY3:
    from urllib.request import urlopen
    from urllib.request import Request
    from urllib.error import URLError
    from urllib.parse import urlencode
    from urllib.parse import quote_plus
else:
    import urllib2
    from urllib import quote_plus
    from urllib2 import urlopen
    from urllib2 import Request
    from urllib2 import URLError
    from urllib import urlencode


TEXT = "欢迎使用百度语音合成。"

# 发音人选择, 基础音库：0为度小美，1为度小宇，3为度逍遥，4为度丫丫，
# 精品音库：5为度小娇，103为度米朵，106为度博文，110为度小童，111为度小萌，默认为度小美 
PER = 4
# 语速，取值0-15，默认为5中语速
SPD = 5
# 音调，取值0-15，默认为5中语调
PIT = 5
# 音量，取值0-9，默认为5中音量
VOL = 5
# 下载的文件格式, 3：mp3(default) 4： pcm-16k 5： pcm-8k 6. wav
AUE = 3

FORMATS = {3: "mp3", 4: "pcm", 5: "pcm", 6: "wav"}
FORMAT = FORMATS[AUE]

CUID = str(get_mac())[:32] # "123456PYTHON"

TTS_URL = 'http://tsn.baidu.com/text2audio'

"""  TOKEN start """

TOKEN_URL = 'http://openapi.baidu.com/oauth/2.0/token'
SCOPE = 'audio_tts_post'  # 有此scope表示有tts能力，没有请在网页里勾选


def fetch_token(api_key,secret_key):
    # print("fetch token begin")
    params = {'grant_type': 'client_credentials',
              'client_id': api_key,
              'client_secret': secret_key}
    post_data = urlencode(params)
    if (IS_PY3):
        post_data = post_data.encode('utf-8')
    req = Request(TOKEN_URL, post_data)
    try:
        f = urlopen(req, timeout=5)
        result_str = f.read()
    except URLError as err:
        # print('token http response http code : ' + str(err.code))
        result_str = err.read()
    if (IS_PY3):
        result_str = result_str.decode()

    # print(result_str)
    result = json.loads(result_str)
    # print(result)
    if ('access_token' in result.keys() and 'scope' in result.keys()):
        if not SCOPE in result['scope'].split(' '):
            raise DemoError('scope is not correct')
        # print('SUCCESS WITH TOKEN: %s ; EXPIRES IN SECONDS: %s' % (result['access_token'], result['expires_in']))
        return result['access_token']
    else:
        raise DemoError('MAYBE API_KEY or SECRET_KEY not correct: access_token or scope not found in token response')


"""  TOKEN end """




class AbstractTTSEngine(object):
    """
    Generic parent class for all speakers
    """
    __metaclass__ = ABCMeta

    @classmethod
    def get_config(cls):
        return {}

    @classmethod
    def get_instance(cls):
        param = cls.get_config()
        instance = cls(**param)
        return instance

    @classmethod
    @abstractmethod
    def is_available(cls):
        return diagnose.check_executable('aplay')

    def __init__(self, **kwargs):
        self._logger = logging.getLogger(__name__)

    @abstractmethod
    def say(self, phrase, *args):
        pass

    def play(self, filename):
        """
        The method has deprecated, use 'mic.Mic.play' instead.
        play wave by aplay
        """
        sound = player.get_sound_manager()
        sound.play_block(filename)


class AbstractMp3TTSEngine(AbstractTTSEngine):
    """
    Generic class that implements the 'play' method for mp3 files
    """
    SLUG = ''

    @classmethod
    def is_available(cls):
        return (super(AbstractMp3TTSEngine, cls).is_available() and
                diagnose.check_python_import('mad'))

    def play_mp3(self, filename, remove=False):
        music = player.get_music_manager()
        music.play_block(filename)

    def removePunctuation(self, phrase):
        to_remove = [
            ',', '/', ':', '\\', '@', '!', '%', '&', '*', '(',
            ')', '{', '}'
        ]
        for note in to_remove:
            phrase = phrase.replace(note, '')
        return phrase

    def say(self, phrase, cache=False):
        self._logger.debug(u"Saying '%s' with '%s'", phrase, self.SLUG)
        h = hashlib.md5()
        h.update(phrase)
        cache_file_path = os.path.join(
            dingdangpath.TEMP_PATH,
            self.SLUG + h.hexdigest() + '.mp3'
        )
        if cache and os.path.exists(cache_file_path):
            self._logger.info(
                "found speech in cache, playing...[%s]" % cache_file_path)
            self.play_mp3(cache_file_path)
        else:
            tmpfile = self.get_speech(phrase)
            if tmpfile is not None:
                self.play_mp3(tmpfile)
                if cache:
                    self._logger.info(
                        "not found speech in cache," +
                        " caching...[%s]" % cache_file_path)
                    os.rename(tmpfile, cache_file_path)
                else:
                    os.remove(tmpfile)

    def get_speech(self, phrase):
        # The subclass needs to implement
        return None


class BaiduTTS(AbstractMp3TTSEngine):

    SLUG = "baidu-tts"

    def __init__(self, api_id, api_key, secret_key, per=0, **args):
        super(self.__class__, self).__init__()
        self._logger = logging.getLogger(__name__)
        self.api_id = api_id
        self.api_key = api_key
        self.secret_key = secret_key
        self.per = per
        self.token = ''

    @classmethod
    def get_config(cls):
        # Try to get baidu_yuyin config from config
        return config.get('baidu_yuyin', {})

    @classmethod
    def is_available(cls):
        return diagnose.check_network_connection()

    def get_token(self):
        cache = open(os.path.join(dingdangpath.TEMP_PATH, 'baidustt.ini'),
                     'a+')
        try:
            pms = cache.readlines()
            if len(pms) > 0:
                time = pms[0]
                tk = pms[1]
                # 计算token是否过期 官方说明一个月，这里保守29天
                time = dparser.parse(time)
                endtime = datetime.datetime.now()
                if (endtime - time).days <= 29:
                    return tk
        finally:
            cache.close()
        try:
            token = fetch_token(self.api_key,self.secret_key)
            return token
        except requests.exceptions.HTTPError:
            self._logger.critical('Token request failed with response: %r',
                                  r.text,
                                  exc_info=True)
            return ''


    def split_sentences(self, text):
        punctuations = ['.', '。', ';', '；', '\n']
        for i in punctuations:
            text = text.replace(i, '@@@')
        return text.split('@@@')

    def get_speech(self, phrase):
        self._logger.critical('stt>>>> : ' + str(phrase),exc_info=True)
        if self.token == '':
            self.token = fetch_token()
        self._logger.critical('stt token>>>> : ' + str(self.token),exc_info=True)
        self._logger.critical('stt token>>>> : ' + str(phrase),exc_info=True)
        self._logger.critical('stt token>>>> : ' + str(self.per),exc_info=True)
        self._logger.critical('stt token>>>> : ' + str(SPD),exc_info=True)
        self._logger.critical('stt token>>>> : ' + str(PIT),exc_info=True)
        self._logger.critical('stt token>>>> : ' + str(VOL),exc_info=True)
        self._logger.critical('stt token>>>> : ' + str(AUE),exc_info=True)
        self._logger.critical('stt token>>>> : ' + str(get_mac())[:32],exc_info=True)


        params = {'tok': self.token,
                  'tex': phrase,
                  'per': self.per,
                  'spd': SPD,
                  'pit': PIT,
                  'vol': VOL,
                  'aue': AUE,
                  'cuid': str(get_mac())[:32],
                  'lan': 'zh', 'ctp': 1}  # lan ctp 固定参数
        data = urlencode(params)
        req = Request(TTS_URL, data.encode('utf-8'))
        has_error = False
        try:
            f = urlopen(req)
            result_str = f.read()

            headers = dict((name.lower(), value) for name, value in f.headers.items())

            has_error = ('content-type' not in headers.keys() or headers['content-type'].find('audio/') < 0)
        except  URLError as err:
            self._logger.critical('asr http response http code : ' + str(err.code),exc_info=True)
            result_str = err.read()
            has_error = True

        if has_error:
            if (IS_PY3):
                result_str = str(result_str, 'utf-8')
                self._logger.critical("tts api  error:" + result_str.json()['err_msg'],exc_info=True)
                return None

        # try:
        #     result_str.raise_for_status()
        #     if result_str.json()['err_msg'] is not None:
        #         self._logger.critical('Baidu TTS failed with response: %result_str',
        #                               result_str.json()['err_msg'],
        #                               exc_info=True)
        #         return None
        # except Exception:
        #     pass
        with tempfile.NamedTemporaryFile(suffix='.mp3', delete=False) as f:
            f.write(result_str)
            tmpfile = f.name
            return tmpfile


class BaiduTTS2018(AbstractMp3TTSEngine):
    """
    使用百度语音合成技术
    要使用本模块, 首先到 yuyin.baidu.com 注册一个开发者账号,
    之后创建一个新应用, 然后在应用管理的"查看key"中获得 API Key 和 Secret Key
    填入 profile.yml 中.
    ...
        baidu_yuyin: 'AIzaSyDoHmTEToZUQrltmORWS4Ott0OHVA62tw8'
            api_key: 'LMFYhLdXSSthxCNLR7uxFszQ'
            secret_key: '14dbd10057xu7b256e537455698c0e4e'
        ...
    """

    SLUG = "baidu-tts2018"

    def __init__(self, api_id, api_key, secret_key, per=0, **args):
        super(self.__class__, self).__init__()
        self._logger = logging.getLogger(__name__)
        self.api_id = api_id
        self.api_key = api_key
        self.secret_key = secret_key
        self.per = per
        self.token = ''

    @classmethod
    def get_config(cls):
        # Try to get baidu_yuyin config from config
        return config.get('baidu_yuyin', {})

    @classmethod
    def is_available(cls):
        return diagnose.check_network_connection()

    def get_token(self):
        cache = open(os.path.join(dingdangpath.TEMP_PATH, 'baidustt.ini'),
                     'a+')
        try:
            pms = cache.readlines()
            if len(pms) > 0:
                time = pms[0]
                tk = pms[1]
                # 计算token是否过期 官方说明一个月，这里保守29天
                time = dparser.parse(time)
                endtime = datetime.datetime.now()
                if (endtime - time).days <= 29:
                    return tk
        finally:
            cache.close()
        URL = 'http://openapi.baidu.com/oauth/2.0/token'
        params = parse.urlencode({'grant_type': 'client_credentials',
                                  'client_id': self.api_key,
                                  'client_secret': self.secret_key})
        r = requests.get(URL, params=params)
        try:
            r.raise_for_status()
            token = r.json()['access_token']
            return token
        except requests.exceptions.HTTPError:
            self._logger.critical('Token request failed with response: %r',
                                  r.text,
                                  exc_info=True)
            return ''

    def split_sentences(self, text):
        punctuations = ['.', '。', ';', '；', '\n']
        for i in punctuations:
            text = text.replace(i, '@@@')
        return text.split('@@@')

    def get_speech(self, phrase):
        if self.token == '':
            self.token = self.get_token()
        query = {'tex': phrase,
                 'lan': 'zh',
                 'tok': self.token,
                 'ctp': 1,
                 'cuid': str(get_mac())[:32],
                 'per': self.per
                 }
        r = requests.post('http://tsn.baidu.com/text2audio',
                          data=query,
                          headers={'content-type': 'application/json'})
        try:
            r.raise_for_status()
            if r.json()['err_msg'] is not None:
                self._logger.critical('Baidu TTS failed with response: %r',
                                      r.json()['err_msg'],
                                      exc_info=True)
                return None
        except Exception:
            pass
        with tempfile.NamedTemporaryFile(suffix='.mp3', delete=False) as f:
            f.write(r.content)
            tmpfile = f.name
            return tmpfile

class IFlyTekTTS(AbstractMp3TTSEngine):
    """
    使用讯飞的语音合成技术
    要使用本模块, 请先在 profile.yml 中启用本模块并选择合适的发音人.
    """

    SLUG = "iflytek-tts"

    def __init__(self, api_id, api_key, proxy='', voice_name='xiaoyan',
                 speed='50', volume='80', pitch='50', **args):
        super(self.__class__, self).__init__()
        self._logger = logging.getLogger(__name__)
        self.api_id = api_id
        self.api_key = api_key
        self.proxy = proxy
        self.voice_name = voice_name
        self.speed = str(speed)
        self.volume = str(volume)
        self.pitch = str(pitch)

    @classmethod
    def get_config(cls):
        # Try to get iflytek_yuyin config from config
        param = config.get('/iflytek_yuyin/tts', {})
        if 'api_id' not in param or not param['api_id']:
            param['api_id'] = config.get('/iflytek_yuyin/api_id')
        return param

    @classmethod
    def is_available(cls):
        return diagnose.check_network_connection()

    def get_speech(self, phrase):
        url = 'http://api.xfyun.cn/v1/service/v1/tts'
        param = {
            'auf': 'audio/L16;rate=16000',
            'aue': 'lame',
            'voice_name': self.voice_name,
            'speed': self.speed,
            'volume': self.volume,
            'pitch': self.pitch
        }
        xparam = base64.b64encode(json.dumps(param))
        curTime = str(int(time.time()))
        h = hashlib.md5()
        h.update(self.api_key + curTime + xparam)
        header = {
            'X-Appid': self.api_id,
            'X-CurTime': curTime,
            'X-Param': xparam,
            'X-CheckSum': h.hexdigest(),
            'Content-Type': 'application/x-www-form-urlencoded; charset=utf-8'
        }
        data = {
            'text': phrase.encode('utf8')
        }
        if self.proxy:
            session = requests.session()
            session.proxies = {
                'http': self.proxy,
                'https': self.proxy
            }
            resp = session.post(url, data=parse.urlencode(data),
                                headers=header, )
        else:
            resp = requests.post(url, data=parse.urlencode(data),
                                 headers=header)
        if resp.headers['Content-Type'] != 'audio/mpeg':
            self._logger.error("get tts by xunfei error, resp:%s", resp.text)
            return None
        with tempfile.NamedTemporaryFile(suffix='.mp3', delete=False) as f:
            f.write(resp.content)
            return f.name


class ALiBaBaTTS(AbstractMp3TTSEngine):
    """
    使用阿里云的语音合成技术
    要使用本模块, 请先在 profile.yml 中启用本模块并选择合适的发音人.
    """

    SLUG = "ali-tts"

    def __init__(self, ak_id, ak_secret, voice_name='xiaoyun', **args):
        super(self.__class__, self).__init__()
        self._logger = logging.getLogger(__name__)
        self.ak_id = ak_id
        self.ak_secret = ak_secret
        self.voice_name = voice_name

    @classmethod
    def get_config(cls):
        # Try to get ali_yuyin config from config
        return config.get('ali_yuyin', {})

    @classmethod
    def is_available(cls):
        return diagnose.check_network_connection()

    def split_sentences(self, text):
        punctuations = ['.', '。', ';', '；', '\n']
        for i in punctuations:
            text = text.replace(i, '@@@')
        return text.split('@@@')

    def get_current_date(self):
        date = datetime.datetime.strftime(datetime.datetime.utcnow(),
                                          "%a, %d %b %Y %H: %M: %S GMT")
        return date

    def to_md5_base64(self, strBody):
        hash = hashlib.md5()
        hash.update(strBody)
        return hash.digest().encode('base64').strip()

    def to_sha1_base64(self, stringToSign, secret):
        hmacsha1 = hmac.new(str(secret), str(stringToSign), hashlib.sha1)
        return base64.b64encode(hmacsha1.digest())

    def get_speech(self, phrase):
        options = {
            'url': 'http://nlsapi.aliyun.com/speak?encode_type=' +
            'mp3&voice_name=' + self.voice_name + '&volume=50',
            'method': 'POST',
            'body': phrase.encode('utf8'),
        }
        headers = {
            'date': self.get_current_date(),
            'content-type': 'text/plain',
            'authorization': '',
            'accept': 'audio/wav, application/json'
        }

        body = ''
        if 'body' in options:
            body = options['body']

        bodymd5 = ''
        if not body == '':
            bodymd5 = self.to_md5_base64(body)

        stringToSign = options['method'] + '\n' + headers['accept'] + '\n' + \
            bodymd5 + '\n' + headers['content-type'] + '\n' + headers['date']
        signature = self.to_sha1_base64(stringToSign, self.ak_secret)
        authHeader = 'Dataplus ' + self.ak_id + ':' + signature
        headers['authorization'] = authHeader
        url = options['url']
        r = requests.post(url, data=body, headers=headers, verify=False)
        with tempfile.NamedTemporaryFile(suffix='.mp3', delete=False) as f:
            f.write(r.content)
            tmpfile = f.name
            return tmpfile


class GoogleTTS(AbstractMp3TTSEngine):
    """
    Uses the Google TTS online translator
    Requires pymad and gTTS to be available
    """

    SLUG = "google-tts"

    def __init__(self, language='en', **args):
        super(self.__class__, self).__init__()
        self.language = language

    @classmethod
    def is_available(cls):
        return (super(cls, cls).is_available() and
                diagnose.check_python_import('gtts') and
                diagnose.check_network_connection())

    @classmethod
    def get_config(cls):
        # Try to get google_yuyin from config
        return config.get('google_yuyin', {})

    @property
    def languages(self):
        langs = ['af', 'sq', 'ar', 'hy', 'ca', 'zh-CN', 'zh-TW', 'hr', 'cs',
                 'da', 'nl', 'en', 'eo', 'fi', 'fr', 'de', 'el', 'ht', 'hi',
                 'hu', 'is', 'id', 'it', 'ja', 'ko', 'la', 'lv', 'mk', 'no',
                 'pl', 'pt', 'ro', 'ru', 'sr', 'sk', 'es', 'sw', 'sv', 'ta',
                 'th', 'tr', 'vi', 'cy', 'zh-yue']
        return langs

    def get_speech(self, phrase):
        if self.language not in self.languages:
            raise ValueError("Language '%s' not supported by '%s'",
                             self.language, self.SLUG)
        tts = gtts.gTTS(text=phrase, lang=self.language)
        with tempfile.NamedTemporaryFile(suffix='.mp3', delete=False) as f:
            tmpfile = f.name
        tts.save(tmpfile)
        return tmpfile


def get_default_engine_slug():
    return 'osx-tts' if platform.system().lower() == 'darwin' else 'espeak-tts'


def get_engine_by_slug(slug=None):
    """
    Returns:
        A speaker implementation available on the current platform

    Raises:
        ValueError if no speaker implementation is supported on this platform
    """

    if not slug or type(slug) is not str:
        raise TypeError("Invalid slug '%s'", slug)

    selected_engines = filter(lambda engine: hasattr(engine, "SLUG") and
                              engine.SLUG == slug, get_engines())
    if len(selected_engines) == 0:
        raise ValueError("No TTS engine found for slug '%s'" % slug)
    else:
        if len(selected_engines) > 1:
            print("WARNING: Multiple TTS engines found for slug '%s'. " +
                  "This is most certainly a bug." % slug)
        engine = selected_engines[0]
        if not engine.is_available():
            raise ValueError(("TTS engine '%s' is not available (due to " +
                              "missing dependencies, etc.)") % slug)
        return engine


def get_engines():
    def get_subclasses(cls):
        subclasses = set()
        for subclass in cls.__subclasses__():
            subclasses.add(subclass)
            subclasses.update(get_subclasses(subclass))
        return subclasses
    return [tts_engine for tts_engine in
            list(get_subclasses(AbstractTTSEngine))
            if hasattr(tts_engine, 'SLUG') and tts_engine.SLUG]


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Dingdang TTS module')
    parser.add_argument('--debug', action='store_true',
                        help='Show debug messages')
    args = parser.parse_args()

    logging.basicConfig()
    if args.debug:
        logger = logging.getLogger(__name__)
        logger.setLevel(logging.DEBUG)

    engines = get_engines()
    available_engines = []
    for engine in get_engines():
        if engine.is_available():
            available_engines.append(engine)
    disabled_engines = list(set(engines).difference(set(available_engines)))
    print("Available TTS engines:")
    for i, engine in enumerate(available_engines, start=1):
        print("%d. %s" % (i, engine.SLUG))

    print("")
    print("Disabled TTS engines:")

    for i, engine in enumerate(disabled_engines, start=1):
        print("%d. %s" % (i, engine.SLUG))

    print("")
    for i, engine in enumerate(available_engines, start=1):
        print("%d. Testing engine '%s'..." % (i, engine.SLUG))
        engine.get_instance().say("This is a test.")
    print("Done.")
