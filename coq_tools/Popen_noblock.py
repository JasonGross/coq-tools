# from http://stackoverflow.com/questions/375427/non-blocking-read-on-a-subprocess-pipe-in-python

import sys
from subprocess import PIPE, STDOUT
import subprocess, time
from threading import Thread

__all__ = ["Popen_async", "Empty", "PIPE", "STDOUT"]

try:
    from Queue import Queue, Empty
except ImportError:
    from queue import Queue, Empty  # python 3.x

ON_POSIX = "posix" in sys.builtin_module_names


def enqueue_output(out, queue):
    for line in iter((lambda: out.read(1)), b""):
        # print('0: %s' % line)
        queue.put(line)
    out.close()


class Popen_async(object):
    """Allows non-blocking reading from a Popen, by

    p = Popen_async(['myprogram.exe'], stdout=PIPE, stderr=PIPE)
    try:  line = p.stdout.get_nowait() # or p.stdout.get(timeout=.1)
    except Empty:
        print('no output yet')
    else: # got line
    """

    def __init__(self, *args, **kwargs):
        self._p = subprocess.Popen(*args, bufsize=1, close_fds=ON_POSIX, **kwargs)
        self.stdout = Queue()
        self.stderr = Queue()
        self._tout = Thread(target=enqueue_output, args=(self._p.stdout, self.stdout))
        # self._terr = Thread(target=enqueue_output, args=(self._p.stderr, self.stderr))
        self._tout.daemon = True  # thread dies with the program
        # self._terr.daemon = True # thread dies with the program
        self._tout.start()
        # self._terr.start()
        self.stdin = self._p.stdin
        time.sleep(0.1)
