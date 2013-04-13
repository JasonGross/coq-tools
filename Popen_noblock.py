# from http://stackoverflow.com/questions/375427/non-blocking-read-on-a-subprocess-pipe-in-python

import sys
from subprocess import PIPE
import subprocess
from threading  import Thread

__all__ = ["Popen_async", "Empty", "PIPE"]

try:
    from Queue import Queue, Empty
except ImportError:
    from queue import Queue, Empty  # python 3.x

ON_POSIX = 'posix' in sys.builtin_module_names

def enqueue_output(out, queue):
    for line in iter(out.readline, b''):
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
        self._terr = Thread(target=enqueue_output, args=(self._p.stderr, self.stderr))
        self._tout.daemon = True # thread dies with the program
        self._terr.daemon = True # thread dies with the program
        self._tout.start()
        self._terr.start()
    def __getattr__(self, name):
        # http://docs.python.org/2/reference/datamodel.html#object.__getattr__ says:
        #
        # Direct Call
        #
        # The simplest and least common call is when user code
        # directly invokes a descriptor method: x.__get__(a).
        #
        # Instance Binding
        #
        # If binding to a new-style object instance, a.x is
        # transformed into the call: type(a).__dict__['x'].__get__(a,
        # type(a)).
        #
        # Class Binding
        #
        # If binding to a new-style class, A.x is transformed into the
        # call: A.__dict__['x'].__get__(None, A).
        #
        # Super Binding
        #
        # If a is an instance of super, then the binding super(B,
        # obj).m() searches obj.__class__.__mro__ for the base class A
        # immediately preceding B and then invokes the descriptor with
        # the call: A.__dict__['m'].__get__(obj, obj.__class__).

        return type(self._p).__dict__[name].__get__(self._p, type(self._p))
