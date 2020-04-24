import sys, re

__all__ = ["prompt", "yes_no_prompt", "b", "s", "cmp_compat", "PY3", "raw_input", "re_escape"]

if sys.version_info < (3,):
    PY3 = False
    def b(x):
        return x
    def s(x):
        return x
else:
    PY3 = True
    def b(x):
        if x is not None: return x.encode()
    def s(x):
        if x is not None: return x.decode('utf-8', 'ignore')
    def cmp(x, y):
        if x < y: return -1
        if y < x: return 1
        return 0
    raw_input = input

if sys.version_info < (3, 7):
    # see https://bugs.python.org/issue29995
    def re_escape(*args, **kwargs):
        ret = re.escape(*args, **kwargs)
        for ch in ':"':
            ret = ret.replace('\\' + ch, ch)
        return ret
else:
    re_escape = re.escape

cmp_compat = cmp

def prompt(options, case_sensitive=False, strip=True, sep='/', prefix='Please enter ', postfix=': '):
    msg = prefix + sep.join(i['display'] for i in options) + postfix
    response = raw_input(msg)
    while True:
        if not case_sensitive:
            response = response.lower()
        if strip:
            response = response.strip()
        for expected in options:
            if response in expected['values']:
                return expected['value']
        print('Response "%s" is not one of %s' % (response, ', '.join(repr(val) for i in options for val in i['values'])))
        response = raw_input(msg)

def yes_no_prompt(**kwargs):
    return prompt(({'value':True, 'display':'(y)es', 'values':('y', 'yes')},
                   {'value':False, 'display':'(n)o', 'values':('n', 'no')}),
                  **kwargs)
