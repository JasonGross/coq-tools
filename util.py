__all__ = ["prompt", "yes_no_prompt", "format_text", "NO_COLOR", "RED", "GREEN"]


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

NO_COLOR = 'no_color'
RED = 'red'
GREEN = 'green'

COLORS = (RED, GREEN)

FORMATS = {NO_COLOR : r'\033[0m',
           RED      : r'\033[0;31m',
           GREEN    : r'\033[0;32m'}

def format_text_helper(text, fmt):
    if fmt in COLORS:
        return '%s%s%s' % (FORMATS[fmt], text, FORMATS[NO_COLOR])
    return text

def format_text(text, *fmts):
    for fmt in fmts:
        text = format_text_helper(text, fmt)
    return text
