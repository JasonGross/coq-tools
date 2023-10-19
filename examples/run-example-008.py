#!/usr/bin/env python3
import os, sys, inspect, glob

DIR = os.path.dirname(os.path.realpath(__file__))
N = __file__[__file__.rindex('-')+1:__file__.rindex('.')]

NORM_EXPECT='Require Coq.Arith.Arith.\nRequire Top.A.\nRequire Top.C.\nRequire Top.B.\nRequire Top.D.\n\nImport Top.D.\n\nFail Check A.mA.axA.\n'

GET_EXPECT = {
    'Coq.Arith.Arith': None,
    'Top.A': 'Module Export Top_DOT_A.\nModule Export Top.\nModule A.\nImport Coq.Arith.Arith.\nModule mA.\n  Section secA.\n    Axiom axA : Set.\n  End secA.\nEnd mA.\n\nModule mA2.\nEnd mA2.\n\nEnd A.\n\nEnd Top.\n\nEnd Top_DOT_A.\n',
    'Top.B': 'Module Export Top_DOT_B.\nModule Export Top.\nModule B.\nImport Top.A.\n\nEnd B.\n\nEnd Top.\n\nEnd Top_DOT_B.\n',
    'Top.C': 'Module Export Top_DOT_C.\nModule Export Top.\nModule C.\nImport Top.A.\n\nEnd C.\n\nEnd Top.\n\nEnd Top_DOT_C.\n',
    'Top.D': 'Module Export Top_DOT_D.\nModule Export Top.\nModule D.\nImport Top.C Top.B.\nExport Top.A.\n\nEnd D.\n\nEnd Top.\n\nEnd Top_DOT_D.\n'
}

def trace(frame, event, arg):
    print((frame, event, arg))

if __name__ == '__main__':
    # from http://stackoverflow.com/a/6098238/377022
    cmd_subfolder = os.path.realpath(os.path.abspath(os.path.join(os.path.split(inspect.getfile( inspect.currentframe() ))[0], "..")))
    if cmd_subfolder not in sys.path:
        sys.path.insert(0, cmd_subfolder)
    from coq_tools.replace_imports import normalize_requires, get_required_contents
    os.chdir(DIR)
    os.chdir('example_%s' % N)
    for i in glob.glob('*.vo') + glob.glob('*.glob'):
        os.remove(i)
    NORM_FOUND = normalize_requires("example_%s.v" % N)
    print('if %s != %s:' % (repr(NORM_FOUND), repr(NORM_EXPECT)))
    if NORM_FOUND != NORM_EXPECT:
        print('sys.exit(1)')
        sys.exit(1)
    for libname, expect in GET_EXPECT.items():
        print('libname: ' + libname)
        try:
            got = get_required_contents(libname)
        except IOError:
            got = None
        print('if %s != %s:' % (repr(got), repr(expect)))
        if got != expect:
            print('sys.exit(1)')
            sys.exit(1)
    print('sys.exit(0)')
    sys.exit(0)
