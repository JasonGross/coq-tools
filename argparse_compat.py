import sys
if sys.version_info < (3,):
    import argparse_py2 as argparse
else:
    import argparse
