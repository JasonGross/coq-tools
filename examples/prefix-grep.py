from __future__ import with_statement
import subprocess, sys

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

GOOD = True
BAD = False
INVALID = None

def binary_search_on_string(f, arg):
    start = 0
    mid = 0
    end = len(arg)
    while mid < end and f(arg[start:end]) is not GOOD:
        new_end = (mid + end) / 2
        if new_end == end:
            new_end -= 1
        if new_end <= mid:
            end = mid
        else:
            ret = f(arg[start:new_end])
            if ret is GOOD:
                mid = new_end
            elif ret is BAD:
                end = new_end
            else:
                orig_new_end = new_end
                while ret is INVALID and new_end < end:
                    new_end += 1
                    ret = f(arg[start:new_end])
                if mid < new_end and ret is GOOD:
                    mid = new_end
                elif new_end < end and ret is BAD:
                    end = new_end
                else:
                    new_end = orig_new_end
                    while ret is INVALID and mid < new_end:
                        new_end -= 1
                        ret = f(arg[start:new_end])
                    if mid == new_end:
                        end = new_end
                    elif ret is GOOD:
                        mid = new_end
                    elif ret is BAD:
                        end = new_end
                    else:
                        sys.stderr.write("This should be impossible\n")
                        end = mid
                        break
    while end + 1 < len(arg) and f(arg[start:end + 1]) == GOOD:
        sys.stderr.write("This should be impossible (2)\n")
        end += 1
    orig_end = end
    while end + 1 < len(arg):
        end += 1
        if f(arg[start:end]) == GOOD:
            orig_end = end
    return arg[start:orig_end]

def check_grep_for(in_str, search_for):
    #print("echo %s | grep -q %s" % (repr(in_str), repr(search_for)))
    p = subprocess.Popen(["timeout", "0.5s", "grep", search_for], universal_newlines=False, stderr=subprocess.PIPE, stdout=subprocess.PIPE, stdin=subprocess.PIPE)
    #print(search_for)
    (stdout, stderr) = p.communicate(input=in_str)
    p.stdin.close()
    p.wait()
    if stderr != '' or p.returncode == 124: # timeout
        return INVALID
    return (GOOD if p.returncode == 0 else BAD)

if __name__ == '__main__':
    if len(sys.argv) != 3:
        sys.stderr.write("USAGE: %s SEARCH_IN SEARCH_FOR\n" % sys.argv[0])
        sys.exit(1)
    def check_grep(search_for):
        return check_grep_for(sys.argv[1], search_for)
    search_for = binary_search_on_string(check_grep, sys.argv[2])
    #p = subprocess.Popen(["grep", "--color=auto", search_for], universal_newlines=False, stdin=subprocess.PIPE)
    #p.communicate(input=sys.argv[1])
    #p.stdin.close()
    #p.wait()
    text = sys.argv[1]
    p = subprocess.Popen(["grep", "-o", search_for], universal_newlines=False, stderr=subprocess.PIPE, stdout=subprocess.PIPE, stdin=subprocess.PIPE)
    (stdout, stderr) = p.communicate(input=text)
    p.stdin.close()
    p.wait()
    found = stdout
    start = text.index(found)
    end = start + len(found)
    pre, mid, post = text[:start], text[start:end], text[end:]
    print(pre + format_text(mid, GREEN) + post)
    if len(search_for) < len(sys.argv[2]):
        print("Mismatch: bad next characters: %s" % (repr(sys.argv[2][len(search_for):][:10])))
    #sys.exit(p.errorcode)
