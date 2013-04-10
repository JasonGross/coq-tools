from __future__ import with_statement
import os

file_contents = {}
file_imports = {}

def get_file(file_name):
    if file_name[-2:] != '.v': file_name += '.v'
    if file_name not in file_contents.keys():
        print(file_name)
        try:
            with open(file_name, 'r', encoding='UTF-8') as f:
                file_contents[file_name] = f.read()
        except TypeError:
            with open(file_name, 'r') as f:
                file_contents[file_name] = f.read()
    return file_contents[file_name]

def get_imports(file_name):
    if file_name[-2:] != '.v': file_name += '.v'
    if file_name not in file_imports.keys():
        lines = get_file(file_name).split('\n')
        import_lines = [i.strip('. ') for i in lines if
                        i.strip()[:len('Require ')] == 'Require ' or
                        i.strip()[:len('Import ')] == 'Import ']
        imports = set((' ' + ' '.join(import_lines)).replace(' Require ', ' ').replace(' Import ', ' ').replace(' Export ', ' ').strip().split(' '))
        file_imports[file_name] = tuple(sorted(imports))
    return file_imports[file_name]

def merge_imports(*imports):
    rtn = []
    for import_list in imports:
        for i in import_list:
            if i not in rtn:
                rtn.append(i)
    return rtn

def recursively_get_imports(file_name):
    if file_name[-2:] != '.v': file_name += '.v'
    if os.path.exists(file_name):
        imports = get_imports(file_name)
        imports_list = [recursively_get_imports(i) for i in imports]
        return merge_imports(*imports_list) + [file_name[:-2]]
    return [file_name[:-2]]

def contents_without_imports(file_name):
    if file_name[-2:] != '.v': file_name += '.v'
    contents = get_file(file_name)
    lines = [i for i in contents.split('\n') if
             i.strip()[:len('Require ')] != 'Require ' and
             i.strip()[:len('Import ')] != 'Import ']
    return '\n'.join(lines)

def include_imports(file_name):
    if file_name[-2:] != '.v': file_name += '.v'
    all_imports = recursively_get_imports(file_name)
    remaining_imports = []
    rtn = ''
    for import_name in all_imports:
        if os.path.exists(import_name + '.v'):
            rtn += contents_without_imports(import_name)
        else:
            remaining_imports.append(import_name)
    rtn = 'Require Import %s.\n%s' % (' '.join(remaining_imports), rtn)
    return rtn
