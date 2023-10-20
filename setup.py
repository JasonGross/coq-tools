from setuptools import setup, find_packages

setup(
    name='coq-tools',
    version='0.0.1',
    packages=find_packages(),
    install_requires=[
        # Add any dependencies here
    ],
    scripts=[
        # Add non-python executable scripts to install here
    ],
    package_data={
        'coq_tools': [
            'coqtop-as-coqc.sh',
            'coqtop.bat',
        ],
    },
    entry_points={
        'console_scripts': [
            'coq-bug-minimizer=coq_tools.find_bug:main',
            'coq-require-minimizer=coq_tools.minimize_requires:main',
            'coq-import-inliner=coq_tools.inline_imports:main',
        ],
    }
)
