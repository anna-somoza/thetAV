## -*- encoding: utf-8 -*-
import os
import sys
from setuptools import setup
from codecs import open # To open the README file with proper encoding
from setuptools.command.test import test as TestCommand # for tests

# Get information from separate files (README, VERSION)
def readfile(filename):
    with open(filename,  encoding='utf-8') as f:
        return f.read()

# For the tests
class SageTest(TestCommand):
    def run_tests(self):
        errno = os.system("sage -t --force-lib thetAV")
        if errno != 0:
            sys.exit(1)

setup(
    name = "thetAV",
    version = "0.1.1", #readfile("VERSION").strip(), # the VERSION file is shared with the documentation
    description = 'A SageMath package on abelian varieties with theta structure',
    long_description = readfile("README.md"),
    long_description_content_type="text/markdown",
    url='https://thetav.readthedocs.io/',
    author='Anna Somoza',
    author_email='anna.somoza.henares@gmail.com', # choose a main contact email
    license='GPLv3', # This should be consistent with the LICENCE file
    classifiers=[
      # How mature is this project? Common values are
      #   3 - Alpha
      #   4 - Beta
      #   5 - Production/Stable
      'Development Status :: 4 - Beta',
      'Intended Audience :: Science/Research',
      'Topic :: Scientific/Engineering :: Mathematics',
      'License :: OSI Approved :: GNU General Public License v3 (GPLv3)',
      'Programming Language :: Python :: 3.10',
    ], # classifiers list: https://pypi.python.org/pypi?%3Aaction=list_classifiers
    keywords = "SageMath package",
    packages = ['thetAV'],
    install_requires=['sage',],
    cmdclass = {'test': SageTest},
)
