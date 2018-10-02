# Indifferentiability analysis

## Installation

*1*. Install [Opam](https://opam.ocaml.org/).

 * In Ubuntu,

~~~~~
apt-get install -y ocaml ocaml-native-compilers opam m4 camlp4-extra
~~~~~

 * In OS X, use homebrew,

~~~~~
brew install opam
~~~~~

*2*. Install the right compiler and the right libraries.

~~~~~
opam pin add indiff CLONED_DIR -n
opam install indiff --deps-only
~~~~~

*3*. To compile the tool, run:

~~~~~
make
~~~~~

*4*. To test the tool, run:

~~~
./test.native examples/tests/CHOOSE_FILE
~~~

*5*. To reproduce our (checking universality) experiments run:

~~~
cd examples/check-universality/
python run_tests.py
~~~

*6*. To reproduce our (attacks search) experiments run:

~~~
cd examples/attack-search/
python3 run_tests.py
~~~