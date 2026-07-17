# ProbabilityIter

Probability solver for discreete logical statements.

## Installation

It is recommended to use the library in a separate python environment. 
An environment named *temp* may be created using:
```
$ python -m venv temp 
``` 
This created the directory `temp` with the relavent files.
Next the environment needs to be activated:
```
$ . <path to temp direcory>/bin/activate
```
and an activated environment might be indicated
by a change to the prompt. 

To install dependencies, inside the activated environment, run:
```
(temp) pip install numpy torch scipy sympy
```

To check if the installation of dependencies was successfull, inside the *tests* directories
try:
```
(temp) $ python test.py -v
```
This will run unit tests, success of each test schould be indicated by a green `ok`,
and the success of all tests by a green `OK`.

Once dependencies are installed the library may imported inside python using 
`import piter`.
Finally, to deactivate the
environment run:
```
(temp) $ deactivate
```
