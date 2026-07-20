# Sally Clark

The following examples are loosely related to the 
[Sally Clark](https://en.wikipedia.org/wiki/Sally_Clark) case.
Both describe a hypothetical scenario where two infants are
found dead (this is denoted in the code as `d`) and the
mother is suspected of being a murderess (this is denoted in the code as `m`).

- `example_constraints.py`
- `example_no_constraints.py`

In the first example a constraint is imposed on the problem and in the second example 
no constraints are imposed.

# Monty Hall

The following examples are related to the [Monty Hall problem](https://en.wikipedia.org/wiki/Monty_Hall_problem).
In the code we use the notation from 
[this lecture](ttps://bechtel.colorado.edu/~balajir/CVEN5454/lectures/monty.pdf).
The `sympy` symbols `A`, `B`, `C` are statemets about the placement
of the car: behind curtain 1 , 2 , 3 respectively. `O` symbolizes
the statement that Monty Hall opens curtain number 2.

- `example_mh.py`
  - simple setup
- `example_mh_optimize.py`
  - additional statements, irrlelevant to the problem are introduced
- `example_mh_optimize_.py`
  - alternative problem setup, note that for numerical purpouses `p.addP(O , C , 0.99999)`
    is used instead of `p.addP(O , C , 1.0)`

# Entropy Optimization

The final example tests entropy optimization using the `getOptimalSolution` method. 

- `example_optimize.py`

Note that the linear program produces solutions that are very close to the maximum entropy
configutation. To better test entropy maximization see the code in next section.

# Publication Code

The code from the publication TODO is available in

- `publication_code_1.py`
  - Monty Hall problem
- `publication_code_2.py`
  - entropy maximization

# Comparison with Monte Carlo simulation

The two examples:

- `compare_mc.py`
- `compare_mc_1.py`

contain a probabilistical description of two architecural structures.
The comments in these files contain more details.
The calculated probabilities are verified against a direct
Monte Carlo simulation.
