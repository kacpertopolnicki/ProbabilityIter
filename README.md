# ProbabilityIter

Small library of python code for calculations related to probability.

## Probability as logic

The standard axioms of probability were first 
written down by [Andrey Kolmogorov](https://en.wikipedia.org/wiki/Probability_axioms).
For the purpouses of this software library we will be using 
a slightly different formulation based on logic that is attributed to 
[Richard Threlkeld Cox](https://en.wikipedia.org/wiki/Cox%27s_theorem)
and popularized by [Edwin Thompson Jaynes](https://en.wikipedia.org/wiki/Edwin_Thompson_Jaynes).
The calculations presented below can be carried out in any of the two formulations
and produce equivalent results, however the language of logic lends itself 
more to the problems of inference that we are trying to takle.

## The problem

We will assume that the user formulates his assumptions or knowlege as
a certain number the following types of statements:

$$
P(A | B X) = \alpha
$$

where $P(A | B X)$ is the conditional probability of $A$ given $B$ and $X$. 
The three variables $A$, $B$, and $X$ are all logical expressions. $X$ playes
the special role of "bakground knowledge" and is not specified by the user explicitly.
Following [E.T. Jaynes](https://www.cambridge.org/gb/universitypress/subjects/physics/theoretical-physics-and-mathematical-physics/probability-theory-logic-science)
we adopt the following convention:

$$
A + B
$$

means as $A$ **or** $B$, while:

$$
A B
$$

stands for $A$ **and** $B$. Finally $\alpha$ is a real number between $0$ and $1$ - the 
value of $P(A | B X)$.

## Examples

Example usage is in `example_constraints.py` and `example_no_constraints.py`. Both of these 
examples were loosely inspired by the [Sally Clark case](https://en.wikipedia.org/wiki/Sally_Clark).
Additional examples are in tests contained in `piter.py`.

# TODO

There is a lot of room for improvement. 

- Generating the basis using constraints is an expensive operation.
- Currently all the solution for probabilities may be obtained only
  after all relavent information is supplied. Need to add generation
  of entropy maximizing solutions.
