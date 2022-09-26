/-! 

# Probability overivew

In this short file, I will give a brief overview of what probability theory 
currently exists in mathlib. 

The quickest indicator of what exists in mathlib is simply going into the 
probability folder and look at the file names. Of course, this method doesn't 
really give you a indicator of what is actually there. Also, some results 
relevant to probability theory might not actually be in the probability folder, 
e.g. conditional expectation. I will now list the relevant files. 

`probability._`: 
- `cond_count`: classical probability formulated in measure theory. Useful for 
  probabilistic arguments in combinatorics.
- `conditional_expectation`: this is *not* where conditional expectaion is 
  defined but the idea is that it should contain "probabilistic" results about 
  the conditional expectation. There is only one result there at the moment.
- `conditional_probability`: conditioning by an event and Bayes' theorem. 
  This is *not* the conditional probability defined via. the conditional 
  expectation.
- `density`: defines the probability density function and the uniform 
  distribution. It also contains results such as the LOTUS theorem.
- `ident_distrib`: definition of identically distributed random variables.
- `indepencence`: definition of independence (in a lot of sense); has a lot of 
  useful lemmas especially should you want to prove independence via. 
  π-λ systems.
- `integration`: lemmas about independence of random variables
- `moments`: moment generating functions and cumulant generating functions and 
  basic lemmas about them.
- `notation`: defines probability notations (requires you to write
  `open_locale probability_theory` in the file to before you can use)
- `strong_law`: the strong law of large numbers (both the a.e. and Lᵖ versions)
- `variance`: defines variance. Also contain the Chebyshev inequality.

`probability.process._` (most of this is rather self explainitory):
- `adapted`: defines adaptedness for stochastic processes
- `filtration`: defines filtration for stochastic processes
- `hitting_time`: hitting times are a random time (a stopping time in the 
  discrete time setting) and this file contains some basic results about them.
- `stopping`: defines stopping time for stochastic processes

`probability.martingale._`:
- `basic`: defines (sub/super)martingales and prove basic properties about them.
- `borel_cantelli`: proves the one-sided (sub)martingale bound and Lévy's 
  generalized Borel-Cantelli lemma.
- `centering`: proves the Doob's decomposition.
- `convergence`: proves the a.e. and L¹-martingale convergence theorems.
- `optional_stopping`: optional stopping theorem and the maximal inequality.
- `upcrossing`: two variants of the Doob's upcrossing estimate used to prove 
  the martingale covnergence theorems.

`probability.probability_mass_function._`:
I don't know much about this folder. I think these are finite stuff, not very 
relevant to what we want to work with but a lot of "Giry monads" whatever those 
are.

`measure_theory.function.conditional_expectation._`:
- `basic`: the construction of the conditional expecation. A lot of useful 
  lemmas are there too though the idea is we will eventually move them out of 
  there.
- `indicator`: the full-out property of conditional expectation for indicator 
  functions.
- `real`: contains results about the conditional expectation of real-valued 
  random variables (in contrast to Banach-space valued random variables). 
  In particular, this shows that our construction is equivalent to the 
  construction of the conditional expectation via. the Radon-Nikodym derivative. 
  Also, it show the pull-out proerty for real-valued random variables.
  It also contains some cool bounds for real-valued random variables also, 
  though we hope to generalize a lot of them once we have the conditional 
  Jensen's inequality.

`measure_theory.function.uniform_integrable`: uniform integrability in both the 
analyst's and the probabilist's sense (the two definitions are *not* equivalent) 
and proves the Vitali's convergence theorem.

`measure_theory.function.convergence_in_measure`: convergence in measure. See 
the `prob_thy` file for more details.

I am also very familiar with the `measure_theory.decomposition` folder so you 
can ask me about it if you are interested in the formalization of the 
Radon-Nikodym theorem.

-/