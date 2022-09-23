import probability.martingale.borel_cantelli 

open filter
open_locale nnreal ennreal measure_theory probability_theory big_operators topological_space

namespace measure_theory

/-!

# Probability theory 

Now that we know the basics of measure theory in Lean, let us talk about 
measure theoretic probability theory. While probability theory is a large area 
in mathematics, mathlib itself does not contain much of it at the moment. In 
this section I will provide a basic overview of what is there. 

-/

/-!
## The set-up

If you have read any literature on probability, you've probably seen the phrase: 
"let `(Ω, ℱ, ℙ)` be a probability space". A probability space is simply a 
measure space with the additional assumption that `ℙ(Ω) = 1`. In Lean, one can 
declare this by simply declaring a measure space, i.e. 
-/
variables {Ω : Type*} {m0 : measurable_space Ω} {μ : measure Ω}

/-
and require that `μ` is a probability measure with the instance 
```
  [is_probability_measure μ]
```
While, this is the setting most literature in probability will go with, this is 
in fact unnecessarily restrictive. Indeed, most theorems in probability theory 
remains to hold provided that `μ` is a finite measure (although sometimes that 
is not even necessary). As a result, we will add the required assumptions on the 
measure when needed. 
-/

/-!
## Random variables & Lp functions

Random variables are measurable functions and in most cases, are real valued.
Namely, to declare a (real valued)-random variable in Lean, simply declare a 
function `X : Ω → ℝ` and the hypothesis `measurable X`.

*Remark* Since a random variable is simply a function, I will denote random 
variables with the same notations as I use for functions, i.e. `f, g, h...`.
This notation is (mostly) consistent with what is used in mathlib and so I would 
prefer if you use it as well.

Mathematically, this is as simple as it gets however, as usual, its more 
complicated in practice. 

In probability theory, you commonly have hypothesis such as: "let `X` be a 
random variable with finite `n`-th moment". Mathematically, this is saying 
`𝔼[|X|^n] = ∫ ω, |X ω|^n dℙ < ∞`. 

-/


end measure_theory