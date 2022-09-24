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
function `X : Ω → ℝ` and the hypothesis `measurable X`. From this point onwards 
I will use functions and random variables interchangably.

*Remark* Since a random variable is simply a function, I will denote random 
variables with the same notations as I use for functions, i.e. `f, g, h...`.
This notation is (mostly) consistent with what is used in mathlib and so I would 
prefer if you use it as well.

Mathematically, this is as simple as it gets however, as usual, its more 
complicated in practice. 

In probability theory, you commonly have hypothesis such as: "let `X` be a 
random variable with finite `p`-th moment". Mathematically, this is saying 
`𝔼[|X|^p] = ∫ ω, |X ω|^p dℙ < ∞`. In measure theory, this notion is known 
as `ℒp` (see section 6.2 of https://www.xuemei.org/Measure-Integration.pdf). 

`ℒp` functions form a Banch space with the norm `∥⬝∥ₚ` where we define 
`∥f∥ₚ = (∫ x, |f x|^p ∂μ)^(1 / p)`. In the case that `p = 2`, the space is 
actually a Hilbert space with the inner product `⟨f, g⟩ := ∫ x, (f x) (g x) ∂μ`.
We say a sequence of functions converges in `Lp` if it converges with respect 
to the above norm.

I've told a small lie in the above explaination. Actually, by noting that a 
function which is a.e. zero will have norm 0 contradicting the definition of a 
norm. So, to actually get the Banach space we need to quotient by the equivalence 
relation `~` where `f ~ g` if and only if `f =ᵐ[μ] g`. This quotient space is 
is known as `Lp`. However, by axiom of choice, we can always chose a 
representation for each class so we can imagine them as functions and commonly 
to interchange the two notions.

In Lean however, we will stick to the function intepretation and only falling 
back to the quotient when absolutely necessary. Nonetheless, due to the above 
construction, when mathematically defining properties for the `Lp` space 
(the quotient `ℒp / ~`), we should make definitions which transfers over a.e. 
equality. Namely, if we want to define a predicate `P : ℒp → Prop`, we should 
make sure the following diagram holds:

```
ℒp -{P}-> Prop 
 |       /
{q}    / 
 |   /
Lp
```
where `q` is the quotient map.

**Here's the conclusion**: As `measurable` does not satisfy the above diagram, 
it is not a good requirment to assume due to the reasons outlined above. 
Instead, we shall work with `ae_measurable` functions in whenever possible.

I will now interchangably use `Lp` and `ℒp`

Lean vocabulary:
- A function `f` is Lp: `mem_ℒp f p μ`
- the Lp norm of `f`: `snorm f p μ`
-/

variables {f : Ω → ℝ}

-- See Markov inequality
example (hf : ae_measurable f μ) (ε : ℝ≥0∞) :
  ε * μ {x | ε ≤ ∥f x∥₊} ≤ snorm f 1 μ :=
begin
  sorry
end

-- If `(fₙ)` converges in L∞ then it converges almost everywhere. 
-- The L∞ norm of a function `f` is defined as the essential supremum of `|f|`, i.e.
-- `∥f∥∞ = inf {R : ℝ | μ {f ≤ R}ᶜ = 0}`, i.e. 
-- the least element for which bounds `f` a.e.
example (f : ℕ → Ω → ℝ) (f' : Ω → ℝ) 
  (hf : ∀ n, ae_measurable (f n) μ) (hf' : ae_measurable f' μ)
  (hf : tendsto (λ n, snorm (f n - f') ∞ μ) at_top (𝓝 0)) :
  ∀ᵐ ω ∂μ, tendsto (λ n, f n ω) at_top (𝓝 (f' ω)) :=
begin
  sorry
end

/-!
## Convergence in measure/probability

So far we have seen two types of convergence: convergence a.e. and convergence 
in Lp. There is one more type of convergence which we care about in probability 
theory (actually there is one more but we shall not touch on it) known as 
convergence in measure. (or convergence in probability though we will stick 
with the first nomenclature). 

The sequence of function `(fₙ)` is said to converge in measure to some function 
`g` if for all `ε > 0`, `lim_{n → ∞} μ {|fₙ - f| > ε} = 0`. In Lean, this notion 
is defined as `tendsto_in_measure` although there is an extra parameter of type 
`filter`. To recover the mathematical defintion simply take this parameter to be 
the `at_top` filter.

Convergence in measure is the notion of convergence described by the weak law of 
large numbers. 

Convergence in measure is strictly weaker than convergence a.e. and in Lp. This 
is formalized in Lean with `tendsto_in_measure_of_tendsto_ae` and 
`tendsto_in_measure_of_tendsto_snorm`. On the other and, convergence in measure 
partially implies convergence a.e. In particular, a sequence of function 
converges in measure implies it has a subsequence which conveges a.e. This is 
formalized as `tendsto_in_measure.exists_seq_tendsto_ae`.
-/

example (f : ℕ → Ω → ℝ) (f' : Ω → ℝ) 
  (hf : ∀ n, ae_measurable (f n) μ) (hf' : ae_measurable f' μ)
  (hft : tendsto (λ n, snorm (f n - f') 1 μ) at_top (𝓝 0)) : 
  ∃ ns : ℕ → ℕ, strict_mono ns ∧ 
  ∀ᵐ ω ∂μ, tendsto (λ n, f (ns n) ω) at_top (𝓝 (f' ω)) :=
begin
  sorry
end

-- In the above exercise, if `hf'` necessary? I suspect not. Try to prove the 
-- following lemma (I don't this this is in mathlib!)

-- *Hint*: try proving it on paper first
-- *Maths hint*: Fatou's lemma
example (f : ℕ → Ω → ℝ) (f' : Ω → ℝ) (hf : ∀ n, measurable (f n)) 
  (hft : tendsto (λ n, snorm (f n - f') 1 μ) at_top (𝓝 0)) : 
  ae_measurable f' μ :=
begin
  sorry
end

-- Now, give the above example a name and use it to prove the following
example (f : ℕ → Ω → ℝ) (f' : Ω → ℝ) (hf : ∀ n, ae_measurable (f n) μ) 
  (hft : tendsto (λ n, snorm (f n - f') 1 μ) at_top (𝓝 0)) : 
  ae_measurable f' μ :=
begin
  sorry
end

-- Bonus: try to generalize the above for convergence in Lp rather than just 
-- convergence in L1.

/-!
## Conditional expectation


-/

end measure_theory