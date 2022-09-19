import probability.martingale.borel_cantelli 

open filter
open_locale nnreal ennreal measure_theory probability_theory big_operators topological_space

namespace measure_theory

/-!

# Intro to measure theory

Measure theory is the foundations of modern probability theory. Some say that 
measure theory is a necessary evil for probabilists, I disagree. Measure theory 
formalizes the fuzzy notations in everyday probability and clears the mists 
showing us whats actually there. In the beginning, measure theory might seems 
useless forcing us to bang our heads against the wall to prove some trivial 
theorems but as probability gets more complicated, measure theory becomes a 
useful tool to keep track of whats actually correct. Furthermore, measure theory 
is beautiful to study own with some incredible theorems. 

In this section, I will introduce the following definitions in plain English as 
well as in Lean. 

-/

/-! 
## σ-algebra and measures
-/

-- Suppose we have a space `Ω` equipped with a σ-algebra
-- We call `Ω` a measurable space
variables {Ω : Type*} [measurable_space Ω]

/-
A σ-algebra (or `measurable_space` in Lean) is defined as the following:
```
structure measurable_space (Ω : Type*) :=
(measurable_set' : set Ω → Prop)
(measurable_set_empty : measurable_set' ∅)
(measurable_set_compl : ∀ s, measurable_set' s → measurable_set' sᶜ)
(measurable_set_Union : ∀ f : ℕ → set Ω, (∀ i, measurable_set' (f i)) → 
  measurable_set' (⋃ i, f i))
```
Namely, it is a predicate of sets of elements of `Ω` which is satisfied by the 
empty set, closed under complements and countable unions. We say a set is 
measurable if it satisfy this predicate.

Try proving the following lemmas:
(Hint: see what is avaliable on the documentation website: 
https://leanprover-community.github.io/mathlib_docs/measure_theory/measurable_space_def.html)
-/

example (S₁ S₂ S₃ : set Ω) 
  (hS₁ : measurable_set S₁) (hS₂ : measurable_set S₂) (hS₃ : measurable_set S₃) :
  measurable_set (S₁ ∪ (S₂ \ S₃)) := 
begin
  sorry
end

example (s : ℕ → set Ω) (S : set Ω) 
  (hs : ∀ n, measurable_set (s n)) (hS : measurable_set S) : 
  measurable_set (S ∩ ⋂ n, s n) :=
begin
  sorry
end

-- Now lets add a measure `μ` on `Ω`
variables {μ : measure Ω}

/-
You should now learn how to go to definition on VS-code: right click the word
`measure` on line 67 and click `Go to Definition`. It should then open the 
file `measure_space_def` and your cursor should now hover over the defintion 
of measure in mathlib. 

If you know your definition of the measure or have now looked it up on Wikipedia 
you might realize the definiton is slightly different. There's this 
`outer_measure` thing which is nowhere found in the normal definition. The 
technical reason for this is we do not want to define partial functions in Lean, 
namely we want to assign non-measurable sets a value as well. So, to do this, we 
define something called an outer measure which is defined on all sets and then 
restrict it to down to a measure so that countable additivity remains to hold. 
This is known as the Caratheodory extension theorem though you don't really need 
the details to start working with measures. Simply look through the file where 
measure is defined (or the documentation website) and you will find the lemmas 
required which shows that Lean's definition behaves identically to the maths 
definition.

Try proving the following:
-/

example (S T : set Ω) (hS : μ S ≠ ∞) (hT : measurable_set T) : 
  μ (S ∪ T) = μ S + μ T - μ (S ∩ T) :=
begin
  sorry
end

/-
*Remark*: while proving the above, you might have noticed I've added the 
condition `hS` (think about what is a + ∞ - ∞). In particular, subtraction in 
extended non-negative reals (`ℝ≥0∞`) might not be what you expect, 
e.g. 1 - 2 = 0 in `ℝ≥0∞`. For this reason, the above lemma is better phrased as 
`μ (S ∪ T) + μ (S ∩ T) = μ S + μ T` for which we can omit the condition `hS`.
-/

/-! 
## Measurable functions

So far we've worked in the space `Ω` though with all mathematical objects, we 
want to map between them. In measure theory, the correct notion of maps is 
measurable functions. If you have seen continuity in topology, they are quite 
similar, namely, a function `f` between two measurable spaces is said to be 
measurable if the preimages of all measurable sets along `f` is measurable. 
-/

-- Let `X` be another measurable space and let `f` be a function from `Ω` to `X`
variables {X : Type*} [measurable_space X] (f : Ω → X)
-- Furthermore, let `f` be measurable
variables (hf : measurable f)

-- Include the assumption that `f` is measurable in all following examples
include hf

/-
If you go to the definition of measurable you will find what you expect. 
However, of course, measure theory in Lean is a bit more complicated. As we 
shall see, in contrast to maths, there are 3 additional notions of measurability 
in mathlib. These are: 
- `ae_measurable`
- `strongly_measurable`
- `ae_strongly_measurable`
The reasons for their existence is technical so you can ask me if you are 
interested. Along side `measurable`, we will also see them quite often though 
all you have to know is (a) in most cases, `measurable` and 
`strongly_measurable` are equivalent and (b) `ae(_strongly)_measurable` is a 
slightly weaker version than their non-ae counter part and most theorems can be 
relaxed to only require the ae version.
-/

example : measurable (id : Ω → Ω) :=
begin
  sorry
end

example (g : X → X) (hg : measurable g) : measurable (g ∘ f) :=
begin
  sorry
end

/-!
## Integration

One of the primary motivations of measure theory is to introduce a more 
satisfactory theory of integration. If you recall the definition of the 
Darboux-Riemann integral, we cannot integrate the indicator function of 
`ℚ ∩ [0, 1]` despite, intuitively, the set of rationals in the unit interval 
is much "smaller" (rationals is countable while the irrationals are not for 
one). In contrast, measure theory allows us to construct the Lebesgue integral 
which can deal with integrals such as this one. 

Lean uses a even more general notion of integration known as Bochner integration 
which allows us to integrate Banach-space valued functions. Its construction 
is similar to the Lebesgue integral. 

Read page 5-6 of https://arxiv.org/pdf/2102.07636.pdf
should you want to know the details.
-/

-- Suppose now `X` is in addition a Banach space 
variables [normed_add_comm_group X] [normed_space ℝ X] [complete_space X]

-- If `f : Ω → X` is a function, then the integral of `f` is written as 
-- `∫ x, f x ∂μ`. If you want to integrate over the set `s : set Ω` then write 
-- `∫ x in s, f x ∂μ`.

-- Proving anything new is now slightly non-trivial so try to find the following 
-- theorems in mathlib

example {f g : Ω → X} (hf : integrable f μ) (hg : integrable g μ) : 
  ∫ x, f x + g x ∂μ = ∫ x, f x ∂μ + ∫ x, g x ∂μ :=
begin
  sorry
end

example (a : X) (s : set Ω) : ∫ x in s, a ∂μ = (μ s).to_real • a :=
begin
  sorry
end

/-
*Remark* It's a common myth that Lebesgue integration is strictly better than 
the Darboux-Riemann integral. This is true for integration on bounded intervals 
though it is not true when considering improper integrals. A common example 
for this is, while `∫ x in [0, ∞), sin x / x dx` is Darboux-Riemann integrable 
(in fact it equals `π / 2`) it is not Lebesgue integrable as 
`∫ x in [0, ∞), |sin x / x| dx = ∞`.
-/

/-! 
## ae filter

Now we have come to a very important section of working with measure theory 
in Lean.

-/

end measure_theory