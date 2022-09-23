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

-- Let `X` be another measurable space and let `f` and `g` be functions from `Ω` to `X`
variables {X : Type*} [measurable_space X] (f g : Ω → X)

/-
If you go to the definition of measurable you will find what you expect. 
However, of course, measure theory in Lean is a bit more complicated. As we 
shall see, in contrast to maths, there are 3 additional notions of measurability 
in mathlib. These are: 
- `ae_measurable`
- `strongly_measurable`
- `ae_strongly_measurable`
The reasons for their existence is technical but TLDR: `ae_foo f` is the predicate 
that `f` is almost everywhere equal to some function satisfying `foo` (see the 
a.e. filter section) while `strongly_measurable f` is saying `f` is the limit 
of a sequence of simple functions.

Along side `measurable`, we will also see them quite often though 
all you have to know is in most cases (range is metrizable and second-countable), 
`measurable` and `strongly_measurable` are equivalent.
-/

example : measurable (id : Ω → Ω) :=
begin
  sorry
end

example (g : X → X) (hg : measurable g) (hf : measurable f) :
  measurable (g ∘ f) :=
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

In measure theory we have a notion known as almost everywhere (a.e.). In 
probability this is known as almost surely however we will stick with 
almost everywhere in this project. Namely, a predicate `P` on `Ω` is said to 
be true almost everywhere if the set for which `P` holds is co-null, i.e. 
`μ {ω : Ω | P ω}ᶜ = 0`. 

As examples, we say:
- given functions `f, g`, `f` equals `g` a.e. if `μ {ω : Ω | f ω ≠ g ω} = 0`;
- `f` is less equal to `g` a.e. if `μ {ω : Ω | ¬ f ω ≤ g ω} = 0` etc.

Often, showing that a property holds a.e. is the best we can do in 
measure/probability theory. 

In Lean, the notion of a.e. is handled by the `measure.ae` filter. What does 
filters mean? The specific details is not important thought you can find out 
more about it here: 
https://xenaproject.wordpress.com/2021/02/18/formalising-mathematics-workshop-5-filters/
All you have to know right now is that the `measure.ae` filter is what we shall 
use to formulate the notion of almost everywhere and once you unfold all the 
definitions, you will find what I've described above.
-/

-- The following is a proposition that `f` and `g` are almost everywhere equal
-- it's **not** a proof that `f` and `g` are a.e. equal but simply a statement
example := ∀ᵐ ω ∂μ, f ω = g ω

-- Here's another example on how to state `f` is almost everywhere less equal 
-- than `g`
-- To be able to formulate this we need a notion of inequality on `X` so we 
-- will add the `has_le` instance on `X`, i.e. equip `X` with a inequality 
example [has_le X] := ∀ᵐ ω ∂μ, f ω ≤ g ω

-- Since the above two cases come up quite often, there are special notations 
-- for them. See if you can guess what they mean
example := f =ᵐ[μ] g 
example [has_le X] := f ≤ᵐ[μ] g

-- In general, if `P : Ω → Prop` is a predicate on `Ω`, we write `∀ᵐ ω ∂μ, P ω` 
-- for the statement that `P` holds a.e.
example (P : Ω → Prop) := ∀ᵐ ω ∂μ, P ω

-- Sanity check: the above notation actually means what we think
example (P : Ω → Prop) : (∀ᵐ ω ∂μ, P ω) ↔ μ {ω | P ω}ᶜ = 0 := 
begin
  refl,
end

-- Heres a more convoluted example. See if you can figure what it means
example (f : ℕ → Ω → ℝ) (s : set Ω) := 
  ∀ᵐ ω ∂μ.restrict s, ∃ l : ℝ, tendsto (λ n, f n ω) at_top (𝓝 l)

-- Now to do some exercises: you will need to dig into the source code to see 
-- what the definitions are and search for helpful lemmas
-- *Hint*: try out the `measurability` tactic. It should be able to solve simple 
-- goals of the form `measurable_set s` and `measurable f`
example (s : set Ω) (f g : Ω → ℝ)
  (hf : measurable f) (hg : measurable g) (hfg : ∀ ω ∈ s, f ω = g ω) : 
  f =ᵐ[μ.restrict s] g :=
begin
  sorry
end

example (f g h : Ω → ℝ) (h₁ : f ≤ᵐ[μ] g) (h₂ : f ≤ᵐ[μ] h) : 
  2 * f ≤ᵐ[μ] g + h :=
begin
  sorry
end

example (f g : Ω → ℝ) (h : f =ᵐ[μ] g) (hg : ∀ᵐ ω ∂μ, 2 * g ω + 1 ≤ 0) :
  ∀ᵐ ω ∂μ, f ω ≤ -1/2 :=
begin
  sorry
end

example (f g : ℕ → Ω → ℝ) (a b : ℝ) 
  (hf : ∀ᵐ ω ∂μ, tendsto (λ n, f n ω) at_top (𝓝 a))
  (hg : ∀ᵐ ω ∂μ, tendsto (λ n, g n ω) at_top (𝓝 b)) :
  ∀ᵐ ω ∂μ, tendsto (λ n, f n ω + g n ω) at_top (𝓝 (a + b)) :=
begin
  sorry
end

/- 
I hope that you found the above examples slightly annoying, especially the 
third example: why can't we just `rw h`?! Of course, while we often do do so on 
paper, rigourously, such a rewrite require some logic. Luckily, what we normally 
do on paper is most often ok and we would like to do so in Lean as well. While 
we can't directly rewrite almost everywhere equalities, we have the next best 
thing: the `filter_upwards` tactic. See the tactic documentation here: 
https://leanprover-community.github.io/mathlib_docs/tactics.html#filter_upwards

The `filter_upwards` tactic is much more powerful than simply rewritting a.e. 
equalities and is helpful in many situtations, e.g. the above second, third 
and fourth examples are all easily solvable with this tactic. Let us see how 
it works in action.
-/

-- Hover over each line and see how the goal changes
example (f₁ f₂ g₁ g₂ : Ω → ℝ) (h₁ : f₁ ≤ᵐ[μ] g₁) (h₂ : f₂ ≤ᵐ[μ] g₂) : 
  f₁ + f₂ ≤ᵐ[μ] g₁ + g₂ :=
begin
  filter_upwards [h₁, h₂],
  intros ω hω₁ hω₂,
  exact add_le_add hω₁ hω₂,
end

-- Heres an even shorter proof using additional parameters of `filter_upwards`
example (f₁ f₂ g₁ g₂ : Ω → ℝ) (h₁ : f₁ ≤ᵐ[μ] g₁) (h₂ : f₂ ≤ᵐ[μ] g₂) : 
  f₁ + f₂ ≤ᵐ[μ] g₁ + g₂ :=
begin
  filter_upwards[h₁, h₂] with ω hω₁ hω₂ using add_le_add hω₁ hω₂,
end

/-
Intuitively, what `filter_upwards` is doing is simply exploiting the fact that 
the intersection of two full measure sets (i.e. complements are null) is also 
a set of full measure. Thus, it suffices to work in their intersection instead. 

Now, try the above examples again using the `filter_upwards` tactic.
-/

end measure_theory