/-!

# Probability theory in Lean

## About me

Hi, I am Jason and I've just graduated from Imperial College this summer and 
I will be starting part III at Cambridge this fall. I've worked with Lean for 
the past 3 years learning lean from Kevin and the experts on the Lean Zulip 
chat. I mostly formalize probability theory nowadays with my most recent project 
being the formalization of martingales. I also formalized a some linear algebra 
(mostly stuff from the 2nd year linear algebra course at Imperial). 

## About the project

In this project we will work with probability theory in Lean. I have a few 
projects prepared but feel free to suggest something if theres something you 
want to work with. 

### Project outline

Heres the outline of what I intend to do:

- **Intro to measure theory**: Measure theory is fundamental to doing 
probability theory rigorously so I will quickly go over the maths (if you 
haven't seen it before) and also give a brief overview of the measure theory 
that is in mathlib

- **Working with measure-theoretic probability theory**: You probably have used 
notions such as random variable, expectation, conditional expectation in your 
first year probability course. But really, what *is* a random variable? I will 
quickly go through the maths here.

- **State of probability theory**: If you know a lot of probability theory 
already you might be disappointed/exicted that probability theory is relatively 
new for mathlib. I will go over what's there and what's not.

- **Projects**: Finally, we can start discussing the projects and get our hands 
dirty by doing some Lean.

### The projects

Originally I had four projects in mind though it turns our one of them: 
Doob's decomposition theorem was formalized by Rémy Degenne just two weeks ago. 
Furthermore, one of the other project I had in mind - Kolmogorov's 0-1 law is 
probably too easy (at least the martingale proof). As a result I 
will offer two pre-planned projects (feel free to suggest others).

**The weak law of large numbers** 
The weak law of large numbers (WLLN) is one of the famous limit theorems in 
probability theory along side the strong law of large numbers (SLLN) and the 
central limit theorem (CLT). Informally, the WLLN states that if I do a random 
measurement multiple times, the average of the measurements should converge 
(in some specific sense) to the true measurement.

The SLLN has been formalized in Lean by Sébastien Gouëzel while the CLT is not 
doable at the moment (we don't have a theory of characteristic functions but 
there are discussions on formalizing the Fourier transform which will get us 
quite far). The WLLN, in contrast to what the name suggests, is not a direct 
corrolary of the SLLN (though a more restrictive version of the WLLN is). 
Luckily, the WLLN is much easier than the other two limit theorems and have a 
chance of being formalized in a workshop. Even luckier, the WLLN is not yet 
formalized in mathlib so if we manage to formalize it, we can PR it to the 
library for others to use. 

**The second Borel-Cantelli lemma** 
The second Borel-Cantelli lemma is a fun result in probability theory which 
tells you, under certain conditions, the probability of a sequence of events 
happening infinitely often is certain. 

Here's a fun application of the second Borel-Cantelli lemma.
Suppose we have a long jump event at every year where we record the longest 
jumper of that year by `Xₙ`. Furthermore, suppose `Xₙ` is iid. following the law 
`μ` where `μ(Xₙ ≤ r) < 1` for all `r ≥ 0` (e.g. χ² distribution). Then what is 
the probability the record will be crushed infinitely many times? 

I know two proofs of this theorem, a classical proof and a martingale proof. 
The classical proof is what everyone is taught in a typical probability theory 
course involving bounding a finite product. I personally don't like the 
classical proof that much and I would prefer if we do the martingale proof. 
The martingale proof involves a more general theorem known as Lévy's generalized 
Borel-Cantelli. I formalized Lévy's generalized Borel-Cantelli quite recently so 
we can directly use it. As the name suggests, this theorem generalizes the 
Borel-cantelli lemmas though this implication is not trivial and will involve us 
fiddling around with independence.

-/