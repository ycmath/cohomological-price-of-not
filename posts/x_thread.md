# X (x.com) explanatory thread — 6 posts

**1/6** How many NOT gates does a Boolean function really need? Markov (1958):
circuits get away with ⌈log₂(d+1)⌉, where d = the "decrease" — the number of
times f falls back down along a rising chain of inputs. Morizumi (2009):
formulas pay full price — exactly d(f). New note: that price has a
*cohomological address*. 🧵

**2/6** Setting: the dual-rail 4-valued lattice. The negation σ and the
rail-swap P generate a Klein four-group V₄, and H¹(V₄;𝔽₂) = 𝔽₂² has exactly
three nonzero characters. Which one prices negation? Answer: χ_σ — and it is
the UNIQUE one. Two separating witnesses kill the alternatives: P flips the
resolved face but costs 0 NOTs; σP costs 1 NOT but leaves the face alone.

**3/6** Main theorem: d(f) = minimal length of a *nested* negation tower.
Start from monotone functions; each rung allows exactly one fresh ¬ inside a
monotone context: T_{k+1} = { g(x, ¬h(x)) : g monotone, h ∈ T_k }. Each rung
consumes exactly one χ_σ-twist. Degree stays 1 throughout — the tower index
is a LEVEL, not a cohomological degree.

**4/6** The upper bound comes from one uniform witness. Let ω(x) = maximal
decrease along chains ending at x. Then h := 1 where ω ≥ k, ¬f in the middle
zone, 0 where ω = 0 — and d(h) = k−1 exactly. Fun fact: the "obvious" witness
¬f∧[ω≥1] is WRONG already at k = 1 (side-chains jump ω). The top-zone cap is
the whole trick.

**5/6** Everything is machine-verified: 19 theorems in core Lean 4, no
mathlib, no native_decide, no sorry. Axiom print: [propext, Quot.sound] only —
and the finite character tables depend on NO axioms at all. The upper bound
is constructive (an explicit any-based monotone extension; no choice axiom).

**6/6** Note + Lean artifact + independent Python verifications (exhaustive
n≤4, sampled n=5):
https://github.com/ycmath/cohomological-price-of-not
Produced with an AI research pipeline directed by the author; the Lean 4
kernel is the final gate. Corrections welcome.
