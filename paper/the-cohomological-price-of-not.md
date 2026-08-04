# The Cohomological Price of NOT

**Won Chul Yang** — independent researcher · wcy0969@gmail.com · 2026

**Abstract.** The minimal number of negations needed to compute a Boolean
function is governed by Markov's decrease invariant d(f): circuits need
⌈log₂(d(f)+1)⌉ negations (Markov 1958), and formulas need exactly d(f)
(Morizumi 2009). We show that the decrease invariant carries a *cohomological
address*. On the dual-rail four-valued lattice, the negation σ and the
rail-swap P generate a Klein four-group V₄ whose character group
Hom(V₄,𝔽₂) ≅ 𝔽₂² has exactly three nonzero characters, and χ_σ is the
*unique* one that prices negation — the two alternatives fail in opposite
directions, witnessed by P (face-flip 1, cost 0) and σP (face-flip 0,
cost 1). The main theorem reads the full invariant as an iterated extension:
d(f) equals the minimal length of a nested χ_σ-tower, each rung adjoining
exactly one negation inside a monotone context. The upper bound uses a single
uniform three-zone witness; the lower bound is an alternation argument valid
over any finite poset. All statements are machine-verified in core Lean 4
with kernel axioms `propext` and `Quot.sound` only.

## 1. Introduction

Markov [1] determined the inversion complexity of Boolean circuits:
I(f) = ⌈log₂(d(f)+1)⌉, where the decrease d(f) counts the maximal number of
1→0 descents of f along an increasing chain of inputs. Morizumi [2] settled
the formula model: I_for(f) = d(f) exactly. For multi-valued logic,
Kochergin–Mikhailovich [7] extended the *circuit* law (still logarithmic);
no formula-exact multi-valued law appears in the literature.

This note contributes three things.

**(i) A four-valued frame.** On the dual-rail lattice D4 the exact
formula-model law persists (the companion preprint [10] proves
ν(f) = d(f) in that setting; we do not reprove it here).

**(ii) A cohomological reading.** The negation σ and the monotone rail-swap
P generate V₄, and among the three nonzero characters of H¹(V₄;𝔽₂) exactly
one — χ_σ — prices negation (§3). The seemingly natural candidate, the
face-flip character χ_σ+χ_P, fails in *both* directions.

**(iii) A nested normal form.** d(f) = minimal length of a nested tower
T₀ ⊆ T₁ ⊆ ⋯ in which each rung adjoins exactly one negation inside a
monotone context (§6). Morizumi's upper-bound construction is the *parallel*
decomposition f₁ ∨ (f₂ ∧ ¬f_t); the nested single-peel form proved here is
strictly more structured, and appears to be new even in the Boolean case.
The upper bound is produced by one uniform three-zone witness (§5), whose
correctness is a short budget argument; a cautionary example shows the
obvious witness is wrong already at d(f) = 1.

Everything below is machine-verified in core Lean 4 (§7).

## 2. Preliminaries

Let R = {0,1} with 0 < 1, and order Rⁿ componentwise. A *chain* is an
increasing sequence x⁰ < x¹ < ⋯ < xᵐ in Rⁿ. For f : Rⁿ → R and a chain X,
the *decrease* d_X(f) is the number of indices i with f(xⁱ) = 1 and
f(xⁱ⁺¹) = 0 taken along consecutive elements; d(f) = max_X d_X(f) over
maximal chains. For a binary word w, write rises(w) and drops(w) for the
numbers of 01- and 10-adjacencies. The *decrease potential* is

> ω(x) := max { drops of f along an increasing chain ending at x },

so ω is nondecreasing along chains, ω ≤ d(f) everywhere, and every descent
step strictly increases ω.

The dual-rail lattice is D4 = {0,1}², ordered componentwise (four values:
bottom (0,0), the two *resolved* values (1,0) and (0,1) forming the face R,
and top (1,1)). Define the involutions σ(a,b) = (1−a, 1−b) (negation;
order-reversing) and P(a,b) = (b,a) (rail-swap; monotone). They commute and
generate V₄ = {id, σ, P, σP}.

## 3. The pricing character

H¹(V₄;𝔽₂) = Hom(V₄,𝔽₂) ≅ 𝔽₂², with the three nonzero characters determined
by their kernels: χ_σ (kernel {id, P}), χ_P (kernel {id, σ}), and the
face-flip character χ_σ + χ_P (kernel {id, σP}) — the character that is 1
exactly on the elements moving the resolved face R.

For γ ∈ V₄ let ν(γ) ∈ {0,1} be its negation cost: 0 if γ is monotone
(hence expressible without negation), 1 otherwise.

**Proposition 3.1 (gate typing).** As vectors over (id, σ, P, σP):

| γ | monotone | ν(γ) | χ_σ(γ) | (χ_σ+χ_P)(γ) |
|---|---|---|---|---|
| id | yes | 0 | 0 | 0 |
| σ | no | 1 | 1 | 1 |
| P | yes | 0 | 0 | **1** |
| σP | no | 1 | 1 | **0** |

Hence ν = χ_σ pointwise on V₄, and χ_σ is the **unique** nonzero character
with this property: χ_P fails at σ, and the face-flip character fails in
both directions — at P (flip without cost) and at σP (cost without flip).

*Proof.* Inspection of the four actions on D4: σ swaps both the endpoints
(0,0) ↔ (1,1) and the face (1,0) ↔ (0,1) and reverses the order; P fixes
the endpoints, swaps the face, and is monotone; σP swaps the endpoints,
fixes the face, and is not monotone (it exchanges bottom and top).
Machine-checked as `gate_table` and `chiSigma_eq_not_kMono` (axiom-free
kernel `decide`). ∎

The two witnesses deserve names: P is the *first separating witness*
(face-flip 1, cost 0) and σP the *second* (cost 1, face-flip 0). Together
they show that "pricing negation" and "moving the resolved face" are
different characters — they differ exactly by χ_P.

## 4. Subadditivity and the lower bound

**Lemma 4.1 (alternation).** For every binary word w,
rises(w) ≤ drops(w) + 1; if w begins with 1, then rises(w) ≤ drops(w).

*Proof.* Induction on the word, tracking the first letter: each maximal
1-block contributes at most one rise on its left and one drop on its right,
and only the initial 1-block can lack a preceding rise. (Lean:
`rises_le_drops_succ`.) ∎

**Lemma 4.2 (drop transfer).** Let g be monotone in both arguments, h
arbitrary, and f(x) = g(x, ¬h(x)). If x < x′ is a chain step with f(x) = 1
and f(x′) = 0, then h(x) = 0 and h(x′) = 1 (an ascent of h).

*Proof.* If ¬h(x) ≤ ¬h(x′) then (x, ¬h(x)) ≤ (x′, ¬h(x′)) and monotonicity
of g forces f(x) ≤ f(x′), contradiction. So ¬h descends, i.e. h ascends. ∎

**Theorem 4.3 (subadditivity).** For monotone g and arbitrary h,
d(g(x, ¬h(x))) ≤ d(h) + 1. In fact, along any single chain,
drops(f-word) ≤ rises(h-word) ≤ drops(h-word) + 1; the argument uses only
adjacent steps, so it is valid over any relation, in particular any finite
poset. (Lean: `subadd_chain`, `subadd_decOn`.)

*Proof.* Each descent of f is matched by an ascent of h at the same step
(Lemma 4.2); ascents are bounded by descents plus one (Lemma 4.1); descents
of h along any chain are at most d(h). ∎

**Corollary 4.4 (tower lower bound).** Define T₀ = the monotone functions
and T_{k+1} = { g(x, ¬h(x)) : g monotone, h ∈ T_k }. Then f ∈ T_k implies
d(f) ≤ k. (Lean: `F1_lower`, via the end-value-refined form
rises(w) ≤ drops(w) + [w ends in 1].)

**Corollary 4.5 (no skipping).** If f = g(x, ¬h) with g monotone, then
d(h) ≥ d(f) − 1.

## 5. The three-zone witness

Fix f with d(f) = k ≥ 1. Call a pair x < x′ *violated* if f(x) = 1 and
f(x′) = 0; write V⁻ and V⁺ for the lower and upper points of violated pairs.

**Lemma 5.1 (potential jump).** Across a violated pair, ω(x) + 1 ≤ ω(x′).
In particular ω(x) ≤ k − 1 and ω(x′) ≥ 1. (Lean: `omega_viol`.)

*Proof.* Take a cover-path from x up to x′. Either f descends somewhere
along it — then from that step on, ω exceeds the ω-witness through x by at
least one — or f already equals 1 at the last point before some descent to
value 0; in all cases, composing an ω-realizing chain into x with the path
to x′ adds at least one descent. Formally: induct along the path; at a
descent step apply strictness of ω, otherwise monotonicity, recursing on the
first point where f = 1 still holds. ∎

**Theorem 5.2 (three-zone witness).** Define

> h := 1 on {ω ≥ k},  ¬f on {1 ≤ ω ≤ k−1},  0 on {ω = 0}.

Then (a) h covers every violated pair: h = 0 on V⁻ and h = 1 on V⁺; and
(b) d(h) = k − 1 exactly. (Lean: `hgen_covering`, `hgen_drops_le`,
`omega_hgen_le`, over an abstract descent potential; `cube_descPotential`
discharges the potential axioms for the concrete ω.)

*Proof.* (a) For x ∈ V⁻: ω(x) ≤ k−1 by Lemma 5.1, so h(x) is either 0
(zone 0) or ¬f(x) = 0 (middle zone). For x′ ∈ V⁺: ω(x′) ≥ 1, so h(x′) is
either ¬f(x′) = 1 (middle) or 1 (top zone).

(b) Along any chain, ω is nondecreasing, so the chain traverses the zones
in the order {ω=0} → {1 ≤ ω ≤ k−1} → {ω ≥ k}, each a contiguous (possibly
empty) stretch. h is constant 0, then ¬f, then constant 1. A descent of h
cannot start at the 0-zone (h = 0), cannot occur inside the top zone
(h = 1), and cannot occur at either zone boundary (entering the middle from
0 cannot descend; leaving the middle to the top ends at 1). So every
descent of h lies inside the middle stretch and is an *ascent* of f there.
Inside the middle stretch, each descent of f strictly increases ω, and ω
stays within [1, k−1]; hence the stretch contains at most k−2 descents of
f, and by alternation at most k−1 ascents. So d(h) ≤ k−1; equality follows
from Corollary 4.5 applied to any monotone-context factorization produced
in §6. ∎

**Remark 5.3 (the naive witness fails).** The tempting witness
h₁ := ¬f ∧ [ω ≥ 1] is wrong already at k = 1. On three variables take
f(010) = f(111) = 1 and f = 0 elsewhere: then d(f) = 1, but along the chain
000 < 100 < 110 < 111 the potential jumps to 1 at 110 through the *side*
chain 000 < 010 < 110, so h₁ takes values 0,0,1,0 — one descent, though
k − 1 = 0. The top-zone cap (h ≡ 1 on {ω ≥ k}) is exactly what repairs
this. The example generalizes: side-chains can raise ω without any descent
on the chain being traversed.

## 6. The nested tower theorem

**Lemma 6.1 (monotone extension).** Let h cover every violated pair of f.
Then there is a monotone g with f(x) = g(x, ¬h(x)): define

> g(y, v) := 1 iff there is x ≤ y with (h(x) = 1 or v = 1) and f(x) = 1,

a monotone function of (y, v); the covering hypothesis rules out the only
conflict (a witness x ≤ y with f(x) = 1 forcing g = 1 while f(y) = 0 —
such a pair is violated, so h(x) = 0 and h(y) = 1, and the disjunct
(h(x) ∨ ¬h(y)) fails). No choice principle is needed — the extension is an
explicit finite disjunction. (Lean: `gExt`, `gExt_mono`, `gExt_agrees`.) ∎

**Theorem 6.2 (nested tower).** For every nonconstant f : Rⁿ → R,

> f ∈ T_k ⟺ d(f) ≤ k.

Hence d(f) is the minimal length of a nested χ_σ-tower over the monotone
clone, each rung consuming exactly one χ_σ-twist. (Lean: `tower_of_decPts`
for the upper bound — constructive, producing the witness of §5 at each
rung — and `F1_lower` for the lower bound.)

*Proof.* (⟸, upper bound) Induction on k. If d(f) = 0, f is monotone.
Otherwise let h be the three-zone witness for K := d(f): by Theorem 5.2(b)
d(h) = K − 1, by induction h ∈ T_{K−1}, and by Lemma 6.1 with Theorem 5.2(a)
f = g(x, ¬h) for a monotone g, so f ∈ T_K ⊆ T_k. (⟹ is Corollary 4.4.) ∎

**Remark 6.3 (models).** In the formula model this recovers I_for(f) = d(f)
[2] with a *nested* optimal form: Morizumi's construction is the parallel
decomposition f₁ ∨ (f₂ ∧ ¬f_t), in which the recursive part and the fresh
negation sit in separate branches; Theorem 6.2 shows a single nested branch
suffices. In the circuit model the tower reading diverges from I(f) once
d ≥ 3, by Markov's logarithmic law — the tower is a formula-model object.

**Remark 6.4 (level, not degree).** The tower index is a filtration level
at fixed cohomological degree one. No identification with any
higher-degree or higher-level operator theory is claimed.

## 7. Mechanization

All statements are verified in core Lean 4 (no mathlib), 19 theorems; the
axiom print for every theorem is `[propext, Quot.sound]`, and the finite
character tables (`gate_table`, `chiSigma_eq_not_kMono`) depend on **no
axioms**. There is no `native_decide` and no `sorry`; the upper bound is
constructive (no choice axiom). Correspondence:

| Paper | Lean (`lean/DecBridge/`) |
|---|---|
| Lemma 4.1 | `Words.lean: rises_le_drops_succ` |
| Lemma 4.2 | `Subadd.lean: drop_transfer` |
| Theorem 4.3 | `Subadd.lean: subadd_chain`, `subadd_decOn` |
| Proposition 3.1 | `Gates.lean: gate_table`, `chiSigma_eq_not_kMono` |
| Theorem 5.2 (abstract) | `Hgen.lean: hgen_covering`, `hgen_drops_le` |
| ω is a descent potential | `Cube.lean: cube_descPotential` |
| Lemma 5.1 | `CubeViol.lean: omega_viol` |
| ω = chain-max (both directions) | `CubeDec.lean: chainDrops_le_omega`, `omega_attained` |
| Theorem 5.2(b) exact | `CubeDec.lean: omega_hgen_le` |
| Lemma 6.1 | `Tower.lean: gExt`, `gExt_mono`, `gExt_agrees` |
| Theorem 6.2 upper | `Tower.lean: tower_of_decPts` |
| Corollary 4.4 / Theorem 6.2 lower | `Tower.lean: F1_lower`, `decPts_le_of_tower` |

The Lean development is slightly *more* general than the text: subadditivity
is proved for chains of an arbitrary relation (no order axioms), and the
witness theorem over an abstract descent potential, of which the cube ω
(defined by weight-fuel recursion over lower covers) is an instance. The
upper bound is stated over an explicit finite point family (agreement on the
listed points), which is the meaningful content on the cube. Independent
stdlib-only Python verifications (exhaustive n ≤ 4; randomized n = 5) are in
`verification/`.

## References

1. A. A. Markov, *On the inversion complexity of a system of functions*,
   J. ACM 5(4), 331–334, 1958. (Russian original: Doklady AN SSSR 116(6),
   917–919, 1957.)
2. H. Morizumi, *Limiting Negations in Formulas*, ICALP 2009, LNCS 5555,
   701–712. (Preliminary version: arXiv:0811.0699, 2008.)
3. M. J. Fischer, *Lectures on network complexity*, Tech. Report 1104,
   Yale University, 1974 (revised 1996).
4. M. Santha, C. Wilson, *Limiting negations in constant depth circuits*,
   SIAM J. Comput. 22(2), 294–302, 1993.
5. S. Sung, K. Tanaka, *Limiting negations in bounded-depth circuits: an
   extension of Markov's theorem*, ISAAC 2003, LNCS 2906, 108–116.
6. K. Amano, A. Maruoka, *A superpolynomial lower bound for a circuit
   computing the clique function with at most (1/6)·log log n negation
   gates*, SIAM J. Comput. 35(1), 201–216, 2005.
7. V. V. Kochergin, A. V. Mikhailovich, *Inversion complexity of functions
   of multi-valued logic*, arXiv:1510.05942, 2015; journal version:
   Discrete Math. Appl., 2017.
8. S. Guo, I. Komargodski, *Negation-Limited Formulas*, APPROX/RANDOM 2015
   (LIPIcs).
9. W. C. Yang, *Finite-Energy Epistemic Logic with Conservative Pointed
   Extension and Negation Geometry*, public edition v1.0, 2026.
   https://github.com/ycmath/finite-energy-epistemic-logic
   (an earlier draft circulated as *Finite-energy epistemic logic with
   T0-preserving open updates*).
10. W. C. Yang, *The Price of NOT on D4*, public edition v1.0, 2026.
    https://github.com/ycmath/price-of-not-on-d4

## Authorship & provenance

Produced by *KoreoLoop*, an autonomous multi-agent research loop developed
and operated by the author, running frontier language models (Anthropic
Claude family) for discovery, formalization, and adversarial verification,
with the **Lean 4 kernel as the final acceptance gate**. The author directed
the research programme and verified the pipeline. In line with the author's
research-ethics policy, no claim of academic priority is made beyond full
disclosure of how the work was produced. Corrections are invited.
