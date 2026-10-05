/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.AsymptoticSum
import AlgebraicComplexity.Tensor.Monomial
import AlgebraicComplexity.Tensor.PowerCoherence

/-!
# The Galactic method and its exponent `ω_g`

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  This module formalizes Definition 4.1 and
Lemma 4.1 of

> J. Alman and V. Vassilevska Williams, *Limits on All Known (and Some Unknown) Approaches to
> Matrix Multiplication*, arXiv:1810.08671v1,

hereafter AVW, in the reading fixed as option (i) of `BARRIER_FRAMEWORK.md` §6, milestone D.

## What is defined

A **galactic certificate** for a tensor `T` is the data `(n, a, b, c, F)` together with a
*monomial degeneration* of the `n`th canonical tensor power `T^{⊗n}` onto a direct sum of `F`
disjoint copies of the *same* matrix-multiplication tensor `⟨a,b,c⟩`
(`GalacticCertificate`).  The **galactic exponent** `ω_g(T)` is the infimum of the associated
certificate values

`3 · (log R̲(T^{⊗n}) − log F) / log(abc)`

(`galacticExponent`), and `omega ≤ ω_g(T)` (`omega_le_galacticExponent`) is the theorem that makes
`ω_g` meaningful: every certificate is an algorithm, so the galactic method can never prove an
exponent bound below `ω`.

## Recorded design decisions

**Equal dimensions are definitional (framework option (i)).**  AVW's Lemma 4.1 asserts that one
may restrict attention, without loss of generality, to degenerations into a disjoint sum of
matrix-multiplication tensors *of the same dimensions*, citing the reduction of Schönhage
(*Partial and total matrix multiplication*, SIAM J. Comput. 10 (1981), §7.2; see also M. Bläser,
*Fast Matrix Multiplication*, Theory of Computing Graduate Surveys 5 (2013), Theorem 7.5).  That
reduction is **not** formalized in this repository and is **not** part of the proved statement
`AlgebraicComplexity.asymptoticSumInequality`, which handles arbitrary rectangular families.  We
therefore build the equal-dimension restriction into `GalacticCertificate` itself.  Consequently
Lemma 4.1 is *definitional here*, and the only mathematical obligation left — the one this module
discharges — is soundness, `ω ≤ ω_g(T)`.  Nothing in this module claims the general reduction; a
formalization of it would be a separate project and would only *lower* `ω_g`.

**Which rank of the power.**  AVW write the certificate value with `R̃(T)^n` in place of
`R̲(T^{⊗n})`.  We define `ω_g` (`galacticExponent`) with the **constructive border rank of the
`n`th power**, `Tensor.borderRank (Tensor.power T n)`, because that is the quantity Schönhage's
inequality consumes directly (`asymptoticSum_le_borderRank`), it is a natural number that a finite
certificate can exhibit, and it needs no multiplicativity input.  The sharper AVW-style variant
built on `Tensor.asymptoticRank (Tensor.power T n)` is defined alongside as
`galacticAsymptoticExponent`; both are proved sound, and
`galacticAsymptoticExponent_le_galacticExponent` records the comparison
`ω_g^{R̃} ≤ ω_g` implied by `asymptoticRank ≤ borderRank`.  The two would coincide if
`R̃(T^{⊗n}) = R̃(T)^n` were available; that multiplicativity is *not* proved in this repository, so
no equality is claimed.  A downstream barrier (milestone F) proving a lower bound on
`galacticAsymptoticExponent` automatically bounds `galacticExponent` as well.

**Degenerate certificates are excluded by hypothesis**, not by convention: the defining sets
`galacticValues` and `galacticAsymptoticValues` retain only certificates with `2 ≤ a*b*c` (so that
`log(abc) > 0`) and `1 ≤ F` (so that the `log F` correction is meaningful and the direct sum is
nonempty).

## Principal results

* `omega_le_galacticValue_of_certificate` — the finite, per-certificate form of soundness.
* `omega_le_galacticExponent` — `ω ≤ ω_g(T)` whenever `T` has at least one certificate.
* `two_le_galacticExponent` — `2 ≤ ω_g(T)` whenever `T` has at least one certificate.
* `galacticExponent_le_of_certificate` — every certificate value bounds `ω_g(T)` above.
* `galacticExponent_le_galacticExponent_power` — `ω_g(T) ≤ ω_g(T^{⊗k})`.
* `galacticExponent_isomorphic` — `ω_g` is a legwise-isomorphism invariant.
* `galacticCertificate_matrixMultiplication`, `galacticExponent_matrixMultiplication_le` — the
  trivial certificate `(n, a, b, c, F) = (1, a, b, c, 1)` and its value.
* `galacticExponent_matrixMultiplication_two_le`, `omega_le_log_two_seven_of_borderRankLE` — the
  Strassen regression instance `ω ≤ ω_g(⟨2,2,2⟩) ≤ 3·log 7 / log 8 = log₂ 7`, agreeing in value
  and direction with `omega_le_log_of_rankLE`.

## Non-goals and obligations left open

* No monotonicity of `ω_g` under a monomial degeneration of `T` is proved.  It would require
  (a) transitivity of `Tensor.MonomialDegenerates`, and (b) the statement that the `n`th power of a
  monomial degeneration is again a monomial degeneration *in product coordinates* — neither is
  available, and (b) additionally needs the certificate's coordinate presentation to be a
  relabelling rather than an arbitrary legwise isomorphism, since `MonomialDegenerates` is
  basis-dependent.  Only the isomorphism-invariance `galacticExponent_isomorphic` and the power
  comparison `galacticExponent_le_galacticExponent_power` are proved here.
* `ω_g(T^{⊗k}) = ω_g(T)` is proved only in the direction `ω_g(T) ≤ ω_g(T^{⊗k})`; the reverse
  needs the same power-of-a-monomial-degeneration input as above.
-/

namespace AlgebraicComplexity

open Tensor
open scoped DirectSum

universe u v w

/-! ## Galactic certificates -/

section Definitions

variable (K : Type u) [CommSemiring K]

/-- The direct sum of `F` disjoint copies of the *same* matrix-multiplication tensor `⟨a,b,c⟩`.
This is the equal-dimension target of AVW Definition 4.1 in the reading of framework option (i). -/
noncomputable abbrev matrixMultiplicationCopies (F a b c : ℕ) :
    Tensor3 K (MMDirectSumSpace K (fun _ : Fin F ↦ a) (fun _ : Fin F ↦ b)
      (fun _ : Fin F ↦ c)) :=
  matrixMultiplicationDirectSum K (fun _ : Fin F ↦ a) (fun _ : Fin F ↦ b) (fun _ : Fin F ↦ c)

variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- **A galactic certificate** for `T` with data `(n, a, b, c, F)` (AVW Definition 4.1, option (i)
of `BARRIER_FRAMEWORK.md` §6.D).

It asserts: in some finite coordinate presentation `S` of the `n`th tensor power `T^{⊗n}`, a
monomial degeneration carries `S` onto a tensor `D` legwise isomorphic to the direct sum of `F`
disjoint copies of `⟨a,b,c⟩`.

Direction: `Tensor.power T n` is the **source** and the direct sum is the **target**.  The
`Isomorphic` condition on the source and the `Restricts` condition on the target are bookkeeping
only — `Tensor.MonomialDegenerates` is a basis-dependent relation between two tensors of one
*coordinate* space, so a certificate must name the coordinates in which the weights are read.
Coordinates are indexed by `Fin (k c)` so that the definition needs no extra universe parameter;
every finite index type can be transported there.

The target condition is a *restriction*, not an isomorphism: a monomial degeneration keeps the
variables of its source, so the tensor it produces is the direct sum of copies together with
whatever variables it no longer uses, and those cannot be removed by a legwise isomorphism.  Every
isomorphism is a restriction, so this only enlarges the certificate set and hence only lowers
`ω_g`; soundness is unaffected because a restriction is a degeneration.  The
coordinate-level certificates of `MatrixMultiplication/IndependenceBarrier.lean`, which are the
ones AVW's Section 4 actually counts, land in this relaxed form.

Only the *equal-dimension* target is admitted; see the module doc for the Schönhage/Bläser
reduction that this deliberately does not formalize. -/
def GalacticCertificate (T : Tensor3 K V) (n a b c F : ℕ) : Prop :=
  ∃ (k : Leg → ℕ) (S D : Tensor3 K (CoordinateSpace K fun c ↦ Fin (k c))),
    Isomorphic (Tensor.power T n) S ∧
      MonomialDegenerates S D ∧
      Restricts D (matrixMultiplicationCopies K F a b c)

/-- The value `3 · (log r − log F) / log(abc)` attached to a galactic certificate that reaches `F`
copies of `⟨a,b,c⟩` from a power of border rank (or asymptotic rank) `r`. -/
noncomputable def galacticValue (a b c F : ℕ) (r : ℝ) : ℝ :=
  3 * (Real.log r - Real.log F) / Real.log ((a * b * c : ℕ) : ℝ)

/-- The set of values of the nondegenerate galactic certificates of `T`, measured with the
constructive border rank of the power.  Degenerate certificates are excluded by the hypotheses
`2 ≤ a*b*c` and `1 ≤ F`: when `abc ≤ 1` the denominator `log(abc)` is zero and the quotient carries
no information, and `F = 0` is the empty direct sum, which every tensor degenerates to. -/
def galacticValues (T : Tensor3 K V) : Set ℝ :=
  {x | ∃ n a b c F : ℕ, GalacticCertificate K T n a b c F ∧ 2 ≤ a * b * c ∧ 1 ≤ F ∧
    x = galacticValue a b c F (Tensor.borderRank (Tensor.power T n))}

/-- The same set of certificates, measured with the asymptotic rank of the power.  This is the
variant closest to AVW's `R̃`; see the module doc. -/
def galacticAsymptoticValues (T : Tensor3 K V) : Set ℝ :=
  {x | ∃ n a b c F : ℕ, GalacticCertificate K T n a b c F ∧ 2 ≤ a * b * c ∧ 1 ≤ F ∧
    x = galacticValue a b c F (Tensor.asymptoticRank (Tensor.power T n))}

/-- **The galactic exponent `ω_g(T)`** (AVW Definition 4.1): the infimum of the values of the
nondegenerate galactic certificates of `T`, measured with border rank of the power.

As with `omega` in `MatrixMultiplication/Exponent.lean`, this is a bare `sInf` over `ℝ`; the
hygiene lemmas `galacticValues_bddBelow` (over a field) and `galacticValues_nonempty_of_certificate`
are what make it the mathematical infimum, and every statement that reads `ω_g` from below carries
a nonemptiness hypothesis. -/
noncomputable def galacticExponent (T : Tensor3 K V) : ℝ := sInf (galacticValues K T)

/-- The asymptotic-rank variant of `galacticExponent`; see the module doc for why both are kept. -/
noncomputable def galacticAsymptoticExponent (T : Tensor3 K V) : ℝ :=
  sInf (galacticAsymptoticValues K T)

/-- A galactic certificate is in particular a polynomial degeneration from `T^{⊗n}` onto the
equal-dimension direct sum.  This is the only property of a certificate that soundness uses.

Proof sketch: compose the two legwise isomorphisms (degree-zero degenerations) around the monomial
degeneration, using `Tensor.MonomialDegenerates.toPolynomial` and transitivity. -/
theorem GalacticCertificate.polynomialDegenerates {T : Tensor3 K V} {n a b c F : ℕ}
    (h : GalacticCertificate K T n a b c F) :
    PolynomialDegenerates (Tensor.power T n) (matrixMultiplicationCopies K F a b c) := by
  obtain ⟨_k, _S, _D, hS, hSD, hD⟩ := h
  exact (PolynomialDegenerates.of_restricts hS.restricts).trans
    (hSD.toPolynomial.trans (PolynomialDegenerates.of_restricts hD))

/-- **A certificate for a power is a certificate for the base.**  A galactic certificate of length
`m` for `T^{⊗k}` is a galactic certificate of length `m·k` for `T`, with the same dimensions and
copy count.

Proof sketch: `Tensor.Isomorphic.power_power` identifies `(T^{⊗k})^{⊗m}` with `T^{⊗(m·k)}`, so the
coordinate presentation of the former is one of the latter; nothing else in the certificate
changes. -/
theorem GalacticCertificate.of_power {T : Tensor3 K V} {k m a b c F : ℕ}
    (h : GalacticCertificate K (Tensor.power T k) m a b c F) :
    GalacticCertificate K T (m * k) a b c F := by
  obtain ⟨j, S, D, hS, hSD, hD⟩ := h
  exact ⟨j, S, D, (Isomorphic.power_power T k m).symm.trans hS, hSD, hD⟩

/-- **Certificates transport along legwise isomorphisms.**  If `T` is isomorphic to `T'`, every
galactic certificate of `T'` is one of `T`. -/
theorem GalacticCertificate.isomorphic {W : Leg → Type w}
    [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    {T : Tensor3 K V} {T' : Tensor3 K W} (hiso : Isomorphic T T') {n a b c F : ℕ}
    (h : GalacticCertificate K T' n a b c F) : GalacticCertificate K T n a b c F := by
  obtain ⟨j, S, D, hS, hSD, hD⟩ := h
  exact ⟨j, S, D, (hiso.power n).trans hS, hSD, hD⟩

/-- Certificate values of `T^{⊗k}` are certificate values of `T`: the certificate transports by
`GalacticCertificate.of_power`, and the border rank of the power is an isomorphism invariant, so
the value is unchanged. -/
theorem galacticValues_power_subset (T : Tensor3 K V) (k : ℕ) :
    galacticValues K (Tensor.power T k) ⊆ galacticValues K T := by
  rintro x ⟨m, a, b, c, F, hcert, habc, hF, rfl⟩
  refine ⟨m * k, a, b, c, F, hcert.of_power, habc, hF, ?_⟩
  rw [borderRank_isomorphic (Isomorphic.power_power T k m)]

/-- Legwise isomorphic tensors have the same set of galactic certificate values. -/
theorem galacticValues_isomorphic {W : Leg → Type w}
    [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    {T : Tensor3 K V} {T' : Tensor3 K W} (hiso : Isomorphic T T') :
    galacticValues K T = galacticValues K T' := by
  ext x
  constructor
  · rintro ⟨n, a, b, c, F, hcert, habc, hF, rfl⟩
    refine ⟨n, a, b, c, F, GalacticCertificate.isomorphic K hiso.symm hcert, habc, hF, ?_⟩
    rw [borderRank_isomorphic (hiso.power n)]
  · rintro ⟨n, a, b, c, F, hcert, habc, hF, rfl⟩
    refine ⟨n, a, b, c, F, GalacticCertificate.isomorphic K hiso hcert, habc, hF, ?_⟩
    rw [borderRank_isomorphic (hiso.power n)]

/-- **`ω_g` is a legwise-isomorphism invariant.**  This is the only monotonicity statement about
the *source* tensor that this module proves; see the module doc for why monotonicity under a
monomial degeneration of `T` is not available. -/
theorem galacticExponent_isomorphic {W : Leg → Type w}
    [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    {T : Tensor3 K V} {T' : Tensor3 K W} (hiso : Isomorphic T T') :
    galacticExponent K T = galacticExponent K T' := by
  unfold galacticExponent
  rw [galacticValues_isomorphic K hiso]

end Definitions

/-! ## Soundness: `ω ≤ ω_g` -/

section Soundness

variable (K : Type u) [Field K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- Positivity of the three dimensions is implied by nondegeneracy of the volume. -/
private theorem pos_of_two_le_volume {a b c : ℕ} (habc : 2 ≤ a * b * c) :
    0 < a ∧ 0 < b ∧ 0 < c := by
  refine ⟨Nat.pos_of_ne_zero ?_, Nat.pos_of_ne_zero ?_, Nat.pos_of_ne_zero ?_⟩ <;>
    rintro rfl <;> simp at habc

/-- **The arithmetic core of soundness.**  If the fair price `F · (abc)^{ω/3}` of `F` disjoint
copies of `⟨a,b,c⟩` is at most `r`, then `ω ≤ 3 · (log r − log F) / log(abc)`.

Proof sketch: `2 ≤ abc` makes `log(abc) > 0` and `1 ≤ F` makes the left-hand side positive, hence
`r > 0`.  Taking logarithms of `F · (abc)^{ω/3} ≤ r` and using `log (x^t) = t · log x` gives
`log F + (ω/3)·log(abc) ≤ log r`; rearranging divides by the positive `log(abc)`. -/
theorem omega_le_galacticValue {a b c F : ℕ} {r : ℝ}
    (habc : 2 ≤ a * b * c) (hF : 1 ≤ F)
    (h : (F : ℝ) * ((a * b * c : ℕ) : ℝ) ^ (omega K / 3) ≤ r) :
    omega K ≤ galacticValue a b c F r := by
  have hvpos : (0 : ℝ) < ((a * b * c : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two habc
  have hv2 : (2 : ℝ) ≤ ((a * b * c : ℕ) : ℝ) := by exact_mod_cast habc
  have hL : 0 < Real.log ((a * b * c : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hFpos : (0 : ℝ) < (F : ℝ) := by exact_mod_cast hF
  have hpow : (0 : ℝ) < ((a * b * c : ℕ) : ℝ) ^ (omega K / 3) :=
    Real.rpow_pos_of_pos hvpos _
  have hlhs : (0 : ℝ) < (F : ℝ) * ((a * b * c : ℕ) : ℝ) ^ (omega K / 3) :=
    mul_pos hFpos hpow
  have hrpos : (0 : ℝ) < r := lt_of_lt_of_le hlhs h
  have hlog := Real.log_le_log hlhs h
  rw [Real.log_mul (ne_of_gt hFpos) (ne_of_gt hpow),
    Real.log_rpow hvpos] at hlog
  have hsplit : omega K / 3 * Real.log ((a * b * c : ℕ) : ℝ) =
      omega K * Real.log ((a * b * c : ℕ) : ℝ) / 3 := by ring
  rw [hsplit] at hlog
  unfold galacticValue
  rw [le_div_iff₀ hL]
  linarith

/-- **The finite form of soundness for one certificate, with border rank of the power.**  A
galactic certificate `(n, a, b, c, F)` for `T` forces
`ω ≤ 3 · (log R̲(T^{⊗n}) − log F) / log(abc)`.

This is AVW Lemma 4.1 in the option-(i) reading: the equal-dimension restriction is part of the
certificate, and the content is Schönhage's asymptotic sum inequality
(`asymptoticSum_le_borderRank`) applied to the direct sum of `F` equal copies.

Proof sketch: the certificate gives `PolynomialDegenerates (T^{⊗n}) (⊕_{i<F} ⟨a,b,c⟩)`.  Schönhage
then bounds the fair price `∑_{i<F} (abc)^{ω/3} = F · (abc)^{ω/3}` (via `asymptoticSum_const`) by
`R̲(T^{⊗n})`.  `omega_le_galacticValue` turns that into the logarithmic form. -/
theorem omega_le_galacticValue_of_certificate {T : Tensor3 K V} {n a b c F : ℕ}
    (hcert : GalacticCertificate K T n a b c F) (habc : 2 ≤ a * b * c) (hF : 1 ≤ F) :
    omega K ≤ galacticValue a b c F (Tensor.borderRank (Tensor.power T n)) := by
  obtain ⟨ha, hb, hc⟩ := pos_of_two_le_volume habc
  have hprice := asymptoticSum_le_borderRank K (ι := Fin F) (Tensor.power T n)
    (fun _ ↦ a) (fun _ ↦ b) (fun _ ↦ c) (fun _ ↦ ha) (fun _ ↦ hb) (fun _ ↦ hc)
    hcert.polynomialDegenerates
  rw [asymptoticSum_const] at hprice
  simp only [Fintype.card_fin] at hprice
  exact omega_le_galacticValue K habc hF hprice

/-- **The finite form of soundness for one certificate, with asymptotic rank of the power.**  The
same certificate forces the sharper `ω ≤ 3 · (log R̃(T^{⊗n}) − log F) / log(abc)`.

Proof sketch: identical to `omega_le_galacticValue_of_certificate`, but stopping at
`asymptoticSumInequality` itself, whose right-hand side is the asymptotic rank of the source. -/
theorem omega_le_galacticAsymptoticValue_of_certificate {T : Tensor3 K V} {n a b c F : ℕ}
    (hcert : GalacticCertificate K T n a b c F) (habc : 2 ≤ a * b * c) (hF : 1 ≤ F) :
    omega K ≤ galacticValue a b c F (Tensor.asymptoticRank (Tensor.power T n)) := by
  obtain ⟨ha, hb, hc⟩ := pos_of_two_le_volume habc
  have hprice := asymptoticSumInequality K (Fin F) (PowerSpace K V n) (Tensor.power T n)
    (fun _ ↦ a) (fun _ ↦ b) (fun _ ↦ c) (fun _ ↦ ha) (fun _ ↦ hb) (fun _ ↦ hc)
    hcert.polynomialDegenerates
  rw [asymptoticSum_const] at hprice
  simp only [Fintype.card_fin] at hprice
  exact omega_le_galacticValue K habc hF hprice

/-- Every value of a nondegenerate galactic certificate is at least `ω`. -/
theorem omega_le_of_mem_galacticValues {T : Tensor3 K V} {x : ℝ}
    (hx : x ∈ galacticValues K T) : omega K ≤ x := by
  obtain ⟨n, a, b, c, F, hcert, habc, hF, rfl⟩ := hx
  exact omega_le_galacticValue_of_certificate K hcert habc hF

/-- Every value of a nondegenerate galactic certificate, measured with asymptotic rank, is at
least `ω`. -/
theorem omega_le_of_mem_galacticAsymptoticValues {T : Tensor3 K V} {x : ℝ}
    (hx : x ∈ galacticAsymptoticValues K T) : omega K ≤ x := by
  obtain ⟨n, a, b, c, F, hcert, habc, hF, rfl⟩ := hx
  exact omega_le_galacticAsymptoticValue_of_certificate K hcert habc hF

/-- Soundness bounds the whole certificate-value set below, so its infimum is the genuine one. -/
theorem galacticValues_bddBelow (T : Tensor3 K V) : BddBelow (galacticValues K T) :=
  ⟨omega K, fun _ hx ↦ omega_le_of_mem_galacticValues K hx⟩

/-- Asymptotic-rank companion of `galacticValues_bddBelow`. -/
theorem galacticAsymptoticValues_bddBelow (T : Tensor3 K V) :
    BddBelow (galacticAsymptoticValues K T) :=
  ⟨omega K, fun _ hx ↦ omega_le_of_mem_galacticAsymptoticValues K hx⟩

/-- A nondegenerate certificate populates the value set. -/
theorem galacticValues_nonempty_of_certificate {T : Tensor3 K V} {n a b c F : ℕ}
    (hcert : GalacticCertificate K T n a b c F) (habc : 2 ≤ a * b * c) (hF : 1 ≤ F) :
    (galacticValues K T).Nonempty :=
  ⟨_, ⟨n, a, b, c, F, hcert, habc, hF, rfl⟩⟩

/-- A nondegenerate certificate populates the asymptotic-rank value set. -/
theorem galacticAsymptoticValues_nonempty_of_certificate {T : Tensor3 K V} {n a b c F : ℕ}
    (hcert : GalacticCertificate K T n a b c F) (habc : 2 ≤ a * b * c) (hF : 1 ≤ F) :
    (galacticAsymptoticValues K T).Nonempty :=
  ⟨_, ⟨n, a, b, c, F, hcert, habc, hF, rfl⟩⟩

/-- **Soundness of the Galactic method (AVW Lemma 4.1).**  If `T` admits at least one nondegenerate
galactic certificate, then `ω ≤ ω_g(T)`: no galactic certificate for `T` can prove an exponent bound
below the true matrix-multiplication exponent.

The nonemptiness hypothesis is not cosmetic: `sInf ∅ = 0` in `ℝ`, so without a certificate the
statement would be false for the junk value. -/
theorem omega_le_galacticExponent {T : Tensor3 K V}
    (hne : (galacticValues K T).Nonempty) : omega K ≤ galacticExponent K T :=
  le_csInf hne fun _ hx ↦ omega_le_of_mem_galacticValues K hx

/-- Soundness for the asymptotic-rank variant. -/
theorem omega_le_galacticAsymptoticExponent {T : Tensor3 K V}
    (hne : (galacticAsymptoticValues K T).Nonempty) :
    omega K ≤ galacticAsymptoticExponent K T :=
  le_csInf hne fun _ hx ↦ omega_le_of_mem_galacticAsymptoticValues K hx

/-- **`ω_g(T) ≥ 2` whenever certificates exist**, by soundness and the flattening lower bound
`2 ≤ ω`.  This is the sanity check that the galactic method cannot beat the trivial barrier. -/
theorem two_le_galacticExponent {T : Tensor3 K V}
    (hne : (galacticValues K T).Nonempty) : 2 ≤ galacticExponent K T :=
  le_trans (two_le_omega K) (omega_le_galacticExponent K hne)

/-- `ω_g^{R̃}(T) ≥ 2` whenever certificates exist. -/
theorem two_le_galacticAsymptoticExponent {T : Tensor3 K V}
    (hne : (galacticAsymptoticValues K T).Nonempty) :
    2 ≤ galacticAsymptoticExponent K T :=
  le_trans (two_le_omega K) (omega_le_galacticAsymptoticExponent K hne)

/-- **Every certificate bounds `ω_g` above.**  This is the direction that upper-bound clients use:
exhibiting one certificate exhibits an exponent bound the galactic method achieves. -/
theorem galacticExponent_le_of_certificate {T : Tensor3 K V} {n a b c F : ℕ}
    (hcert : GalacticCertificate K T n a b c F) (habc : 2 ≤ a * b * c) (hF : 1 ≤ F) :
    galacticExponent K T ≤
      galacticValue a b c F (Tensor.borderRank (Tensor.power T n)) :=
  csInf_le (galacticValues_bddBelow K T) ⟨n, a, b, c, F, hcert, habc, hF, rfl⟩

/-- Asymptotic-rank companion of `galacticExponent_le_of_certificate`. -/
theorem galacticAsymptoticExponent_le_of_certificate {T : Tensor3 K V} {n a b c F : ℕ}
    (hcert : GalacticCertificate K T n a b c F) (habc : 2 ≤ a * b * c) (hF : 1 ≤ F) :
    galacticAsymptoticExponent K T ≤
      galacticValue a b c F (Tensor.asymptoticRank (Tensor.power T n)) :=
  csInf_le (galacticAsymptoticValues_bddBelow K T) ⟨n, a, b, c, F, hcert, habc, hF, rfl⟩

end Soundness

/-! ## Comparison of the two measures -/

section Comparison

variable (K : Type u) [Field K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- The certificate value is monotone in the rank measure on positive arguments. -/
private theorem galacticValue_mono {a b c F : ℕ} {r s : ℝ}
    (habc : 2 ≤ a * b * c) (hr : 0 < r) (hrs : r ≤ s) :
    galacticValue a b c F r ≤ galacticValue a b c F s := by
  have hvpos : (0 : ℝ) < ((a * b * c : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two habc
  have hv2 : (2 : ℝ) ≤ ((a * b * c : ℕ) : ℝ) := by exact_mod_cast habc
  have hL : 0 < Real.log ((a * b * c : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hlog : Real.log r ≤ Real.log s := Real.log_le_log hr hrs
  unfold galacticValue
  gcongr

/-- **The AVW-style measure never exceeds the border-rank measure.**  Since
`R̃(T^{⊗n}) ≤ R̲(T^{⊗n})`, every border-rank certificate value dominates the corresponding
asymptotic-rank value, hence `ω_g^{R̃}(T) ≤ ω_g(T)`.

Proof sketch: fix a border-rank value `x` coming from a certificate `(n,a,b,c,F)`.  The same
certificate contributes the asymptotic-rank value `y` with the same `(a,b,c,F)` and rank measure
`R̃(T^{⊗n}) ≤ R̲(T^{⊗n})`.  Soundness gives `R̃(T^{⊗n}) ≥ F · (abc)^{ω/3} > 0`, so `log` is
monotone between the two, hence `y ≤ x` and `sInf` of the asymptotic values is `≤ x`. -/
theorem galacticAsymptoticExponent_le_galacticExponent {T : Tensor3 K V}
    (hne : (galacticValues K T).Nonempty) :
    galacticAsymptoticExponent K T ≤ galacticExponent K T := by
  apply le_csInf hne
  intro x hx
  obtain ⟨n, a, b, c, F, hcert, habc, hF, rfl⟩ := hx
  refine le_trans (galacticAsymptoticExponent_le_of_certificate K hcert habc hF) ?_
  have hpos : (0 : ℝ) < Tensor.asymptoticRank (Tensor.power T n) := by
    obtain ⟨ha, hb, hc⟩ := pos_of_two_le_volume habc
    have hprice := asymptoticSumInequality K (Fin F) (PowerSpace K V n) (Tensor.power T n)
      (fun _ ↦ a) (fun _ ↦ b) (fun _ ↦ c) (fun _ ↦ ha) (fun _ ↦ hb) (fun _ ↦ hc)
      hcert.polynomialDegenerates
    rw [asymptoticSum_const] at hprice
    simp only [Fintype.card_fin] at hprice
    have hFpos : (0 : ℝ) < (F : ℝ) := by exact_mod_cast hF
    have hvpos : (0 : ℝ) < ((a * b * c : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two habc
    exact lt_of_lt_of_le (mul_pos hFpos (Real.rpow_pos_of_pos hvpos _)) hprice
  exact galacticValue_mono habc hpos
    (Tensor.asymptoticRank_le_borderRank (Tensor.power T n))

end Comparison

/-! ## Powers of the source tensor -/

section PowerComparison

variable (K : Type u) [Field K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- **Passing to a power cannot improve the galactic exponent:** `ω_g(T) ≤ ω_g(T^{⊗k})`.

AVW use the equality `ω_g(T^{⊗k}) = ω_g(T)`.  Only this half is proved here, and it is the half
that follows from the certificate calculus alone: every certificate of `T^{⊗k}` of length `m` is a
certificate of `T` of length `m·k` with the same value (`galacticValues_power_subset`), so the
infimum over the larger set is no larger.  The converse would need the `k`th power of a *monomial*
degeneration to be a monomial degeneration in product coordinates, which this repository does not
provide; see the module doc. -/
theorem galacticExponent_le_galacticExponent_power (T : Tensor3 K V) (k : ℕ)
    (hne : (galacticValues K (Tensor.power T k)).Nonempty) :
    galacticExponent K T ≤ galacticExponent K (Tensor.power T k) :=
  le_csInf hne fun _ hx ↦
    csInf_le (galacticValues_bddBelow K T) (galacticValues_power_subset K T k hx)

end PowerComparison

/-! ## The trivial certificate, and the Strassen regression instance -/

section TrivialCertificate

variable (K : Type u) [CommSemiring K]

/-- Present the matrix-multiplication index sets in the `Fin`-indexed coordinates required by
`GalacticCertificate`. -/
private noncomputable def mmFinRelabel (a b c : ℕ) (leg : Leg) :
    MMIndex a b c leg ≃ Fin (Fintype.card (MMIndex a b c leg)) :=
  Fintype.equivFin _

/-- **The trivial galactic certificate.**  The matrix-multiplication tensor `⟨a,b,c⟩` is itself a
degeneration (indeed a coordinate presentation) of its own first power onto a direct sum of one
copy of `⟨a,b,c⟩`: `GalacticCertificate K ⟨a,b,c⟩ 1 a b c 1`.

Proof sketch: take the coordinate presentation of `⟨a,b,c⟩` obtained by relabelling each
`MMIndex` leg to `Fin` (`Tensor.relabelLegEquiv`), use the reflexive monomial degeneration
`Tensor.MonomialDegenerates.refl` (all weights zero), and identify a one-element direct sum with its
single summand (`Tensor.Isomorphic.indexedDirectSum_unique`).  The source side additionally uses
`Tensor.power_one_eq_powerOne` and the first-power transport. -/
theorem galacticCertificate_matrixMultiplication (a b c : ℕ) :
    GalacticCertificate K (matrixMultiplication (K := K) a b c) 1 a b c 1 := by
  classical
  set T := matrixMultiplication (K := K) a b c with hT
  set e : ∀ leg, MMSpace K a b c leg ≃ₗ[K]
      CoordinateSpace K (fun leg ↦ Fin (Fintype.card (MMIndex a b c leg))) leg :=
    fun leg ↦ relabelLegEquiv K (mmFinRelabel a b c) leg with he
  have hpres : Isomorphic T (Tensor.map (fun leg ↦ (e leg).toLinearMap) T) :=
    Isomorphic.map T e
  have hone : Isomorphic (Tensor.power T 1) T := by
    rw [Tensor.power_one_eq_powerOne]
    exact (Isomorphic.powerOneTransport T).symm
  have hsum : Isomorphic T (matrixMultiplicationCopies K 1 a b c) :=
    (Isomorphic.indexedDirectSum_unique (ι := Fin 1) T).symm
  exact ⟨fun leg ↦ Fintype.card (MMIndex a b c leg), _, _,
    hone.trans hpres, MonomialDegenerates.refl _, (hpres.symm.trans hsum).restricts⟩

/-- With a single copy the `log F` correction vanishes. -/
theorem galacticValue_one (a b c : ℕ) (r : ℝ) :
    galacticValue a b c 1 r = 3 * Real.log r / Real.log ((a * b * c : ℕ) : ℝ) := by
  simp [galacticValue]

end TrivialCertificate

section TrivialCertificateField

variable (K : Type u) [Field K]

/-- **The value of the trivial certificate.**  For every `a, b, c` with `abc ≥ 2`,

`ω_g(⟨a,b,c⟩) ≤ 3 · log R̲(⟨a,b,c⟩) / log(abc)`.

Proof sketch: `galacticExponent_le_of_certificate` applied to
`galacticCertificate_matrixMultiplication`, then `borderRank_power_one` and `galacticValue_one`. -/
theorem galacticExponent_matrixMultiplication_le {a b c : ℕ} (habc : 2 ≤ a * b * c) :
    galacticExponent K (matrixMultiplication (K := K) a b c) ≤
      3 * Real.log (Tensor.borderRank (matrixMultiplication (K := K) a b c)) /
        Real.log ((a * b * c : ℕ) : ℝ) := by
  have h := galacticExponent_le_of_certificate K
    (galacticCertificate_matrixMultiplication K a b c) habc le_rfl
  rwa [borderRank_power_one, galacticValue_one] at h

/-- `⟨a,b,c⟩` always has at least the trivial certificate, so its value set is nonempty and `ω_g`
is a genuine infimum. -/
theorem galacticValues_matrixMultiplication_nonempty {a b c : ℕ} (habc : 2 ≤ a * b * c) :
    (galacticValues K (matrixMultiplication (K := K) a b c)).Nonempty :=
  galacticValues_nonempty_of_certificate K
    (galacticCertificate_matrixMultiplication K a b c) habc le_rfl

/-- **Strassen's instance, upper half.**  A border-rank-seven decomposition of `⟨2,2,2⟩` gives

`ω_g(⟨2,2,2⟩) ≤ 3 · log 7 / log 8 = log 7 / log 2 = log₂ 7`.

Proof sketch: the trivial certificate has volume `2·2·2 = 8` and one copy, so its value is
`3 · log R̲(⟨2,2,2⟩) / log 8`; monotonicity of `log` and `R̲ ≤ 7` replace `R̲` by `7`, and
`log 8 = 3 log 2` cancels the factor three. -/
theorem galacticExponent_matrixMultiplication_two_le
    (h7 : BorderRankLE 7 (matrixMultiplication (K := K) 2 2 2)) :
    galacticExponent K (matrixMultiplication (K := K) 2 2 2) ≤ Real.log 7 / Real.log 2 := by
  have hbr : Tensor.borderRank (matrixMultiplication (K := K) 2 2 2) ≤ 7 :=
    borderRank_le_iff.mpr h7
  have hlog : Real.log (Tensor.borderRank (matrixMultiplication (K := K) 2 2 2) : ℝ) ≤
      Real.log 7 := by
    rcases Nat.eq_zero_or_pos (Tensor.borderRank (matrixMultiplication (K := K) 2 2 2)) with
      h0 | h0
    · rw [h0]
      simpa using Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 7)
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hbr)
  have hvol : (((2 * 2 * 2 : ℕ) : ℝ)) = 8 := by norm_num
  have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine le_trans (galacticExponent_matrixMultiplication_le K (by norm_num)) ?_
  rw [hvol, hlog8]
  rw [div_le_div_iff₀ (by positivity) hlog2]
  nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 7)]

/-- **Direction-of-inequality regression test.**  Chaining soundness with the trivial certificate
reproduces Strassen's classical bound through the galactic exponent:

`ω ≤ ω_g(⟨2,2,2⟩) ≤ log₂ 7`.

This matches `omega_le_log_of_rankLE` numerically (`Real.log 7 / Real.log 2`), and confirms that
the definition of `ω_g` points in the intended direction — a galactic certificate is an upper bound
on `ω_g`, and `ω_g` is an upper bound on `ω`.  Note the hypothesis here is only a *border*-rank
certificate, whereas `omega_le_log_of_rankLE` needs an exact rank certificate. -/
theorem omega_le_log_two_seven_of_borderRankLE
    (h7 : BorderRankLE 7 (matrixMultiplication (K := K) 2 2 2)) :
    omega K ≤ Real.log 7 / Real.log 2 :=
  le_trans
    (omega_le_galacticExponent K (galacticValues_matrixMultiplication_nonempty K (by norm_num)))
    (galacticExponent_matrixMultiplication_two_le K h7)

end TrivialCertificateField

end AlgebraicComplexity
