/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.GalacticMethod
import AlgebraicComplexity.MatrixMultiplication.TypeExtraction
import AlgebraicComplexity.MatrixMultiplication.Compression

/-!
# The Universal method and its exponent `ω_u`

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  This module formalizes Section 4.5 of

> J. Alman, *Limits on the Universal Method for Matrix Multiplication*, PhD thesis, MIT, 2019
> (see also J. Alman, *Limits on the Universal Method for Matrix Multiplication*, CCC 2019),

hereafter [Alman2019]: the definition of the universal exponent `ω_u`, its soundness
`ω ≤ ω_u`, Proposition 4.3 (*one matrix-multiplication tensor without loss of generality*), and
the Section 5.2 barrier Theorem 5.1 / Corollary 5.2 in the abstract form that a future
asymptotic-slice-rank module can instantiate in one line.

## What is defined

A **universal certificate** for `T` with data `(n, q)` is a *polynomial degeneration* of the
`n`th canonical tensor power `T^{⊗n}` onto the **single** square matrix-multiplication tensor
`⟨q,q,q⟩` (`UniversalCertificate`).  The certificate value is

`log R̃(T^{⊗n}) / log q`

(`universalValue`), and the **universal exponent** `ω_u(T)` (`universalExponent`) is the infimum
of the values of the nondegenerate certificates.  The variant measured with the *constructive
border rank* of the power is `universalBorderExponent`; both are proved sound, and
`universalExponent_le_universalBorderExponent` records `ω_u^{R̃} ≤ ω_u^{R̲}`.

## Recorded design decisions

**A single matrix-multiplication tensor, not a disjoint sum.**  This is the whole point of the
Universal method as opposed to the Solar/Galactic methods, and it is what makes Proposition 4.3
a theorem rather than a definition.  The target of a certificate is therefore
`matrixMultiplication K q q q` and not `matrixMultiplicationCopies K F q q q`.

**Which rank of the power.**  [Alman2019] measures the cost of the `n`th power by `r^n` for a
bound `R̃(T) ≤ r`.  The primary definition here measures it by `R̃(T^{⊗n})` itself, exactly as
`MatrixMultiplication/GalacticMethod.lean` measures a galactic certificate by
`R̲(T^{⊗n})` rather than by `R̲(T)^n`.  Because only the half `R̃(T)^n ≤ R̃(T^{⊗n})` of
multiplicativity is available in this repository
(`Tensor.asymptoticRank_pow_le_asymptoticRank_power`), the present choice is the one that makes
*both* directions of the theory work: it gives soundness with no multiplicativity input at all,
and it gives the barrier Theorem 5.1 from the available half.  The thesis-shaped statement with
budget `r^n` is proved as a corollary
(`universalExponent_le_of_copies_of_asymptoticRank_le`), where the passage
`R̃(T^{⊗N}) ≤ r^N` is supplied by `Tensor.asymptoticRank_power_le_pow_of_lt` below.

**Degenerate certificates are excluded by hypothesis.**  `universalValues` retains only
certificates with `2 ≤ q` (so that `log q > 0`) and `1 ≤ n` (a zeroth power carries no
information).

**`ω_u ≤ ω_g` holds for square galactic certificates only.**  [Alman2019] defines `ω_g` with a
disjoint sum of copies of a *square* `⟨q,q,q⟩`, and the chain `ω ≤ ω_u ≤ ω_g ≤ ω_s` of its
Section 4.5.1 is stated for that definition.  The `GalacticCertificate` of
`MatrixMultiplication/GalacticMethod.lean` follows AVW instead and admits a *rectangular*
`⟨a,b,c⟩`; for rectangular targets the inequality `ω_u(T) ≤ ω_g(T)` is **false** in general (the
thesis' own discussion after Proposition 4.3 explains that rectangular targets are absorbed only
after replacing `T` by its symmetrization `sym(T)`; already `T = ⟨q,1,1⟩` has a galactic
certificate but no universal certificate at all).  This module therefore proves
`universalExponent_le_galacticValue_of_square_certificate` and
`universalExponent_le_squareGalacticExponent` for the square sub-family
`squareGalacticValues ⊆ galacticValues`, and records the general statement as a non-goal.

## Principal results

* `omega_le_universalValue_of_certificate`, `omega_le_universalExponent` — soundness, from
  Schönhage's asymptotic sum inequality exactly as in `omega_le_galacticExponent`.
* `two_le_universalExponent` — `2 ≤ ω_u(T)` whenever `T` has a certificate.
* `universalExponent_le_of_certificate` — every certificate bounds `ω_u` above.
* `universalExponent_mul_log_add_log_le` — **Proposition 4.3**, in the form
  `ω_u(T)·log q + log F ≤ log B` for any budget `B` with `R̃(T^{⊗mn}) ≤ B^m`.
* `universalExponent_le_of_copies_of_asymptoticRank_le` — Proposition 4.3 in the thesis' shape:
  `R̃(T) ≤ r` and `F ⊙ ⟨q,q,q⟩ ⊴ T^{⊗n}` give `ω_u(T) ≤ log(r^n/F) / log q`.
* `universalExponent_le_squareGalacticExponent` — the chain `ω ≤ ω_u ≤ ω_g^{square}`.
* `two_mul_log_div_log_le_universalExponent` — **Theorem 5.1**,
  `ω_u(T) ≥ 2·log R / log S` from abstract hypotheses on `R` (a lower bound for `R̃`) and `S` (an
  upper bound for an asymptotic-slice-rank-like measure).
* `two_div_le_universalExponent` — **Corollary 5.2**, `S ≤ R^s` with `s < 1` gives `2/s ≤ ω_u`.

## Non-goals and obligations left open

* Asymptotic slice rank itself is not defined here; Theorem 5.1 is stated against the two
  abstract measure sequences `fPower` and `fMM` and the numerical hypotheses
  they must satisfy (`two_mul_log_div_log_le_universalExponent_of_measure`).  Instantiating
  `fPower n = S̃(T^{⊗n})` and `fMM q = S̃(⟨q,q,q⟩)` once `Tensor/AsymptoticSliceRank.lean` lands is
  one line each.
* `ω_u(T) ≤ ω_g(T)` for *rectangular* galactic certificates is a non-theorem; see above.
* There is deliberately **no** coordinate-table twin of `universalExponent`.  The
  abstract/coordinate split of
  `MatrixMultiplication/IndependenceBarrier.lean`'s `coordinateGalacticExponent` exists
  because `Tensor.MonomialDegenerates` is a *basis-dependent* relation, so a galactic certificate
  must name the coordinates in which its weights are read.  `Tensor.PolynomialDegenerates` is
  basis-free and `universalExponent_isomorphic` already records invariance, so nothing is gained
  by a coordinate presentation here.
* `Tensor.asymptoticRank_power_le_pow_of_lt` (the strict missing half of the power law) lives in
  `Tensor/AsymptoticRank.lean`; Proposition 4.3 consumes it.
-/

namespace AlgebraicComplexity

open Tensor
open scoped DirectSum

universe u v w

/-! ## Auxiliary lemmas proposed for promotion

The first two statements are finite combinatorial facts about `Tensor.PositiveWord`; the third is
the layer-1 asymptotic-rank fact discussed in the module documentation.  They are proved here
because their natural target modules are owned by concurrent work. -/

section Auxiliary

variable {K : Type u} [CommSemiring K]

/-- Every word of length `m + 1` over `Fin F` has constant dimension product `q ^ (m + 1)`. -/
private theorem positiveWordProduct_const (F q m : ℕ)
    (word : Tensor.PositiveWord (Fin F) m) :
    positiveWordProduct (fun _ : Fin F ↦ q) m word = q ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih => simp [positiveWordProduct_succ, ih, pow_succ]

/-- There are exactly `F ^ (m + 1)` words of length `m + 1` over `Fin F`. -/
private theorem card_positiveWord_fin (F m : ℕ) :
    Fintype.card (Tensor.PositiveWord (Fin F) m) = F ^ (m + 1) := by
  rw [Fintype.card_congr (Tensor.positiveWordEquiv (Fin F) m)]
  simp

variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]


end Auxiliary

/-! ## From many copies to one matrix-multiplication tensor

The finite algebraic heart of Proposition 4.3: a power of a direct sum of `F` copies of
`⟨q,q,q⟩` is a direct sum of `F^m` copies of `⟨q^m,q^m,q^m⟩`, and an exact rank-`F^m` algorithm
for `⟨a,a,a⟩` substitutes those copies into its scalar multiplication slots. -/

section Copies

variable {K : Type u} [CommSemiring K]

/-- **A power of equal matrix-multiplication copies is again equal copies.**  The `(m+1)`st
canonical power of `F ⊙ ⟨q,q,q⟩` is legwise isomorphic to `F^{m+1} ⊙ ⟨q^{m+1},q^{m+1},q^{m+1}⟩`,
the copies being indexed by the words of length `m+1` over `Fin F`.

Proof sketch: transport the canonical power to the left-associated positive external power
(`Tensor.Isomorphic.power_positive_iteratedExternal`), expand that external power of a direct sum
into the direct sum over all words (`Tensor.Isomorphic.iteratedExternal_indexedDirectSum`), and
identify each word tensor with the rectangular tensor of its dimension products
(`Tensor.Isomorphic.positiveWordTensor_matrixMultiplication`), which for a constant family is
`⟨q^{m+1},q^{m+1},q^{m+1}⟩`. -/
theorem Tensor.Isomorphic.power_matrixMultiplicationCopies (F q m : ℕ) :
    Isomorphic (Tensor.power (matrixMultiplicationCopies K F q q q) (m + 1))
      (Tensor.indexedDirectSum
        (fun _ : Tensor.PositiveWord (Fin F) m ↦
          matrixMultiplication (K := K) (q ^ (m + 1)) (q ^ (m + 1)) (q ^ (m + 1)))) := by
  have h1 := Tensor.Isomorphic.power_positive_iteratedExternal
    (Tensor.indexedDirectSumFamily (matrixMultiplicationFamily (K := K)
      (fun _ : Fin F ↦ q) (fun _ ↦ q) (fun _ ↦ q)))
    (Tensor.indexedDirectSum
      (matrixMultiplicationTensorFamily (K := K) (fun _ : Fin F ↦ q) (fun _ ↦ q) (fun _ ↦ q))) m
  have h2 := Tensor.Isomorphic.iteratedExternal_indexedDirectSum
    (matrixMultiplicationFamily (K := K) (fun _ : Fin F ↦ q) (fun _ ↦ q) (fun _ ↦ q))
    (matrixMultiplicationTensorFamily (K := K) (fun _ : Fin F ↦ q) (fun _ ↦ q) (fun _ ↦ q)) m
  have h3 : Isomorphic
      (Tensor.indexedDirectSum
        (Tensor.positiveWordTensor
          (matrixMultiplicationFamily (K := K) (fun _ : Fin F ↦ q) (fun _ ↦ q) (fun _ ↦ q))
          (matrixMultiplicationTensorFamily (K := K)
            (fun _ : Fin F ↦ q) (fun _ ↦ q) (fun _ ↦ q)) m))
      (Tensor.indexedDirectSum
        (fun _ : Tensor.PositiveWord (Fin F) m ↦
          matrixMultiplication (K := K) (q ^ (m + 1)) (q ^ (m + 1)) (q ^ (m + 1)))) := by
    refine Tensor.Isomorphic.indexedDirectSum fun word ↦ ?_
    have h := Tensor.Isomorphic.positiveWordTensor_matrixMultiplication (K := K)
      (fun _ : Fin F ↦ q) (fun _ ↦ q) (fun _ ↦ q) m word
    rwa [positiveWordProduct_const] at h
  exact (h1.trans h2).trans h3

/-- **Copy trading.**  If `⟨a,a,a⟩` has an exact algorithm with `F^{m+1}` multiplications, then
the `(m+1)`st power of `F ⊙ ⟨q,q,q⟩` restricts to the single square tensor
`⟨a·q^{m+1}, a·q^{m+1}, a·q^{m+1}⟩`.

Proof sketch: `Tensor.Isomorphic.power_matrixMultiplicationCopies` turns the power into
`F^{m+1}` independent copies of `⟨q^{m+1},q^{m+1},q^{m+1}⟩`, and Schönhage's compression step
`Tensor.RankLE.matrixMultiplication_compression_card` substitutes one copy into each of the
`F^{m+1} = R(⟨a,a,a⟩)` scalar slots. -/
theorem Tensor.Restricts.power_matrixMultiplicationCopies_compression
    (F q m a : ℕ)
    (hrank : RankLE (F ^ (m + 1)) (matrixMultiplication (K := K) a a a)) :
    Restricts (Tensor.power (matrixMultiplicationCopies K F q q q) (m + 1))
      (matrixMultiplication (K := K)
        (a * q ^ (m + 1)) (a * q ^ (m + 1)) (a * q ^ (m + 1))) := by
  refine (Tensor.Isomorphic.power_matrixMultiplicationCopies (K := K) F q m).restricts.trans ?_
  refine Tensor.RankLE.matrixMultiplication_compression_card
    (ι := Tensor.PositiveWord (Fin F) m) ?_
  rwa [card_positiveWord_fin]

end Copies

/-! ## Universal certificates -/

section Definitions

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- **A universal certificate** for `T` with data `(n, q)` ([Alman2019], §4.5, step (2)): a
polynomial degeneration of the `n`th canonical tensor power of `T` onto the single square
matrix-multiplication tensor `⟨q,q,q⟩`.

Direction: `Tensor.power T n` is the **source** and `⟨q,q,q⟩` is the **target**. -/
def UniversalCertificate (T : Tensor3 K V) (n q : ℕ) : Prop :=
  PolynomialDegenerates (Tensor.power T n) (matrixMultiplication (K := K) q q q)

/-- The value `log r / log q` attached to a universal certificate reaching `⟨q,q,q⟩` from a power
of rank measure `r`. -/
noncomputable def universalValue (q : ℕ) (r : ℝ) : ℝ :=
  Real.log r / Real.log (q : ℝ)

/-- The set of values of the nondegenerate universal certificates of `T`, measured with the
asymptotic rank of the power.  This is [Alman2019]'s `ω_u` measure `R̃`. -/
def universalValues (T : Tensor3 K V) : Set ℝ :=
  {x | ∃ n q : ℕ, UniversalCertificate K T n q ∧ 2 ≤ q ∧ 1 ≤ n ∧
    x = universalValue q (Tensor.asymptoticRank (Tensor.power T n))}

/-- The same certificates, measured with the constructive border rank of the power.  This is the
variant that mirrors `galacticValues` exactly. -/
def universalBorderValues (T : Tensor3 K V) : Set ℝ :=
  {x | ∃ n q : ℕ, UniversalCertificate K T n q ∧ 2 ≤ q ∧ 1 ≤ n ∧
    x = universalValue q (Tensor.borderRank (Tensor.power T n))}

/-- **The universal exponent `ω_u(T)`** ([Alman2019], §4.5): the infimum of the values of the
nondegenerate universal certificates of `T`.

As with `omega` and `galacticExponent`, this is a bare `sInf` over `ℝ`; the hygiene lemmas
`universalValues_bddBelow` (over a field) and `universalValues_nonempty_of_certificate` are what
make it the mathematical infimum, and every statement reading `ω_u` from below carries a
nonemptiness hypothesis. -/
noncomputable def universalExponent (T : Tensor3 K V) : ℝ := sInf (universalValues K T)

/-- The border-rank variant of `universalExponent`. -/
noncomputable def universalBorderExponent (T : Tensor3 K V) : ℝ :=
  sInf (universalBorderValues K T)

/-- A universal certificate for a power is a universal certificate for the base, of length
multiplied by the inner exponent. -/
theorem UniversalCertificate.of_power {T : Tensor3 K V} {k m q : ℕ}
    (h : UniversalCertificate K (Tensor.power T k) m q) :
    UniversalCertificate K T (m * k) q :=
  (PolynomialDegenerates.of_restricts
    (Tensor.Isomorphic.power_power T k m).symm.restricts).trans h

/-- Universal certificates transport along legwise isomorphisms. -/
theorem UniversalCertificate.isomorphic {W : Leg → Type w}
    [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    {T : Tensor3 K V} {T' : Tensor3 K W} (hiso : Isomorphic T T') {n q : ℕ}
    (h : UniversalCertificate K T' n q) : UniversalCertificate K T n q :=
  (PolynomialDegenerates.of_restricts (hiso.power n).restricts).trans h

/-- Legwise isomorphic tensors have the same set of universal certificate values. -/
theorem universalValues_isomorphic {W : Leg → Type w}
    [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    {T : Tensor3 K V} {T' : Tensor3 K W} (hiso : Isomorphic T T') :
    universalValues K T = universalValues K T' := by
  ext x
  constructor
  · rintro ⟨n, q, hcert, hq, hn, rfl⟩
    refine ⟨n, q, UniversalCertificate.isomorphic K hiso.symm hcert, hq, hn, ?_⟩
    rw [Tensor.asymptoticRank_isomorphic (hiso.power n)]
  · rintro ⟨n, q, hcert, hq, hn, rfl⟩
    refine ⟨n, q, UniversalCertificate.isomorphic K hiso hcert, hq, hn, ?_⟩
    rw [Tensor.asymptoticRank_isomorphic (hiso.power n)]

/-- **`ω_u` is a legwise-isomorphism invariant.** -/
theorem universalExponent_isomorphic {W : Leg → Type w}
    [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    {T : Tensor3 K V} {T' : Tensor3 K W} (hiso : Isomorphic T T') :
    universalExponent K T = universalExponent K T' := by
  unfold universalExponent
  rw [universalValues_isomorphic K hiso]

end Definitions

/-! ## Soundness: `ω ≤ ω_u` -/

section Soundness

variable (K : Type u) [Field K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- A universal certificate is in particular a degeneration onto a one-summand direct sum, the
shape consumed by Schönhage's asymptotic sum inequality. -/
theorem UniversalCertificate.polynomialDegenerates_copies {T : Tensor3 K V} {n q : ℕ}
    (h : UniversalCertificate K T n q) :
    PolynomialDegenerates (Tensor.power T n) (matrixMultiplicationCopies K 1 q q q) :=
  h.trans (PolynomialDegenerates.of_restricts
    (Tensor.Isomorphic.indexedDirectSum_unique (ι := Fin 1)
      (matrixMultiplication (K := K) q q q)).symm.restricts)

/-- **The fixed-size form of soundness.**  A universal certificate `(n,q)` forces
`q^ω ≤ R̃(T^{⊗n})`.

Proof sketch: Schönhage's asymptotic sum inequality applied to the one-summand direct sum gives
`(q·q·q)^{ω/3} ≤ R̃(T^{⊗n})`, and `(q³)^{ω/3} = q^ω`. -/
theorem rpow_omega_le_asymptoticRank_power_of_certificate {T : Tensor3 K V} {n q : ℕ}
    (hq : 2 ≤ q) (hcert : UniversalCertificate K T n q) :
    (q : ℝ) ^ omega K ≤ Tensor.asymptoticRank (Tensor.power T n) := by
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_two hq
  have hprice := asymptoticSumInequality K (Fin 1) (PowerSpace K V n) (Tensor.power T n)
    (fun _ ↦ q) (fun _ ↦ q) (fun _ ↦ q) (fun _ ↦ hqpos) (fun _ ↦ hqpos) (fun _ ↦ hqpos)
    hcert.polynomialDegenerates_copies
  rw [asymptoticSum_const] at hprice
  simp only [Fintype.card_fin, Nat.cast_one, one_mul] at hprice
  refine le_trans (le_of_eq ?_) hprice
  have hcube : (((q * q * q : ℕ) : ℝ)) = (q : ℝ) ^ (3 : ℕ) := by push_cast; ring
  rw [hcube, ← Real.rpow_natCast (q : ℝ) 3, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- **The arithmetic core of soundness.**  If `q^ω ≤ r` and `2 ≤ q`, then
`ω ≤ log r / log q`. -/
theorem omega_le_universalValue {q : ℕ} {r : ℝ}
    (hq : 2 ≤ q) (h : (q : ℝ) ^ omega K ≤ r) :
    omega K ≤ universalValue q r := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hL : 0 < Real.log (q : ℝ) := Real.log_pos (by linarith)
  have hpow : (0 : ℝ) < (q : ℝ) ^ omega K := Real.rpow_pos_of_pos hqpos _
  have hlog := Real.log_le_log hpow h
  rw [Real.log_rpow hqpos] at hlog
  unfold universalValue
  rw [le_div_iff₀ hL]
  linarith

/-- **Soundness for one certificate.**  A universal certificate `(n,q)` forces
`ω ≤ log R̃(T^{⊗n}) / log q`: the Universal method can never prove an exponent bound below the
true matrix-multiplication exponent. -/
theorem omega_le_universalValue_of_certificate {T : Tensor3 K V} {n q : ℕ}
    (hcert : UniversalCertificate K T n q) (hq : 2 ≤ q) :
    omega K ≤ universalValue q (Tensor.asymptoticRank (Tensor.power T n)) :=
  omega_le_universalValue K hq
    (rpow_omega_le_asymptoticRank_power_of_certificate K hq hcert)

/-- Soundness for one certificate, measured with the border rank of the power. -/
theorem omega_le_universalBorderValue_of_certificate {T : Tensor3 K V} {n q : ℕ}
    (hcert : UniversalCertificate K T n q) (hq : 2 ≤ q) :
    omega K ≤ universalValue q (Tensor.borderRank (Tensor.power T n)) :=
  omega_le_universalValue K hq
    ((rpow_omega_le_asymptoticRank_power_of_certificate K hq hcert).trans
      (Tensor.asymptoticRank_le_borderRank (Tensor.power T n)))

/-- Every value of a nondegenerate universal certificate is at least `ω`. -/
theorem omega_le_of_mem_universalValues {T : Tensor3 K V} {x : ℝ}
    (hx : x ∈ universalValues K T) : omega K ≤ x := by
  obtain ⟨n, q, hcert, hq, _, rfl⟩ := hx
  exact omega_le_universalValue_of_certificate K hcert hq

/-- Every border-rank-measured value of a nondegenerate universal certificate is at least `ω`. -/
theorem omega_le_of_mem_universalBorderValues {T : Tensor3 K V} {x : ℝ}
    (hx : x ∈ universalBorderValues K T) : omega K ≤ x := by
  obtain ⟨n, q, hcert, hq, _, rfl⟩ := hx
  exact omega_le_universalBorderValue_of_certificate K hcert hq

/-- Soundness bounds the certificate-value set below, so its infimum is the genuine one. -/
theorem universalValues_bddBelow (T : Tensor3 K V) : BddBelow (universalValues K T) :=
  ⟨omega K, fun _ hx ↦ omega_le_of_mem_universalValues K hx⟩

/-- Border-rank companion of `universalValues_bddBelow`. -/
theorem universalBorderValues_bddBelow (T : Tensor3 K V) :
    BddBelow (universalBorderValues K T) :=
  ⟨omega K, fun _ hx ↦ omega_le_of_mem_universalBorderValues K hx⟩

/-- A nondegenerate certificate populates the value set. -/
theorem universalValues_nonempty_of_certificate {T : Tensor3 K V} {n q : ℕ}
    (hcert : UniversalCertificate K T n q) (hq : 2 ≤ q) (hn : 1 ≤ n) :
    (universalValues K T).Nonempty :=
  ⟨_, ⟨n, q, hcert, hq, hn, rfl⟩⟩

/-- A nondegenerate certificate populates the border-rank value set. -/
theorem universalBorderValues_nonempty_of_certificate {T : Tensor3 K V} {n q : ℕ}
    (hcert : UniversalCertificate K T n q) (hq : 2 ≤ q) (hn : 1 ≤ n) :
    (universalBorderValues K T).Nonempty :=
  ⟨_, ⟨n, q, hcert, hq, hn, rfl⟩⟩

/-- **Soundness of the Universal method** ([Alman2019], §4.5): `ω ≤ ω_u(T)` whenever `T` admits
at least one nondegenerate universal certificate.

The nonemptiness hypothesis is not cosmetic: `sInf ∅ = 0` in `ℝ`. -/
theorem omega_le_universalExponent {T : Tensor3 K V}
    (hne : (universalValues K T).Nonempty) : omega K ≤ universalExponent K T :=
  le_csInf hne fun _ hx ↦ omega_le_of_mem_universalValues K hx

/-- Soundness for the border-rank variant. -/
theorem omega_le_universalBorderExponent {T : Tensor3 K V}
    (hne : (universalBorderValues K T).Nonempty) :
    omega K ≤ universalBorderExponent K T :=
  le_csInf hne fun _ hx ↦ omega_le_of_mem_universalBorderValues K hx

/-- **`ω_u(T) ≥ 2` whenever certificates exist**, by soundness and the flattening bound
`2 ≤ ω`. -/
theorem two_le_universalExponent {T : Tensor3 K V}
    (hne : (universalValues K T).Nonempty) : 2 ≤ universalExponent K T :=
  le_trans (two_le_omega K) (omega_le_universalExponent K hne)

/-- **Every certificate bounds `ω_u` above.** -/
theorem universalExponent_le_of_certificate {T : Tensor3 K V} {n q : ℕ}
    (hcert : UniversalCertificate K T n q) (hq : 2 ≤ q) (hn : 1 ≤ n) :
    universalExponent K T ≤
      universalValue q (Tensor.asymptoticRank (Tensor.power T n)) :=
  csInf_le (universalValues_bddBelow K T) ⟨n, q, hcert, hq, hn, rfl⟩

/-- Border-rank companion of `universalExponent_le_of_certificate`. -/
theorem universalBorderExponent_le_of_certificate {T : Tensor3 K V} {n q : ℕ}
    (hcert : UniversalCertificate K T n q) (hq : 2 ≤ q) (hn : 1 ≤ n) :
    universalBorderExponent K T ≤
      universalValue q (Tensor.borderRank (Tensor.power T n)) :=
  csInf_le (universalBorderValues_bddBelow K T) ⟨n, q, hcert, hq, hn, rfl⟩

/-- The universal value is monotone in the rank measure on positive arguments. -/
private theorem universalValue_mono {q : ℕ} {r s : ℝ}
    (hq : 2 ≤ q) (hr : 0 < r) (hrs : r ≤ s) :
    universalValue q r ≤ universalValue q s := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hL : 0 < Real.log (q : ℝ) := Real.log_pos (by linarith)
  have hlog : Real.log r ≤ Real.log s := Real.log_le_log hr hrs
  unfold universalValue
  gcongr

/-- **The asymptotic-rank measure never exceeds the border-rank measure**, so
`ω_u^{R̃}(T) ≤ ω_u^{R̲}(T)`.

Proof sketch: the same certificate contributes both values, `R̃(T^{⊗n}) ≤ R̲(T^{⊗n})`, and
soundness makes `R̃(T^{⊗n}) ≥ q^ω > 0`, so `log` is monotone between them. -/
theorem universalExponent_le_universalBorderExponent {T : Tensor3 K V}
    (hne : (universalBorderValues K T).Nonempty) :
    universalExponent K T ≤ universalBorderExponent K T := by
  apply le_csInf hne
  intro x hx
  obtain ⟨n, q, hcert, hq, hn, rfl⟩ := hx
  refine le_trans (universalExponent_le_of_certificate K hcert hq hn) ?_
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hpos : (0 : ℝ) < Tensor.asymptoticRank (Tensor.power T n) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hqpos _)
      (rpow_omega_le_asymptoticRank_power_of_certificate K hq hcert)
  exact universalValue_mono hq hpos (Tensor.asymptoticRank_le_borderRank (Tensor.power T n))

end Soundness

/-! ## Proposition 4.3: one matrix-multiplication tensor without loss of generality -/

section PropositionFourThree

variable (K : Type u) [Field K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- **The certificate produced by copy trading.**  A degeneration of `T^{⊗n}` onto `F` copies of
`⟨q,q,q⟩`, together with an exact algorithm for `⟨a,a,a⟩` using `F^{m+1}` multiplications, is a
universal certificate for `T` of length `(m+1)·n` and side `a·q^{m+1}`.

Proof sketch: raise the degeneration to its `(m+1)`st power, transport the source along
`(T^{⊗n})^{⊗(m+1)} ≅ T^{⊗((m+1)n)}`, and finish with
`Tensor.Restricts.power_matrixMultiplicationCopies_compression`. -/
theorem universalCertificate_of_copies {T : Tensor3 K V} {n F q : ℕ}
    (hdeg : PolynomialDegenerates (Tensor.power T n) (matrixMultiplicationCopies K F q q q))
    {m a : ℕ} (hrank : RankLE (F ^ (m + 1)) (matrixMultiplication (K := K) a a a)) :
    UniversalCertificate K T ((m + 1) * n) (a * q ^ (m + 1)) :=
  ((PolynomialDegenerates.of_restricts
      (Tensor.Isomorphic.power_power T n (m + 1)).symm.restricts).trans
    (hdeg.power (m + 1))).trans
    (PolynomialDegenerates.of_restricts
      (Tensor.Restricts.power_matrixMultiplicationCopies_compression
        (K := K) F q m a hrank))

/-- **Proposition 4.3** ([Alman2019], §4.5), in abstract-budget form.  Suppose the `n`th power of
`T` degenerates to `F` disjoint copies of `⟨q,q,q⟩`, and suppose `B` is a *cost per block*, i.e.
`R̃(T^{⊗(mn)}) ≤ B^m` for every `m ≥ 1`.  Then

`ω_u(T)·log q + log F ≤ log B`,

i.e. the Universal method with a *single* matrix-multiplication tensor already achieves the bound
`log(B/F)/log q` that Schönhage's asymptotic sum inequality extracts from `F` disjoint copies.

Proof sketch (the thesis' argument).  Fix `γ > ω`.  By the definition of `ω` there is, for every
budget `L`, an `a` with `R(⟨a,a,a⟩) ≤ L` and `a ≥ ((L/C)^{1/γ})/2`.  Taking `L = F^m` and trading
the `F^m` copies of `⟨q^m,q^m,q^m⟩` present in the `m`th power of the direct sum for the `F^m`
scalar slots of that algorithm produces a universal certificate of length `mn` and side
`a·q^m`, whose value is at most `m·log B / (log a + m·log q)`.  Since `ω_u` is a lower bound for
every certificate value, this gives, for every `m`,

`m·(ω_u·(log F/γ + log q) − log B) ≤ ω_u·(log C/γ + log 2)`,

and letting `m → ∞` (an Archimedean step, no limits) yields
`ω_u·(log F/γ + log q) ≤ log B`.  Finally `γ` is specialized to `ω_u + δ`, which is legitimate
because soundness gives `ω ≤ ω_u`; letting `δ → 0` removes the correction. -/
theorem universalExponent_mul_log_add_log_le {T : Tensor3 K V} {n q F : ℕ} {B : ℝ}
    (hn : 1 ≤ n) (hq : 2 ≤ q) (hF : 1 ≤ F)
    (hdeg : PolynomialDegenerates (Tensor.power T n) (matrixMultiplicationCopies K F q q q))
    (hbudget : ∀ m : ℕ, 1 ≤ m →
      Tensor.asymptoticRank (Tensor.power T (m * n)) ≤ B ^ m) :
    universalExponent K T * Real.log (q : ℝ) + Real.log (F : ℝ) ≤ Real.log B := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by linarith)
  have hF1 : (1 : ℝ) ≤ (F : ℝ) := by exact_mod_cast hF
  have hFpos : (0 : ℝ) < (F : ℝ) := by linarith
  have hlogF : 0 ≤ Real.log (F : ℝ) := Real.log_nonneg hF1
  -- Certificates produced by copy trading, for every `γ > ω` and every block count `m + 1`.
  have hcerts : ∀ γ : ℝ, omega K < γ → ∃ C : ℝ, 1 ≤ C ∧ ∀ m : ℕ,
      ∃ a : ℕ, 1 ≤ a ∧ UniversalCertificate K T ((m + 1) * n) (a * q ^ (m + 1)) ∧
        (((F ^ (m + 1) : ℕ) : ℝ) / C) ^ γ⁻¹ / 2 < (a : ℝ) := by
    intro γ hγ
    obtain ⟨C, hC, hslot⟩ := exists_rankLE_with_large_side_all_budgets_of_omega_lt K hγ
    refine ⟨C, hC, fun m ↦ ?_⟩
    obtain ⟨a, ha1, harank, halower⟩ := hslot (F ^ (m + 1)) (Nat.one_le_pow (m + 1) F hF)
    exact ⟨a, ha1, universalCertificate_of_copies K hdeg harank, halower⟩
  -- Side lengths of the produced certificates are at least two.
  have hside : ∀ a m : ℕ, 1 ≤ a → 2 ≤ a * q ^ (m + 1) := by
    intro a m ha
    have hpow : 2 ≤ q ^ (m + 1) := le_trans hq (Nat.le_self_pow (Nat.succ_ne_zero m) q)
    calc 2 = 1 * 2 := by ring
      _ ≤ a * q ^ (m + 1) := Nat.mul_le_mul ha hpow
  have hlen : ∀ m : ℕ, 1 ≤ (m + 1) * n := fun m ↦ Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (Nat.succ_ne_zero m) (Nat.one_le_iff_ne_zero.mp hn))
  -- Nonemptiness of the certificate-value set, hence `2 ≤ ω_u`.
  obtain ⟨_C₀, _hC₀, hslot₀⟩ := hcerts 4 (lt_of_le_of_lt (omega_le_three K) (by norm_num))
  obtain ⟨a₀, ha₀, hcert₀, _⟩ := hslot₀ 0
  have hne : (universalValues K T).Nonempty :=
    universalValues_nonempty_of_certificate K hcert₀ (hside a₀ 0 ha₀) (hlen 0)
  have hω : omega K ≤ universalExponent K T := omega_le_universalExponent K hne
  have hωpos : 0 < universalExponent K T :=
    lt_of_lt_of_le (by norm_num) (le_trans (two_le_omega K) hω)
  -- The `γ`-corrected inequality.
  have key : ∀ γ : ℝ, omega K < γ →
      universalExponent K T * (Real.log (F : ℝ) / γ + Real.log (q : ℝ)) ≤ Real.log B := by
    intro γ hγ
    have hγpos : 0 < γ := lt_of_lt_of_le (by norm_num) ((two_le_omega K).trans hγ.le)
    obtain ⟨C, hC, hslot⟩ := hcerts γ hγ
    have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
    have hstep : ∀ m : ℕ,
        ((m : ℝ) + 1) *
            (universalExponent K T * (Real.log (F : ℝ) / γ + Real.log (q : ℝ)) - Real.log B) ≤
          universalExponent K T * (Real.log C / γ + Real.log 2) := by
      intro m
      obtain ⟨a, ha1, hcert, halower⟩ := hslot m
      have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
      have hQ2 : 2 ≤ a * q ^ (m + 1) := hside a m ha1
      have hQ2R : (2 : ℝ) ≤ ((a * q ^ (m + 1) : ℕ) : ℝ) := by exact_mod_cast hQ2
      have hlogQ : 0 < Real.log ((a * q ^ (m + 1) : ℕ) : ℝ) := Real.log_pos (by linarith)
      -- the certificate value bounds `ω_u` from above
      have hvalue := universalExponent_le_of_certificate K hcert hQ2 (hlen m)
      -- positivity and the budget for the powered rank
      have hRpos : (0 : ℝ) < Tensor.asymptoticRank (Tensor.power T ((m + 1) * n)) :=
        lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) (omega K))
          (rpow_omega_le_asymptoticRank_power_of_certificate K hQ2 hcert)
      have hRB := hbudget (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
      have hlogR : Real.log (Tensor.asymptoticRank (Tensor.power T ((m + 1) * n))) ≤
          ((m : ℝ) + 1) * Real.log B := by
        refine le_trans (Real.log_le_log hRpos hRB) ?_
        rw [Real.log_pow]
        push_cast
        exact le_rfl
      have hmain : universalExponent K T * Real.log ((a * q ^ (m + 1) : ℕ) : ℝ) ≤
          ((m : ℝ) + 1) * Real.log B := by
        refine le_trans ?_ hlogR
        rw [← le_div_iff₀ hlogQ] at *
        exact hvalue
      -- expand `log (a * q^{m+1})`
      have hlogsplit : Real.log ((a * q ^ (m + 1) : ℕ) : ℝ) =
          Real.log (a : ℝ) + ((m : ℝ) + 1) * Real.log (q : ℝ) := by
        have hcast : ((a * q ^ (m + 1) : ℕ) : ℝ) = (a : ℝ) * (q : ℝ) ^ (m + 1) := by push_cast; ring
        rw [hcast, Real.log_mul (by linarith) (by positivity), Real.log_pow]
        push_cast
        ring
      -- lower bound for `log a`
      have hloga : ((m : ℝ) + 1) * (Real.log (F : ℝ) / γ) - Real.log C / γ - Real.log 2 ≤
          Real.log (a : ℝ) := by
        have hz : (0 : ℝ) < ((F : ℝ) ^ (m + 1)) / C := by positivity
        have hcast : (((F ^ (m + 1) : ℕ) : ℝ) / C) = ((F : ℝ) ^ (m + 1)) / C := by push_cast; ring
        rw [hcast] at halower
        have hsmall : (0 : ℝ) < (((F : ℝ) ^ (m + 1)) / C) ^ γ⁻¹ / 2 := by positivity
        have hlog := Real.log_le_log hsmall halower.le
        rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hz,
          Real.log_div (by positivity) (ne_of_gt hCpos), Real.log_pow] at hlog
        refine le_trans (le_of_eq ?_) hlog
        field_simp
        push_cast
        ring
      -- assemble
      have hexpand : universalExponent K T *
          ((((m : ℝ) + 1) * (Real.log (F : ℝ) / γ) - Real.log C / γ - Real.log 2) +
            ((m : ℝ) + 1) * Real.log (q : ℝ)) ≤
          universalExponent K T * Real.log ((a * q ^ (m + 1) : ℕ) : ℝ) := by
        rw [hlogsplit]
        exact mul_le_mul_of_nonneg_left (by linarith) hωpos.le
      nlinarith [hexpand, hmain]
    -- Archimedean removal of the additive constant.
    by_contra hcon
    rw [not_le] at hcon
    set X : ℝ :=
      universalExponent K T * (Real.log (F : ℝ) / γ + Real.log (q : ℝ)) - Real.log B with hX
    have hXpos : 0 < X := by rw [hX]; linarith
    obtain ⟨m, hm⟩ :=
      exists_nat_gt ((universalExponent K T * (Real.log C / γ + Real.log 2)) / X)
    have hlt : universalExponent K T * (Real.log C / γ + Real.log 2) < (m : ℝ) * X :=
      (div_lt_iff₀ hXpos).mp hm
    have hcontr := hstep m
    linarith
  -- Specialize `γ = ω_u + δ` and let `δ → 0`.
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set δ : ℝ := ε * universalExponent K T / (Real.log (F : ℝ) + 1) with hδ
  have hlogF1 : (0 : ℝ) < Real.log (F : ℝ) + 1 := by linarith
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hden : 0 < universalExponent K T + δ := by linarith
  have h1 := key (universalExponent K T + δ) (by linarith)
  have heq : Real.log (F : ℝ) -
      universalExponent K T * (Real.log (F : ℝ) / (universalExponent K T + δ)) =
      Real.log (F : ℝ) * δ / (universalExponent K T + δ) := by
    field_simp
    ring
  have hcmp : Real.log (F : ℝ) * δ / (universalExponent K T + δ) ≤
      Real.log (F : ℝ) * δ / universalExponent K T := by
    apply div_le_div_of_nonneg_left (by positivity) hωpos (by linarith)
  have hδeq : Real.log (F : ℝ) * δ / universalExponent K T =
      Real.log (F : ℝ) * ε / (Real.log (F : ℝ) + 1) := by
    rw [hδ]
    field_simp
  have hδle : Real.log (F : ℝ) * ε / (Real.log (F : ℝ) + 1) ≤ ε := by
    rw [div_le_iff₀ hlogF1]
    nlinarith [hlogF, hε.le]
  nlinarith [h1, heq, hcmp, hδeq, hδle]

/-- **Proposition 4.3** ([Alman2019]) in the shape printed in the thesis: if `R̃(T) ≤ r` and the
`n`th power of `T` degenerates to `F` disjoint copies of `⟨q,q,q⟩`, then

`ω_u(T) ≤ log(r^n / F) / log q`.

Proof sketch: for `ρ > r` the strict multiplicativity bound `Tensor.asymptoticRank_power_le_pow_of_lt`
turns `R̃(T) ≤ r < ρ` into the block budget `R̃(T^{⊗(mn)}) ≤ (ρ^n)^m`, so
`universalExponent_mul_log_add_log_le` applies with `B = ρ^n`.  Choosing `ρ = r·exp(ε/n)` makes
`n·log ρ = n·log r + ε`, and `ε` is arbitrary. -/
theorem universalExponent_le_of_copies_of_asymptoticRank_le
    {T : Tensor3 K V} {n q F : ℕ} {r : ℝ}
    (hn : 1 ≤ n) (hq : 2 ≤ q) (hF : 1 ≤ F) (hr : 0 < r)
    (hR : Tensor.asymptoticRank T ≤ r)
    (hdeg : PolynomialDegenerates (Tensor.power T n) (matrixMultiplicationCopies K F q q q)) :
    universalExponent K T ≤ ((n : ℝ) * Real.log r - Real.log (F : ℝ)) / Real.log (q : ℝ) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by linarith)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmain : universalExponent K T * Real.log (q : ℝ) + Real.log (F : ℝ) ≤
      (n : ℝ) * Real.log r := by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    set ρ : ℝ := r * Real.exp (ε / (n : ℝ)) with hρ
    have hρr : r < ρ := by
      rw [hρ]
      nlinarith [Real.add_one_le_exp (ε / (n : ℝ)), div_pos hε hnR, hr]
    have hρpos : 0 < ρ := lt_trans hr hρr
    have hbudget : ∀ m : ℕ, 1 ≤ m →
        Tensor.asymptoticRank (Tensor.power T (m * n)) ≤ (ρ ^ n) ^ m := by
      intro m _
      have := Tensor.asymptoticRank_power_le_pow_of_lt (lt_of_le_of_lt hR hρr) (m * n)
      calc Tensor.asymptoticRank (Tensor.power T (m * n)) ≤ ρ ^ (m * n) := this
        _ = (ρ ^ n) ^ m := by rw [pow_mul']
    have h := universalExponent_mul_log_add_log_le K hn hq hF hdeg hbudget
    have hlogρ : Real.log (ρ ^ n) = (n : ℝ) * Real.log r + ε := by
      rw [Real.log_pow, hρ, Real.log_mul (ne_of_gt hr) (Real.exp_ne_zero _), Real.log_exp]
      field_simp
    rw [hlogρ] at h
    linarith
  rw [le_div_iff₀ hlogq]
  linarith

end PropositionFourThree

/-! ## Comparison with the Galactic method -/

section SquareGalactic

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- The **square** galactic certificate values of `T`: the subfamily of `galacticValues` whose
target is a disjoint sum of copies of a *square* matrix-multiplication tensor `⟨q,q,q⟩`.

[Alman2019] defines `ω_g` with exactly this subfamily, whereas the `GalacticCertificate` of
`MatrixMultiplication/GalacticMethod.lean` follows AVW and admits rectangular targets.  The
distinction matters: only the square subfamily is dominated by `ω_u`. -/
def squareGalacticValues (T : Tensor3 K V) : Set ℝ :=
  {x | ∃ n q F : ℕ, GalacticCertificate K T n q q q F ∧ 2 ≤ q ∧ 1 ≤ F ∧ 1 ≤ n ∧
    x = galacticValue q q q F (Tensor.borderRank (Tensor.power T n))}

/-- **The square galactic exponent** ([Alman2019], §4.5.1): the infimum of the values of the
square galactic certificates of `T`. -/
noncomputable def squareGalacticExponent (T : Tensor3 K V) : ℝ :=
  sInf (squareGalacticValues K T)

/-- Every square galactic certificate value is a galactic certificate value. -/
theorem squareGalacticValues_subset_galacticValues (T : Tensor3 K V) :
    squareGalacticValues K T ⊆ galacticValues K T := by
  rintro x ⟨n, q, F, hcert, hq, hF, _, rfl⟩
  have h1 : 1 ≤ q := le_trans (by norm_num) hq
  have hvol : 2 ≤ q * q * q := by nlinarith
  exact ⟨n, q, q, q, F, hcert, hvol, hF, rfl⟩

end SquareGalactic

section SquareGalacticField

variable (K : Type u) [Field K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- **The Galactic method is subsumed by the Universal method for square targets**
([Alman2019], §4.5.1, via Proposition 4.3).  A galactic certificate `(n, q, q, q, F)` for `T`
forces `ω_u(T) ≤ 3·(log R̲(T^{⊗n}) − log F) / log(q³)`, the very value the Galactic method
extracts from it.

Proof sketch: a galactic certificate is a polynomial degeneration onto `F ⊙ ⟨q,q,q⟩`, and
`R̃(T^{⊗mn}) = R̃((T^{⊗n})^{⊗m}) ≤ R̲((T^{⊗n})^{⊗m}) ≤ R̲(T^{⊗n})^m` is an admissible block
budget, so Proposition 4.3 (`universalExponent_mul_log_add_log_le`) applies with
`B = R̲(T^{⊗n})`.  Finally `log(q³) = 3·log q`. -/
theorem universalExponent_le_galacticValue_of_square_certificate {T : Tensor3 K V} {n q F : ℕ}
    (hcert : GalacticCertificate K T n q q q F) (hq : 2 ≤ q) (hF : 1 ≤ F) (hn : 1 ≤ n) :
    universalExponent K T ≤
      galacticValue q q q F (Tensor.borderRank (Tensor.power T n)) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by linarith)
  have hbudget : ∀ m : ℕ, 1 ≤ m →
      Tensor.asymptoticRank (Tensor.power T (m * n)) ≤
        ((Tensor.borderRank (Tensor.power T n) : ℕ) : ℝ) ^ m := by
    intro m _
    have hiso : Tensor.asymptoticRank (Tensor.power T (m * n)) =
        Tensor.asymptoticRank (Tensor.power (Tensor.power T n) m) :=
      (Tensor.asymptoticRank_isomorphic (Tensor.Isomorphic.power_power T n m)).symm
    rw [hiso]
    refine le_trans (Tensor.asymptoticRank_le_borderRank _) ?_
    have hb := Tensor.borderRank_power_le (Tensor.power T n) m
    exact_mod_cast hb
  have h := universalExponent_mul_log_add_log_le K hn hq hF
    hcert.polynomialDegenerates hbudget
  have hcube : (((q * q * q : ℕ)) : ℝ) = (q : ℝ) ^ (3 : ℕ) := by push_cast; ring
  have hlog3 : Real.log (((q * q * q : ℕ)) : ℝ) = 3 * Real.log (q : ℝ) := by
    rw [hcube, Real.log_pow]
    norm_num
  unfold galacticValue
  rw [hlog3, le_div_iff₀ (by linarith)]
  linarith

/-- **The chain `ω ≤ ω_u ≤ ω_g^{square}`.**  The Universal method never proves a worse bound than
the square Galactic method. -/
theorem universalExponent_le_squareGalacticExponent {T : Tensor3 K V}
    (hne : (squareGalacticValues K T).Nonempty) :
    universalExponent K T ≤ squareGalacticExponent K T := by
  refine le_csInf hne ?_
  rintro x ⟨n, q, F, hcert, hq, hF, hn, rfl⟩
  exact universalExponent_le_galacticValue_of_square_certificate K hcert hq hF hn

/-- Restricting the Galactic method to square targets can only raise its exponent:
`ω_g(T) ≤ ω_g^{square}(T)`. -/
theorem galacticExponent_le_squareGalacticExponent {T : Tensor3 K V}
    (hne : (squareGalacticValues K T).Nonempty) :
    galacticExponent K T ≤ squareGalacticExponent K T :=
  le_csInf hne fun _ hx ↦
    csInf_le (galacticValues_bddBelow K T) (squareGalacticValues_subset_galacticValues K T hx)

end SquareGalacticField

/-! ## Theorem 5.1 and Corollary 5.2: the asymptotic-slice-rank barrier

Chapter 5 of [Alman2019] bounds `ω_u(T)` *from below* by combining two facts about a
degeneration-monotone, submultiplicative tensor measure `S̃` (asymptotic slice rank): `S̃` cannot
increase under degeneration, and `S̃(⟨q,q,q⟩) = q²`.  Neither fact is available in this
repository yet, so both are taken as hypotheses; the resulting statements are strictly more
general than the slice-rank instance and are the intended library form. -/

section Barrier

variable (K : Type u) [Field K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- **Theorem 5.1** ([Alman2019], §5.2).  Let `R` be a geometric lower bound for the asymptotic
ranks of the powers of `T` (think `R = R̃(T)`), and let `S > 1` be such that every universal
certificate `(n,q)` of `T` satisfies `q² ≤ S^n` (think: `S = S̃(T)`, with `q² = S̃(⟨q,q,q⟩)`
bounded by `S̃(T^{⊗n}) ≤ S̃(T)^n` because degenerations cannot increase asymptotic slice rank).
Then

`ω_u(T) ≥ 2·log R / log S`.

Proof sketch: for every `δ > 0` there is a certificate `(n,q)` whose value
`log R̃(T^{⊗n}) / log q` is below `ω_u + δ`.  Then `n·log R ≤ log R̃(T^{⊗n}) < (ω_u+δ)·log q`,
while `q² ≤ S^n` gives `2·log q ≤ n·log S`.  Combining and cancelling the positive factor `n`
gives `2·log R < (ω_u+δ)·log S`, and `δ` is arbitrary. -/
theorem two_mul_log_div_log_le_universalExponent {T : Tensor3 K V} {R S : ℝ}
    (hne : (universalValues K T).Nonempty) (hR : 0 < R) (hS : 1 < S)
    (hRle : ∀ n : ℕ, 1 ≤ n → R ^ n ≤ Tensor.asymptoticRank (Tensor.power T n))
    (hSle : ∀ n q : ℕ, 1 ≤ n → 2 ≤ q → UniversalCertificate K T n q →
      (q : ℝ) ^ 2 ≤ S ^ n) :
    2 * Real.log R / Real.log S ≤ universalExponent K T := by
  have hlogS : 0 < Real.log S := Real.log_pos hS
  rw [div_le_iff₀ hlogS]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set δ : ℝ := ε / Real.log S with hδ
  have hδpos : 0 < δ := div_pos hε hlogS
  have hδS : δ * Real.log S = ε := by
    rw [hδ]
    field_simp
  obtain ⟨x, hx, hxlt⟩ := exists_lt_of_csInf_lt hne
    (show sInf (universalValues K T) < universalExponent K T + δ by
      unfold universalExponent; linarith)
  obtain ⟨n, q, hcert, hq, hn, rfl⟩ := hx
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by linarith)
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hωδ : 0 < universalExponent K T + δ := by
    have h2 := two_le_universalExponent K hne
    linarith
  have hlogRn : (n : ℝ) * Real.log R ≤
      Real.log (Tensor.asymptoticRank (Tensor.power T n)) := by
    have hpos : (0 : ℝ) < R ^ n := pow_pos hR n
    have hle := Real.log_le_log hpos (hRle n hn)
    rwa [Real.log_pow] at hle
  have hval : Real.log (Tensor.asymptoticRank (Tensor.power T n)) <
      (universalExponent K T + δ) * Real.log (q : ℝ) := by
    have := hxlt
    unfold universalValue at this
    exact (div_lt_iff₀ hlogq).mp this
  have hlogSq : 2 * Real.log (q : ℝ) ≤ (n : ℝ) * Real.log S := by
    have hpos : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
    have hle := Real.log_le_log hpos (hSle n q hn hq hcert)
    rw [Real.log_pow, Real.log_pow] at hle
    exact_mod_cast hle
  have step1 : 2 * ((n : ℝ) * Real.log R) <
      (universalExponent K T + δ) * (2 * Real.log (q : ℝ)) := by linarith
  have step2 : (universalExponent K T + δ) * (2 * Real.log (q : ℝ)) ≤
      (universalExponent K T + δ) * ((n : ℝ) * Real.log S) :=
    mul_le_mul_of_nonneg_left hlogSq hωδ.le
  have step3 : (n : ℝ) * (2 * Real.log R) <
      (n : ℝ) * ((universalExponent K T + δ) * Real.log S) := by nlinarith [step1, step2]
  have step4 : 2 * Real.log R < (universalExponent K T + δ) * Real.log S :=
    lt_of_mul_lt_mul_left step3 hnpos.le
  nlinarith [step4, hδS]

/-- **Theorem 5.1, abstract-measure form.**  This is the shape a future
`Tensor/AsymptoticSliceRank.lean` instantiates: `fPower n` stands for `S̃(T^{⊗n})` and `fMM q`
for `S̃(⟨q,q,q⟩)`, `hmono` is degeneration monotonicity of `S̃`, `hsub` is the submultiplicative
bound `S̃(T^{⊗n}) ≤ S^n`, and `hmm` is `q² ≤ S̃(⟨q,q,q⟩)`. -/
theorem two_mul_log_div_log_le_universalExponent_of_measure {T : Tensor3 K V} {R S : ℝ}
    (fPower fMM : ℕ → ℝ)
    (hne : (universalValues K T).Nonempty) (hR : 0 < R) (hS : 1 < S)
    (hRle : ∀ n : ℕ, 1 ≤ n → R ^ n ≤ Tensor.asymptoticRank (Tensor.power T n))
    (hmono : ∀ n q : ℕ, UniversalCertificate K T n q → fMM q ≤ fPower n)
    (hsub : ∀ n : ℕ, fPower n ≤ S ^ n)
    (hmm : ∀ q : ℕ, (q : ℝ) ^ 2 ≤ fMM q) :
    2 * Real.log R / Real.log S ≤ universalExponent K T :=
  two_mul_log_div_log_le_universalExponent K hne hR hS hRle
    fun n q _ _ hcert ↦ le_trans (hmm q) (le_trans (hmono n q hcert) (hsub n))

/-- **Theorem 5.1 with `R = R̃(T)`**, the form printed in [Alman2019]:
`ω_u(T) ≥ 2·log R̃(T) / log S̃(T)`.  The hypothesis `hone` is the nondegeneracy condition under
which `R̃(T)^n ≤ R̃(T^{⊗n})` is available. -/
theorem two_mul_log_asymptoticRank_div_log_le_universalExponent {T : Tensor3 K V} {S : ℝ}
    (hne : (universalValues K T).Nonempty) (hS : 1 < S)
    (hone : ∀ m : ℕ, 1 ≤ Tensor.rank (Tensor.power T m))
    (hRpos : 0 < Tensor.asymptoticRank T)
    (hSle : ∀ n q : ℕ, 1 ≤ n → 2 ≤ q → UniversalCertificate K T n q →
      (q : ℝ) ^ 2 ≤ S ^ n) :
    2 * Real.log (Tensor.asymptoticRank T) / Real.log S ≤ universalExponent K T :=
  two_mul_log_div_log_le_universalExponent K hne hRpos hS
    (fun n _ ↦ Tensor.asymptoticRank_pow_le_asymptoticRank_power T hone n) hSle

/-- **Corollary 5.2** ([Alman2019], §5.2).  If the slice-rank-like measure `S` is at most `R^s`,
then `ω_u(T) ≥ 2/s`.  The interesting range is `s < 1`, where the bound is strictly above `2`
(`two_lt_universalExponent`); the statement itself needs only `s > 0`.

Proof sketch: `log S ≤ s·log R` with `log S > 0` and `s > 0` forces `log R > 0`, and then
`2·log R / log S ≥ 2·log R / (s·log R) = 2/s`; conclude by Theorem 5.1. -/
theorem two_div_le_universalExponent {T : Tensor3 K V} {R S s : ℝ}
    (hne : (universalValues K T).Nonempty) (hR : 0 < R) (hS : 1 < S)
    (hs : 0 < s) (hSR : S ≤ R ^ s)
    (hRle : ∀ n : ℕ, 1 ≤ n → R ^ n ≤ Tensor.asymptoticRank (Tensor.power T n))
    (hSle : ∀ n q : ℕ, 1 ≤ n → 2 ≤ q → UniversalCertificate K T n q →
      (q : ℝ) ^ 2 ≤ S ^ n) :
    2 / s ≤ universalExponent K T := by
  have hlogS : 0 < Real.log S := Real.log_pos hS
  have hlogSR : Real.log S ≤ s * Real.log R := by
    have hle := Real.log_le_log (by linarith) hSR
    rwa [Real.log_rpow hR] at hle
  have hlogR : 0 < Real.log R := by
    by_contra hcon
    rw [not_lt] at hcon
    have hprod : s * Real.log R ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs.le hcon
    linarith
  have hmain := two_mul_log_div_log_le_universalExponent K hne hR hS hRle hSle
  have hcmp : 2 / s ≤ 2 * Real.log R / Real.log S := by
    rw [div_le_div_iff₀ hs hlogS]
    nlinarith
  linarith

/-- **Corollary 5.2, final form** ([Alman2019], §5.2): a slice-rank-like measure that is a
strictly sublinear power of the rank-like measure, `S ≤ R^s` with `0 < s < 1`, forces
`ω_u(T) ≥ 2/s > 2`.  No such tensor can prove `ω = 2` by the Universal method.

Compare `six_div_add_two_le_coordinateGalacticExponent_of_concise`
(`MatrixMultiplication/IndependenceBarrier.lean`), the AVW barrier with the weaker constant
`6/(s+2)`; for `s < 1` one has `2/s > 6/(s+2)`. -/
theorem two_lt_universalExponent {T : Tensor3 K V} {R S s : ℝ}
    (hne : (universalValues K T).Nonempty) (hR : 0 < R) (hS : 1 < S)
    (hs : 0 < s) (hs1 : s < 1) (hSR : S ≤ R ^ s)
    (hRle : ∀ n : ℕ, 1 ≤ n → R ^ n ≤ Tensor.asymptoticRank (Tensor.power T n))
    (hSle : ∀ n q : ℕ, 1 ≤ n → 2 ≤ q → UniversalCertificate K T n q →
      (q : ℝ) ^ 2 ≤ S ^ n) :
    2 < universalExponent K T := by
  have h := two_div_le_universalExponent K hne hR hS hs hSR hRle hSle
  have hlt : (2 : ℝ) < 2 / s := by
    rw [lt_div_iff₀ hs]
    linarith
  linarith

/-- **Corollary 5.2, first half.**  If the Universal method applied to `T` could reach the
optimal exponent `ω_u(T) ≤ 2`, then the slice-rank-like upper bound `S` must be at least the
rank-like lower bound `R`. -/
theorem le_of_universalExponent_le_two {T : Tensor3 K V} {R S : ℝ}
    (hne : (universalValues K T).Nonempty) (hR : 0 < R) (hS : 1 < S)
    (hRle : ∀ n : ℕ, 1 ≤ n → R ^ n ≤ Tensor.asymptoticRank (Tensor.power T n))
    (hSle : ∀ n q : ℕ, 1 ≤ n → 2 ≤ q → UniversalCertificate K T n q →
      (q : ℝ) ^ 2 ≤ S ^ n)
    (hle : universalExponent K T ≤ 2) : R ≤ S := by
  have hlogS : 0 < Real.log S := Real.log_pos hS
  have hmain := two_mul_log_div_log_le_universalExponent K hne hR hS hRle hSle
  rw [div_le_iff₀ hlogS] at hmain
  have hlogRS : Real.log R ≤ Real.log S := by nlinarith
  exact (Real.log_le_log_iff hR (by linarith)).mp hlogRS

end Barrier

/-! ## The trivial certificate, and the Strassen regression instance

The deliberately tiny client required by `DESIGN.md`: `⟨q,q,q⟩` is its own universal certificate,
so `ω_u(⟨q,q,q⟩) ≤ log R̃(⟨q,q,q⟩)/log q`, and chaining that with soundness reproduces Strassen's
classical bound.  This is the direction-of-inequality check for the whole module: a certificate is
an upper bound on `ω_u`, and `ω_u` is an upper bound on `ω`. -/

section TrivialCertificate

variable (K : Type u) [CommSemiring K]

/-- **The trivial universal certificate.**  A square matrix-multiplication tensor is a
(degree-zero) polynomial degeneration of its own first tensor power. -/
theorem universalCertificate_matrixMultiplication (q : ℕ) :
    UniversalCertificate K (matrixMultiplication (K := K) q q q) 1 q := by
  have hone : Isomorphic (Tensor.power (matrixMultiplication (K := K) q q q) 1)
      (matrixMultiplication (K := K) q q q) := by
    rw [Tensor.power_one_eq_powerOne]
    exact (Tensor.Isomorphic.powerOneTransport _).symm
  exact PolynomialDegenerates.of_restricts hone.restricts

end TrivialCertificate

section TrivialCertificateField

variable (K : Type u) [Field K]

/-- `⟨q,q,q⟩` always has the trivial certificate, so its value set is nonempty and `ω_u` is a
genuine infimum. -/
theorem universalValues_matrixMultiplication_nonempty {q : ℕ} (hq : 2 ≤ q) :
    (universalValues K (matrixMultiplication (K := K) q q q)).Nonempty :=
  universalValues_nonempty_of_certificate K
    (universalCertificate_matrixMultiplication K q) hq le_rfl

/-- **The value of the trivial certificate**: `ω_u(⟨q,q,q⟩) ≤ log R̃(⟨q,q,q⟩) / log q`. -/
theorem universalExponent_matrixMultiplication_le {q : ℕ} (hq : 2 ≤ q) :
    universalExponent K (matrixMultiplication (K := K) q q q) ≤
      Real.log (Tensor.asymptoticRank (matrixMultiplication (K := K) q q q)) /
        Real.log (q : ℝ) := by
  have hiso : Tensor.asymptoticRank (Tensor.power (matrixMultiplication (K := K) q q q) 1) =
      Tensor.asymptoticRank (matrixMultiplication (K := K) q q q) := by
    rw [Tensor.power_one_eq_powerOne]
    exact Tensor.asymptoticRank_isomorphic (Tensor.Isomorphic.powerOneTransport _).symm
  have h := universalExponent_le_of_certificate K
    (universalCertificate_matrixMultiplication K q) hq le_rfl
  unfold universalValue at h
  rwa [hiso] at h

/-- **Strassen's instance, upper half**, through the universal exponent: a border-rank-seven
certificate for `⟨2,2,2⟩` gives `ω_u(⟨2,2,2⟩) ≤ log 7 / log 2 = log₂ 7`.

Proof sketch: the trivial certificate has side `2`, so its value is `log R̃(⟨2,2,2⟩)/log 2`, and
`R̃ ≤ R̲ ≤ 7`. -/
theorem universalExponent_matrixMultiplication_two_le
    (h7 : BorderRankLE 7 (matrixMultiplication (K := K) 2 2 2)) :
    universalExponent K (matrixMultiplication (K := K) 2 2 2) ≤ Real.log 7 / Real.log 2 := by
  have hbr : Tensor.asymptoticRank (matrixMultiplication (K := K) 2 2 2) ≤ 7 := by
    refine le_trans (Tensor.asymptoticRank_le_borderRank _) ?_
    exact_mod_cast borderRank_le_iff.mpr h7
  have hnn : 0 ≤ Tensor.asymptoticRank (matrixMultiplication (K := K) 2 2 2) :=
    Tensor.asymptoticRank_nonneg _
  have hlog : Real.log (Tensor.asymptoticRank (matrixMultiplication (K := K) 2 2 2)) ≤
      Real.log 7 := by
    rcases eq_or_lt_of_le hnn with h0 | h0
    · rw [← h0]
      simpa using Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 7)
    · exact Real.log_le_log h0 hbr
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine le_trans (universalExponent_matrixMultiplication_le K (by norm_num)) ?_
  rw [show (((2 : ℕ) : ℝ)) = 2 by norm_num, div_le_div_iff₀ hlog2 hlog2]
  nlinarith [hlog, hlog2]

/-- **Direction-of-inequality regression test.**  Chaining soundness with the trivial certificate
reproduces Strassen's classical bound through the universal exponent:
`ω ≤ ω_u(⟨2,2,2⟩) ≤ log₂ 7`.  Compare `omega_le_log_two_seven_of_borderRankLE`, which routes the
same certificate through the Galactic exponent. -/
theorem omega_le_log_two_seven_of_borderRankLE_universal
    (h7 : BorderRankLE 7 (matrixMultiplication (K := K) 2 2 2)) :
    omega K ≤ Real.log 7 / Real.log 2 :=
  le_trans
    (omega_le_universalExponent K
      (universalValues_matrixMultiplication_nonempty K (by norm_num)))
    (universalExponent_matrixMultiplication_two_le K h7)

end TrivialCertificateField

end AlgebraicComplexity
