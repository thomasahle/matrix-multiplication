/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.GalacticMethod
import AlgebraicComplexity.MatrixMultiplication.IndependentDiagonal

/-!
# The independence-number barrier (AVW Theorem 4.1 and Corollary 4.3)

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  This module is milestone **F** of
`BARRIER_FRAMEWORK.md`: the inequality that turns an upper bound on the asymptotic independence
number of a tensor into a lower bound on the exponent the Galactic method can prove with it,

> J. Alman and V. Vassilevska Williams, *Limits on All Known (and Some Unknown) Approaches to
> Matrix Multiplication*, arXiv:1810.08671v1, **Theorem 4.1** and **Corollary 4.3**.

## The statement, and the exponent it is about

AVW's Theorem 4.1 reads `Ī(T) ≥ R̃(T)^{6/ω_g(T) − 2}` for concise `T`.  Every quantity in it is
read off a *coefficient table*: `Ī` is basis-dependent
(`Tensor.HadamardWitness.independenceNumber_not_isomorphism_invariant`), and `F_{T,n,a,b,c}` counts
monomial degenerations of `T^{⊗n}` in the variables of `T`.  The exponent in the statement is
therefore **not** `AlgebraicComplexity.galacticExponent`, which
`MatrixMultiplication/GalacticMethod.lean` defines as an infimum over *all* coordinate
presentations of `T^{⊗n}`.  This module introduces the coefficient-level notion the theorem is
about:

* `CoordinateGalacticCertificate K T n a b c F` --- `ℕ`-valued weights and a threshold on the words
  of `T^{⊗n}` whose minimum-weight part **is** the block table of `F` disjoint copies of
  `⟨a,b,c⟩`, embedded in the words by legwise injections and extended by zero;
* `coordinateGalacticExponent` and `coordinateGalacticAsymptoticExponent`, the infima of the
  corresponding certificate values, measured with the border rank and with the asymptotic rank of
  the power respectively.

`galacticExponent_le_coordinateGalacticExponent` is the exact comparison: every coordinate
certificate is a galactic certificate of the tensor `T` defines, so
`ω ≤ ω_g(T) ≤ ω_g^{coord}(T)`.  The reverse inequality is not available and should not be
expected --- this is a **recorded correction** to the reading of AVW Section 4, whose statements
conflate the two.  (`GalacticMethod.lean` was correspondingly relaxed, so that its target
condition is a *restriction* onto the direct sum rather than an isomorphism: a monomial
degeneration keeps the variables of its source, so its target carries variables it no longer
uses.)

## Principal results

* `CoordinateGalacticCertificate.le_asymptoticIndependenceNumber_pow` --- **certificates feed `Ī`**:
  a certificate `(n,a,b,c,F)` forces `F · abc/max{a,b,c} ≤ Ī(T)^n`.  This is the only route from a
  monomial degeneration to `Ī`: the power law of `Ī`, Corollary 4.2
  (`Tensor.asymptoticIndependenceNumber_minimumWeightPart_le`) and Lemma 4.4
  (`asymptoticIndependenceNumber_mmCoefficients_copies`).
* `CoordinateGalacticCertificate.card_le` --- the variable count `F·ab ≤ |X|^n` and its two
  companions, from injectivity of the certificate's embeddings.
* `CoordinateGalacticCertificate.sq_le_asymptoticIndependenceNumber_pow` (plan item **M1**) --- the
  balanced case `a = b = c` of the previous item, `F·a² ≤ Ī(T)^n`.
* `coordinateGalacticCertificate_of_zeroOut` and
  `sq_le_asymptoticIndependenceNumber_pow_of_zeroOut` (plan item **M2**) --- an explicit *zeroing
  out* of `T^{⊗n}` onto `F` embedded copies of `⟨a,b,c⟩` is a coordinate galactic certificate, via
  indicator weights and threshold `0`.
* `coordinateGalacticCertificate_of_pivot_bijection` --- the packaged form every barrier client
  uses: zeroing `T` to one `X` variable and a bijectively matched pair of `Y`/`Z` variable sets
  gives a `(1,1,1,|A_Y|,1)` certificate, hence a nonempty certificate value set.
* `CoordinateGalacticCertificate.of_coordinateZeroOut` --- **a certificate for a zeroing out of
  `T` is a certificate for `T`**, so a laser extraction may be run on a simplified table and its
  certificate read on the original one.
* `le_asymptoticIndependenceNumber_rpow_of_certificate` --- **the barrier for one certificate**:
  `R^{6/x − 2} ≤ Ī(T)` for a certificate of value `x`, whenever `R ≥ 1` bounds the leg dimensions
  and `R^n` is at most the rank measure of the power.
* `rpow_coordinateGalacticAsymptoticExponent_le_asymptoticIndependenceNumber` and its border-rank
  companion --- **Theorem 4.1**, after the `ε`-and-limit passage to the infimum.
* `six_div_add_two_le_coordinateGalacticExponent` and
  `two_lt_coordinateGalacticExponent_of_le_rpow` --- **Corollary 4.3 in the explicit form the
  framework mandates**: for each `s < 1` the constant is `w = 6/(s+2)`, and `2 < w`
  (`two_lt_six_div_add_two`).  No limiting argument is needed for this form, which is why it, and
  not Theorem 4.1, is the interface for the later sections.
* `..._of_concise` versions of all of the above, in which conciseness supplies `R = R̃(T)`, and
  `asymptoticIndependenceNumber_eq_asymptoticRank_of_coordinateGalacticExponent_eq_two`, the first
  sentence of Corollary 4.3.

## Where conciseness enters

Exactly once, to bound the leg dimensions: `Tensor.card_le_asymptoticRank` proves
`|κ i| ≤ R̃(T)` for a table that is concise on leg `i`.  Since the basis-free flattening bound of
`Tensor/Concise.lean` applies to a *single* tensor, and the bound is needed for every Kronecker
power, the coordinate form of the predicate is used instead (`Tensor.IsCoordinateConcise`, the
slices in the direction of a leg span that leg), for which stability under Kronecker products is
the statement that pointwise products of two spanning families of functions span
(`Tensor.span_image2_mulPair`).  The comparison with the basis-free `Tensor.IsConcise` is not
needed and is not proved.

The second use of `R̃` is `Tensor.asymptoticRank_pow_le_asymptoticRank_power`,
`R̃(T)^n ≤ R̃(T^{⊗n})` --- the half of AVW's `R̃(T^{⊗n}) = R̃(T)^n` that follows from the
infimum characterization of asymptotic rank, the other half needing a multiplicativity statement
this repository does not have.

## Position in the library, and lemmas awaiting promotion

Layer 3.  It imports `MatrixMultiplication/GalacticMethod.lean` (the certificate calculus and
soundness) and `MatrixMultiplication/IndependentDiagonal.lean` (Lemma 4.2, Lemma 4.4 and the
coefficient table of `⟨m,n,p⟩`).  The coordinate certificate is defined here rather than in
`GalacticMethod.lean` only because it mentions `mmCoefficients`, which lives in
`IndependentDiagonal.lean`; it belongs next to `GalacticCertificate`.

The layer-1 statements this module used to carry now live in their proper homes:
`Tensor.Restricts.coordinateTensor_coordinateDirectSum` and the coordinate-conciseness calculus in
`Tensor/IndependenceNumber.lean` (which owns `coordinateTensor`, `coordinatePower` and
`coordinateRelabel`), `Tensor.IsCoordinateConcise` itself in `Tensor/Concise.lean`,
`Tensor.MonomialIndependence.minimumWeightPart_coordinateRelabel` in
`Tensor/MonomialIndependence.lean`, and
`Tensor.asymptoticRank_pow_le_asymptoticRank_power` in `Tensor/AsymptoticRank.lean`.

## Non-goals

* No lower bound on `AlgebraicComplexity.galacticExponent` is claimed; see above.
* `R̃(T^{⊗n}) = R̃(T)^n` is used only in the direction proved.
* Nothing here evaluates `Ī` for a named tensor; the Section 5 partitioning tools that produce the
  hypothesis `Ī(T) ≤ R̃(T)^s` are milestones G--J of `BARRIER_FRAMEWORK.md`.
-/

namespace AlgebraicComplexity

open Tensor
open scoped DirectSum

universe u v w

/-! ## Coordinate galactic certificates

`MatrixMultiplication/GalacticMethod.lean` defines a galactic certificate for an *abstract* tensor:
some coordinate presentation of `T^{⊗n}` monomially degenerates onto `F` disjoint copies of
`⟨a,b,c⟩`.  The presentation there is an arbitrary legwise isomorphism, so `galacticExponent` is an
infimum over *all* bases.

That is not the quantity AVW's Section 4 bounds.  The independence number is basis-dependent
(`Tensor.HadamardWitness.independenceNumber_not_isomorphism_invariant`), so a bound on `Ī(T)` for
one coefficient table can say nothing about degenerations read in another basis.  AVW's
`F_{T,n,a,b,c}` counts monomial degenerations of `T^{⊗n}` *in the variables of `T`*, and
`CoordinateGalacticCertificate` is exactly that: `ℕ`-valued weights and a threshold on the words of
`T^{⊗n}` whose minimum-weight part **is** the table of `F` disjoint copies of `⟨a,b,c⟩`, extended
by zero to the words that no longer occur.

The two exponents are compared by `galacticExponent_le_coordinateGalacticExponent`: every
coordinate certificate is an abstract certificate, so `ω ≤ ω_g(T) ≤ ω_g^{coord}(T)`.  The reverse
inequality is not available and should not be expected.
-/

section CoordinateCertificate

open MonomialIndependence

variable (K : Type u) [CommSemiring K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- **A coordinate galactic certificate** for the coefficient table `T`, with data `(n,a,b,c,F)`
(AVW Definition 4.1 and Lemma 4.1, read in the variables of `T`).

It asserts: there are `ℕ`-valued weights `w` on the variables of `T^{⊗n}` (words of length `n`) and
a threshold `d` with every occurring term of weight at least `d` --- so that `T^{⊗n}` monomially
degenerates onto its minimum-weight part (`Tensor.monomialDegenerates_coordinateTensor_minimumWeightPart`)
--- and that minimum-weight part is the table of `F` disjoint copies of `⟨a,b,c⟩`, placed on the
words by the legwise injections `f` and extended by zero elsewhere.

The injections are presented as maps with retractions `g`, which is the choice-free form of
`Tensor.coordinateExtend`; injectivity of `f` is what makes `F·ab ≤ |X|^n` and its two companions
(`CoordinateGalacticCertificate.card_le`), the variable count AVW use in Theorem 4.1. -/
def CoordinateGalacticCertificate (T : (∀ i, κ i) → K) (n a b c F : ℕ) : Prop :=
  ∃ (w : ∀ i, (Fin n → κ i) → ℕ) (d : ℕ)
    (f : ∀ i, (Fin F × MMIndex a b c i) → (Fin n → κ i))
    (g : ∀ i, (Fin n → κ i) → (Fin F × MMIndex a b c i)),
    (∀ i x, g i (f i x) = x) ∧
    (∀ p, coordinatePower T n p ≠ 0 → d ≤ monomialTotalWeight w p) ∧
    minimumWeightPart w d (coordinatePower T n) =
      coordinateExtend f g (coordinateDirectSum (fun _ : Fin F ↦ mmCoefficients K a b c))

/-- **Counting variables in a certificate** (the step AVW phrase as "by counting variables in
`F ⊙ ⟨a,b,c⟩`, `F·ab ≤ |X^n|`").  The three legwise injections of a coordinate galactic
certificate bound the number of variables of the `F` copies by the number of variables of
`T^{⊗n}`, leg by leg:

```text
F·ab ≤ |X|^n,    F·bc ≤ |Y|^n,    F·ca ≤ |Z|^n.
```
-/
theorem CoordinateGalacticCertificate.card_le {T : (∀ i, κ i) → K} {n a b c F : ℕ}
    (h : CoordinateGalacticCertificate K T n a b c F) (i : Leg) :
    F * Fintype.card (MMIndex a b c i) ≤ Fintype.card (κ i) ^ n := by
  obtain ⟨w, d, f, g, hgf, -, -⟩ := h
  have hinj : Function.Injective (f i) := by
    intro x y hxy
    rw [← hgf i x, hxy, hgf]
  have hcard := Fintype.card_le_of_injective (f i) hinj
  rwa [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin] at hcard

/-- **From a certificate to a lower bound on `Ī`** (AVW Lemma 4.4 fed by Corollary 4.2).  A
coordinate galactic certificate `(n,a,b,c,F)` for `T` forces

```text
F · abc / max{a,b,c} ≤ Ī(T)^n.
```

Proof sketch: the power law `Ī(T^{⊗n}) = Ī(T)^n` and Corollary 4.2
(`Tensor.asymptoticIndependenceNumber_minimumWeightPart_le`, the *only* way a monomial
degeneration can feed `Ī`) bound `Ī` of the certificate's minimum-weight part by `Ī(T)^n`.  That
minimum-weight part is the block table of `F` copies of `⟨a,b,c⟩` up to variables occurring in no
term, which `Tensor.asymptoticIndependenceNumber_coordinateExtend` discards, and AVW Lemma 4.4
(`asymptoticIndependenceNumber_mmCoefficients_copies`) evaluates it. -/
theorem CoordinateGalacticCertificate.le_asymptoticIndependenceNumber_pow
    [NoZeroDivisors K] [Nontrivial K] {T : (∀ i, κ i) → K} {n a b c F : ℕ}
    (h : CoordinateGalacticCertificate K T n a b c F) (hn : n ≠ 0) :
    (F : ℝ) * (((a * b * c : ℕ) : ℝ) / ((max a (max b c) : ℕ) : ℝ)) ≤
      asymptoticIndependenceNumber T ^ n := by
  obtain ⟨w, d, f, g, hgf, hmin, heq⟩ := h
  have hstep := Tensor.asymptoticIndependenceNumber_minimumWeightPart_le
    (A := coordinatePower T n) w d hmin
  rw [heq, Tensor.asymptoticIndependenceNumber_coordinateExtend hgf,
    asymptoticIndependenceNumber_mmCoefficients_copies K F a b c,
    asymptoticIndependenceNumber_coordinatePower T hn] at hstep
  exact hstep

/-- A nondegenerate certificate has positive length: with `n = 0` the `F` copies would have to fit
into one variable per leg, forcing `abc ≤ 1`. -/
theorem CoordinateGalacticCertificate.length_ne_zero {T : (∀ i, κ i) → K} {n a b c F : ℕ}
    (h : CoordinateGalacticCertificate K T n a b c F) (habc : 2 ≤ a * b * c) (hF : 1 ≤ F) :
    n ≠ 0 := by
  rintro rfl
  have hX := CoordinateGalacticCertificate.card_le K h Leg.X
  have hY := CoordinateGalacticCertificate.card_le K h Leg.Y
  simp only [pow_zero, Fintype.card_prod, Fintype.card_fin] at hX hY
  have hab : a * b ≤ 1 := le_trans (Nat.le_mul_of_pos_left _ hF) hX
  have hbc : b * c ≤ 1 := le_trans (Nat.le_mul_of_pos_left _ hF) hY
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · simp at habc
    · exact h
  have hb0 : 0 < b := by
    rcases Nat.eq_zero_or_pos b with rfl | h
    · simp at habc
    · exact h
  have ha : a ≤ 1 := le_trans (Nat.le_mul_of_pos_right a hb0) hab
  have hb : b ≤ 1 := le_trans (Nat.le_mul_of_pos_left b ha0) hab
  have hc : c ≤ 1 := le_trans (Nat.le_mul_of_pos_left c hb0) hbc
  have hvol : a * b * c ≤ 1 * 1 * 1 := Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc
  omega

/-- **Every coordinate certificate is a galactic certificate** for the tensor `T` defines.

Proof sketch: relabel the words of `T^{⊗n}` to `Fin`-indexed coordinates
(`Tensor.Isomorphic.coordinateTensor_coordinateRelabel`), transport the weights along that
relabelling (`Tensor.MonomialIndependence.minimumWeightPart_coordinateRelabel`), and read the
certificate's equality as the target of `Tensor.monomialDegenerates_coordinateTensor_minimumWeightPart`.  The target then
restricts onto `F ⊙ ⟨a,b,c⟩` in three steps: forget the relabelling, forget the unused variables
(`Tensor.Restricts.coordinateTensor_pullback` with `Tensor.coordinateExtend_pullback`), and fold
the block table into the indexed direct sum
(`Tensor.Restricts.coordinateTensor_coordinateDirectSum`). -/
theorem CoordinateGalacticCertificate.galacticCertificate {T : (∀ i, κ i) → K} {n a b c F : ℕ}
    (h : CoordinateGalacticCertificate K T n a b c F) :
    GalacticCertificate K (coordinateTensor T) n a b c F := by
  classical
  obtain ⟨w, d, f, g, hgf, hmin, heq⟩ := h
  set A := coordinatePower T n with hA
  set e : ∀ i, (Fin n → κ i) ≃ Fin (Fintype.card (Fin n → κ i)) := fun i ↦ Fintype.equivFin _
    with he
  refine ⟨fun i ↦ Fintype.card (Fin n → κ i),
    coordinateTensor (coordinateRelabel e A),
    coordinateTensor (coordinateRelabel e (minimumWeightPart w d A)), ?_, ?_, ?_⟩
  · exact (Isomorphic.coordinateTensor_coordinatePower T n).symm.trans
      (Isomorphic.coordinateTensor_coordinateRelabel e A)
  · have hmin' : ∀ p, coordinateRelabel e A p ≠ 0 →
        d ≤ monomialTotalWeight (fun i y ↦ w i ((e i).symm y)) p := fun p hp ↦ hmin _ hp
    have hdeg := monomialDegenerates_coordinateTensor_minimumWeightPart
      (fun i y ↦ w i ((e i).symm y)) d (coordinateRelabel e A) hmin'
    rwa [minimumWeightPart_coordinateRelabel] at hdeg
  · have h1 : Restricts (coordinateTensor (coordinateRelabel e (minimumWeightPart w d A)))
        (coordinateTensor (minimumWeightPart w d A)) :=
      Tensor.Restricts.coordinateTensor_coordinateRelabel e _
    have h2 : Restricts (coordinateTensor (minimumWeightPart w d A))
        (coordinateTensor (coordinateDirectSum (fun _ : Fin F ↦ mmCoefficients K a b c))) := by
      rw [heq]
      have hpull := Tensor.Restricts.coordinateTensor_pullback (K := K) f
        (coordinateExtend f g (coordinateDirectSum (fun _ : Fin F ↦ mmCoefficients K a b c)))
      rwa [coordinateExtend_pullback hgf] at hpull
    have h3 : Restricts
        (coordinateTensor (coordinateDirectSum (fun _ : Fin F ↦ mmCoefficients K a b c)))
        (matrixMultiplicationCopies K F a b c) := by
      have hbridge := Tensor.Restricts.coordinateTensor_coordinateDirectSum
        (fun _ : Fin F ↦ mmCoefficients K a b c)
      rwa [funext fun _ : Fin F ↦ coordinateTensor_mmCoefficients (K := K) a b c] at hbridge
    exact (h1.trans h2).trans h3

/-- The set of values of the nondegenerate coordinate galactic certificates of the table `T`,
measured with the constructive border rank of the power --- the measure of
`AlgebraicComplexity.galacticValues`. -/
def coordinateGalacticValues (T : (∀ i, κ i) → K) : Set ℝ :=
  {x | ∃ n a b c F : ℕ, CoordinateGalacticCertificate K T n a b c F ∧ 2 ≤ a * b * c ∧ 1 ≤ F ∧
    x = galacticValue a b c F (Tensor.borderRank (Tensor.power (coordinateTensor T) n))}

/-- The same certificates, measured with the asymptotic rank of the power --- the measure closest
to AVW's `R̃`, and the one Theorem 4.1 is proved with. -/
def coordinateGalacticAsymptoticValues (T : (∀ i, κ i) → K) : Set ℝ :=
  {x | ∃ n a b c F : ℕ, CoordinateGalacticCertificate K T n a b c F ∧ 2 ≤ a * b * c ∧ 1 ≤ F ∧
    x = galacticValue a b c F (Tensor.asymptoticRank (Tensor.power (coordinateTensor T) n))}

/-- **The coordinate galactic exponent `ω_g^{coord}(T)`**: the infimum of the values of the
nondegenerate coordinate galactic certificates of the coefficient table `T`.  This is the exponent
AVW's Section 4 bounds from below, and `galacticExponent_le_coordinateGalacticExponent` compares it
with the basis-free `galacticExponent`. -/
noncomputable def coordinateGalacticExponent (T : (∀ i, κ i) → K) : ℝ :=
  sInf (coordinateGalacticValues K T)

/-- The asymptotic-rank variant of `coordinateGalacticExponent`. -/
noncomputable def coordinateGalacticAsymptoticExponent (T : (∀ i, κ i) → K) : ℝ :=
  sInf (coordinateGalacticAsymptoticValues K T)

/-- Every coordinate certificate value is a galactic certificate value of the tensor `T` defines. -/
theorem coordinateGalacticValues_subset (T : (∀ i, κ i) → K) :
    coordinateGalacticValues K T ⊆ galacticValues K (coordinateTensor T) := by
  rintro x ⟨n, a, b, c, F, hcert, habc, hF, rfl⟩
  exact ⟨n, a, b, c, F, hcert.galacticCertificate K, habc, hF, rfl⟩

/-- Asymptotic-rank companion of `coordinateGalacticValues_subset`. -/
theorem coordinateGalacticAsymptoticValues_subset (T : (∀ i, κ i) → K) :
    coordinateGalacticAsymptoticValues K T ⊆ galacticAsymptoticValues K (coordinateTensor T) := by
  rintro x ⟨n, a, b, c, F, hcert, habc, hF, rfl⟩
  exact ⟨n, a, b, c, F, hcert.galacticCertificate K, habc, hF, rfl⟩

end CoordinateCertificate

/-! ## Soundness of the coordinate exponent -/

section CoordinateSoundness

variable (K : Type u) [Field K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
variable {T : (∀ i, κ i) → K}

/-- Every value of a nondegenerate coordinate galactic certificate is at least `ω`. -/
theorem omega_le_of_mem_coordinateGalacticValues {x : ℝ}
    (hx : x ∈ coordinateGalacticValues K T) : omega K ≤ x :=
  omega_le_of_mem_galacticValues K (coordinateGalacticValues_subset K T hx)

/-- Every value of a nondegenerate coordinate galactic certificate, measured with asymptotic rank,
is at least `ω`. -/
theorem omega_le_of_mem_coordinateGalacticAsymptoticValues {x : ℝ}
    (hx : x ∈ coordinateGalacticAsymptoticValues K T) : omega K ≤ x :=
  omega_le_of_mem_galacticAsymptoticValues K (coordinateGalacticAsymptoticValues_subset K T hx)

/-- Every certificate value is at least `2`, by soundness and the flattening bound `2 ≤ ω`. -/
theorem two_le_of_mem_coordinateGalacticValues {x : ℝ}
    (hx : x ∈ coordinateGalacticValues K T) : 2 ≤ x :=
  le_trans (two_le_omega K) (omega_le_of_mem_coordinateGalacticValues K hx)

/-- Asymptotic-rank companion of `two_le_of_mem_coordinateGalacticValues`. -/
theorem two_le_of_mem_coordinateGalacticAsymptoticValues {x : ℝ}
    (hx : x ∈ coordinateGalacticAsymptoticValues K T) : 2 ≤ x :=
  le_trans (two_le_omega K) (omega_le_of_mem_coordinateGalacticAsymptoticValues K hx)

/-- The coordinate certificate values are bounded below, so their infimum is the genuine one. -/
theorem coordinateGalacticValues_bddBelow (T : (∀ i, κ i) → K) :
    BddBelow (coordinateGalacticValues K T) :=
  ⟨omega K, fun _ hx ↦ omega_le_of_mem_coordinateGalacticValues K hx⟩

/-- Asymptotic-rank companion of `coordinateGalacticValues_bddBelow`. -/
theorem coordinateGalacticAsymptoticValues_bddBelow (T : (∀ i, κ i) → K) :
    BddBelow (coordinateGalacticAsymptoticValues K T) :=
  ⟨omega K, fun _ hx ↦ omega_le_of_mem_coordinateGalacticAsymptoticValues K hx⟩

/-- **The basis-free galactic exponent never exceeds the coordinate one.**  Every monomial
degeneration read in the variables of `T` is in particular one read in some basis, so
`ω ≤ ω_g(T) ≤ ω_g^{coord}(T)`.  The reverse inequality is not available: `Ī` is basis-dependent,
and `galacticExponent` also admits certificates that follow the monomial degeneration by an
arbitrary legwise restriction. -/
theorem galacticExponent_le_coordinateGalacticExponent
    (hne : (coordinateGalacticValues K T).Nonempty) :
    galacticExponent K (coordinateTensor T) ≤ coordinateGalacticExponent K T :=
  le_csInf hne fun _ hx ↦
    csInf_le (galacticValues_bddBelow K _) (coordinateGalacticValues_subset K T hx)

/-- Asymptotic-rank companion of `galacticExponent_le_coordinateGalacticExponent`. -/
theorem galacticAsymptoticExponent_le_coordinateGalacticAsymptoticExponent
    (hne : (coordinateGalacticAsymptoticValues K T).Nonempty) :
    galacticAsymptoticExponent K (coordinateTensor T) ≤
      coordinateGalacticAsymptoticExponent K T :=
  le_csInf hne fun _ hx ↦
    csInf_le (galacticAsymptoticValues_bddBelow K _)
      (coordinateGalacticAsymptoticValues_subset K T hx)

/-- **Soundness of the coordinate galactic method**: `ω ≤ ω_g^{coord}(T)`. -/
theorem omega_le_coordinateGalacticExponent (hne : (coordinateGalacticValues K T).Nonempty) :
    omega K ≤ coordinateGalacticExponent K T :=
  le_csInf hne fun _ hx ↦ omega_le_of_mem_coordinateGalacticValues K hx

/-- Asymptotic-rank companion of `omega_le_coordinateGalacticExponent`. -/
theorem omega_le_coordinateGalacticAsymptoticExponent
    (hne : (coordinateGalacticAsymptoticValues K T).Nonempty) :
    omega K ≤ coordinateGalacticAsymptoticExponent K T :=
  le_csInf hne fun _ hx ↦ omega_le_of_mem_coordinateGalacticAsymptoticValues K hx

/-- `2 ≤ ω_g^{coord}(T)` whenever certificates exist. -/
theorem two_le_coordinateGalacticExponent (hne : (coordinateGalacticValues K T).Nonempty) :
    2 ≤ coordinateGalacticExponent K T :=
  le_trans (two_le_omega K) (omega_le_coordinateGalacticExponent K hne)

/-- `2 ≤ ω_g^{coord,R̃}(T)` whenever certificates exist. -/
theorem two_le_coordinateGalacticAsymptoticExponent
    (hne : (coordinateGalacticAsymptoticValues K T).Nonempty) :
    2 ≤ coordinateGalacticAsymptoticExponent K T :=
  le_trans (two_le_omega K) (omega_le_coordinateGalacticAsymptoticExponent K hne)

end CoordinateSoundness



/-! ## The barrier inequality -/

section Barrier

variable (K : Type u) [Field K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
variable {T : (∀ i, κ i) → K}

/-- **The variable count of a certificate, multiplied out.**  From `F·ab ≤ R^n`, `F·bc ≤ R^n` and
`F·ca ≤ R^n` --- the three legwise counts of `CoordinateGalacticCertificate.card_le`, with `R` any
bound on the three leg dimensions --- the two counts involving the largest of `a, b, c` multiply to

```text
F² · abc · max{a,b,c} ≤ (R^n)².
```

This is AVW's "`max{a,b,c} ≤ R̃(T)^{2n}/(abc F)²·abc`" step, cleared of denominators. -/
theorem CoordinateGalacticCertificate.sq_mul_volume_mul_max_le
    {n a b c F : ℕ} {R : ℝ} (hcert : CoordinateGalacticCertificate K T n a b c F)
    (hR : 1 ≤ R) (hcard : ∀ i, ((Fintype.card (κ i) : ℕ) : ℝ) ≤ R) :
    (F : ℝ) ^ 2 * ((a * b * c : ℕ) : ℝ) * ((max a (max b c) : ℕ) : ℝ) ≤ (R ^ n) ^ 2 := by
  have hR0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR
  have hleg : ∀ i, (F : ℝ) * ((Fintype.card (MMIndex a b c i) : ℕ) : ℝ) ≤ R ^ n := by
    intro i
    have hnat := CoordinateGalacticCertificate.card_le K hcert i
    have h1 : ((F * Fintype.card (MMIndex a b c i) : ℕ) : ℝ) ≤
        ((Fintype.card (κ i) ^ n : ℕ) : ℝ) := by exact_mod_cast hnat
    have h2 : ((Fintype.card (κ i) ^ n : ℕ) : ℝ) ≤ R ^ n := by
      push_cast
      exact pow_le_pow_left₀ (by positivity) (hcard i) n
    push_cast at h1 h2
    linarith
  have hX : (F : ℝ) * ((a : ℝ) * (b : ℝ)) ≤ R ^ n := by
    have h := hleg Leg.X
    rwa [show Fintype.card (MMIndex a b c Leg.X) = a * b by simp, Nat.cast_mul] at h
  have hY : (F : ℝ) * ((b : ℝ) * (c : ℝ)) ≤ R ^ n := by
    have h := hleg Leg.Y
    rwa [show Fintype.card (MMIndex a b c Leg.Y) = b * c by simp, Nat.cast_mul] at h
  have hZ : (F : ℝ) * ((c : ℝ) * (a : ℝ)) ≤ R ^ n := by
    have h := hleg Leg.Z
    rwa [show Fintype.card (MMIndex a b c Leg.Z) = c * a by simp, Nat.cast_mul] at h
  have hRn : (0 : ℝ) ≤ R ^ n := by positivity
  have hmax : max a (max b c) = a ∨ max a (max b c) = b ∨ max a (max b c) = c := by omega
  rcases hmax with h | h | h <;> rw [h] <;> push_cast
  · calc (F : ℝ) ^ 2 * ((a : ℝ) * b * c) * a
        = ((F : ℝ) * ((a : ℝ) * b)) * ((F : ℝ) * ((c : ℝ) * a)) := by ring
      _ ≤ (R ^ n) * (R ^ n) := mul_le_mul hX hZ (by positivity) hRn
      _ = (R ^ n) ^ 2 := by ring
  · calc (F : ℝ) ^ 2 * ((a : ℝ) * b * c) * b
        = ((F : ℝ) * ((a : ℝ) * b)) * ((F : ℝ) * ((b : ℝ) * c)) := by ring
      _ ≤ (R ^ n) * (R ^ n) := mul_le_mul hX hY (by positivity) hRn
      _ = (R ^ n) ^ 2 := by ring
  · calc (F : ℝ) ^ 2 * ((a : ℝ) * b * c) * c
        = ((F : ℝ) * ((b : ℝ) * c)) * ((F : ℝ) * ((c : ℝ) * a)) := by ring
      _ ≤ (R ^ n) * (R ^ n) := mul_le_mul hY hZ (by positivity) hRn
      _ = (R ^ n) ^ 2 := by ring

/-- **The barrier inequality for a single certificate.**  Let `T` be a coefficient table all of
whose leg dimensions are at most `R ≥ 1`, and let `(n,a,b,c,F)` be a nondegenerate coordinate
galactic certificate for `T` whose value, measured with a rank `r ≥ R^n` of the `n`th power, is
`x ≥ 2`.  Then

```text
R^{6/x − 2} ≤ Ī(T).
```

This is the whole content of AVW Theorem 4.1; passing to the infimum over certificates is
`rpow_coordinateGalacticAsymptoticExponent_le_asymptoticIndependenceNumber`.

Proof sketch, in logarithms.  Write `V = abc` and `M = max{a,b,c}`.  The certificate gives
`F·V/M ≤ Ī(T)^n` (`CoordinateGalacticCertificate.le_asymptoticIndependenceNumber_pow`, i.e.
Lemma 4.4 fed by Corollary 4.2) and `F²·V·M ≤ (R^n)²`
(`CoordinateGalacticCertificate.sq_mul_volume_mul_max_le`, the variable count); adding their
logarithms gives `3 log F + 2 log V ≤ n log Ī + 2n log R`.  The definition of the certificate value
says `log r = log F + (x/3) log V`, so `(6/x)·n·log R ≤ (6/x)·log r = (6/x) log F + 2 log V`, and
`(6/x) log F ≤ 3 log F` because `x ≥ 2` and `F ≥ 1`.  Combining and dividing by `n` yields
`(6/x − 2) log R ≤ log Ī`. -/
theorem le_asymptoticIndependenceNumber_rpow_of_certificate
    {n a b c F : ℕ} {R r x : ℝ}
    (hcert : CoordinateGalacticCertificate K T n a b c F)
    (habc : 2 ≤ a * b * c) (hF : 1 ≤ F)
    (hR : 1 ≤ R) (hcard : ∀ i, ((Fintype.card (κ i) : ℕ) : ℝ) ≤ R)
    (hr : R ^ n ≤ r) (hx : x = galacticValue a b c F r) (hx2 : 2 ≤ x) :
    R ^ (6 / x - 2) ≤ asymptoticIndependenceNumber T := by
  have hn : n ≠ 0 := hcert.length_ne_zero K habc hF
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hFR : (1 : ℝ) ≤ (F : ℝ) := by exact_mod_cast hF
  have hF0 : (0 : ℝ) < (F : ℝ) := lt_of_lt_of_le one_pos hFR
  have hlogF : 0 ≤ Real.log F := Real.log_nonneg hFR
  set V : ℝ := ((a * b * c : ℕ) : ℝ) with hV
  have hV2 : (2 : ℝ) ≤ V := by
    rw [hV]
    exact_mod_cast habc
  have hV0 : (0 : ℝ) < V := by linarith
  have hlogV : 0 < Real.log V := Real.log_pos (by linarith)
  set M : ℝ := ((max a (max b c) : ℕ) : ℝ) with hM
  have hMnat : 1 ≤ max a (max b c) := by
    rcases Nat.eq_zero_or_pos (max a (max b c)) with h | h
    · exfalso
      have ha : a = 0 := by omega
      rw [ha] at habc
      simp at habc
    · exact h
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hM]
    exact_mod_cast hMnat
  have hM0 : (0 : ℝ) < M := by linarith
  -- the two certificate inequalities
  have hI := hcert.le_asymptoticIndependenceNumber_pow K hn
  have hFVM := hcert.sq_mul_volume_mul_max_le K hR hcard
  set I : ℝ := asymptoticIndependenceNumber T with hIdef
  have hI0 : 0 ≤ I := asymptoticIndependenceNumber_nonneg T
  have hIn : (0 : ℝ) < I ^ n := lt_of_lt_of_le (by positivity) hI
  have hIpos : 0 < I := by
    rcases hI0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hIn
      simp [zero_pow hn] at hIn
  -- logarithms
  have L1 : Real.log F + (Real.log V - Real.log M) ≤ (n : ℝ) * Real.log I := by
    have h := Real.log_le_log (by positivity) hI
    rwa [Real.log_mul (ne_of_gt hF0) (by positivity),
      Real.log_div (ne_of_gt hV0) (ne_of_gt hM0), Real.log_pow] at h
  have L2 : 2 * Real.log F + Real.log V + Real.log M ≤ 2 * ((n : ℝ) * Real.log R) := by
    have h := Real.log_le_log (by positivity) hFVM
    rw [Real.log_mul (by positivity) (ne_of_gt hM0),
      Real.log_mul (by positivity) (ne_of_gt hV0), Real.log_pow, Real.log_pow,
      Real.log_pow] at h
    push_cast at h
    linarith
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le (by positivity) hr
  have L4 : (n : ℝ) * Real.log R ≤ Real.log r := by
    have h := Real.log_le_log (by positivity) hr
    rwa [Real.log_pow] at h
  have hxpos : (0 : ℝ) < x := by linarith
  have L3 : Real.log r = Real.log F + (x / 3) * Real.log V := by
    have hxV : x * Real.log V = 3 * (Real.log r - Real.log F) := by
      rw [hx, galacticValue, div_mul_cancel₀]
      exact ne_of_gt hlogV
    have hsplit : (x / 3) * Real.log V = x * Real.log V / 3 := by ring
    rw [hsplit, hxV]
    ring
  -- the arithmetic
  have h6x : 0 ≤ 6 / x := by positivity
  have h6x3 : 6 / x ≤ 3 := by
    rw [div_le_iff₀ hxpos]
    linarith
  have k1 : (6 / x) * ((n : ℝ) * Real.log R) ≤ (6 / x) * Real.log r :=
    mul_le_mul_of_nonneg_left L4 h6x
  have k2 : (6 / x) * Real.log r = (6 / x) * Real.log F + 2 * Real.log V := by
    rw [L3]
    field_simp
    ring
  have k3 : (6 / x) * Real.log F ≤ 3 * Real.log F :=
    mul_le_mul_of_nonneg_right h6x3 hlogF
  have hfinal : (6 / x) * ((n : ℝ) * Real.log R) - 2 * ((n : ℝ) * Real.log R) ≤
      (n : ℝ) * Real.log I := by linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := Nat.pos_of_ne_zero hn
    exact_mod_cast this
  have hgoal : (6 / x - 2) * Real.log R ≤ Real.log I := by
    refine le_of_mul_le_mul_left ?_ hn0
    calc (n : ℝ) * ((6 / x - 2) * Real.log R)
        = (6 / x) * ((n : ℝ) * Real.log R) - 2 * ((n : ℝ) * Real.log R) := by ring
      _ ≤ (n : ℝ) * Real.log I := hfinal
  rw [Real.rpow_def_of_pos hR0]
  calc Real.exp (Real.log R * (6 / x - 2)) ≤ Real.exp (Real.log I) := by
        refine Real.exp_le_exp.mpr ?_
        rw [mul_comm]
        exact hgoal
    _ = I := Real.exp_log hIpos

/-- The per-certificate barrier, for the asymptotic-rank measure. -/
theorem le_asymptoticIndependenceNumber_rpow_of_mem_asymptoticValues {R : ℝ}
    (hR : 1 ≤ R) (hcard : ∀ i, ((Fintype.card (κ i) : ℕ) : ℝ) ≤ R)
    (hRpow : ∀ m, R ^ m ≤ Tensor.asymptoticRank (Tensor.power (coordinateTensor T) m))
    {x : ℝ} (hx : x ∈ coordinateGalacticAsymptoticValues K T) :
    R ^ (6 / x - 2) ≤ asymptoticIndependenceNumber T := by
  obtain ⟨n, a, b, c, F, hcert, habc, hF, rfl⟩ := hx
  exact le_asymptoticIndependenceNumber_rpow_of_certificate K hcert habc hF hR hcard (hRpow n) rfl
    (two_le_of_mem_coordinateGalacticAsymptoticValues K ⟨n, a, b, c, F, hcert, habc, hF, rfl⟩)

/-- The per-certificate barrier, for the border-rank measure: the border rank of the power
dominates its asymptotic rank, so the same hypothesis on `R` suffices. -/
theorem le_asymptoticIndependenceNumber_rpow_of_mem_values {R : ℝ}
    (hR : 1 ≤ R) (hcard : ∀ i, ((Fintype.card (κ i) : ℕ) : ℝ) ≤ R)
    (hRpow : ∀ m, R ^ m ≤ Tensor.asymptoticRank (Tensor.power (coordinateTensor T) m))
    {x : ℝ} (hx : x ∈ coordinateGalacticValues K T) :
    R ^ (6 / x - 2) ≤ asymptoticIndependenceNumber T := by
  obtain ⟨n, a, b, c, F, hcert, habc, hF, rfl⟩ := hx
  refine le_asymptoticIndependenceNumber_rpow_of_certificate K hcert habc hF hR hcard
    (le_trans (hRpow n) (Tensor.asymptoticRank_le_borderRank _)) rfl
    (two_le_of_mem_coordinateGalacticValues K ⟨n, a, b, c, F, hcert, habc, hF, rfl⟩)

/-- **AVW Theorem 4.1.**  For a coefficient table `T` whose leg dimensions are all at most `R ≥ 1`,
with `R^m` dominated by the asymptotic rank of every power of the tensor `T` defines,

```text
R^{6/ω_g^{coord}(T) − 2} ≤ Ī(T),
```

where `ω_g^{coord}(T)` is the asymptotic-rank coordinate galactic exponent.  For a concise `T` the
hypotheses hold with `R = R̃(T)` (`asymptoticRank_conciseness` below), which is AVW's displayed
`Ī(T) ≥ R̃(T)^{6/ω_g(T) − 2}`.

Proof sketch: `le_asymptoticIndependenceNumber_rpow_of_mem_asymptoticValues` gives the inequality
for every certificate value `x`, and the exponent is the infimum of those values.  Since
`x ↦ R^{6/x − 2}` is antitone, the passage to the infimum is a limit: for every `ε > 0` some
certificate value lies below `ω_g + ε`, so `R^{6/(ω_g+ε) − 2} ≤ Ī(T)`, and the left-hand side is
continuous in `ε` at `0` because `ω_g ≥ 2 > 0`. -/
theorem rpow_coordinateGalacticAsymptoticExponent_le_asymptoticIndependenceNumber {R : ℝ}
    (hR : 1 ≤ R) (hcard : ∀ i, ((Fintype.card (κ i) : ℕ) : ℝ) ≤ R)
    (hRpow : ∀ m, R ^ m ≤ Tensor.asymptoticRank (Tensor.power (coordinateTensor T) m))
    (hne : (coordinateGalacticAsymptoticValues K T).Nonempty) :
    R ^ (6 / coordinateGalacticAsymptoticExponent K T - 2) ≤ asymptoticIndependenceNumber T := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
  set w : ℝ := coordinateGalacticAsymptoticExponent K T with hw
  have hw2 : 2 ≤ w := two_le_coordinateGalacticAsymptoticExponent K hne
  have hw0 : (0 : ℝ) < w := by linarith
  -- the inequality at every point strictly above the infimum
  have hstep : ∀ e : ℝ, 0 < e → R ^ (6 / (w + e) - 2) ≤ asymptoticIndependenceNumber T := by
    intro e he
    obtain ⟨x, hxmem, hxlt⟩ := exists_lt_of_csInf_lt hne (show w < w + e by linarith)
    have hx2 : 2 ≤ x := two_le_of_mem_coordinateGalacticAsymptoticValues K hxmem
    have hx0 : (0 : ℝ) < x := by linarith
    have hmono : 6 / (w + e) - 2 ≤ 6 / x - 2 := by
      have : 6 / (w + e) ≤ 6 / x := by
        apply div_le_div_of_nonneg_left (by norm_num) hx0
        linarith
      linarith
    refine le_trans (Real.rpow_le_rpow_of_exponent_le hR hmono) ?_
    exact le_asymptoticIndependenceNumber_rpow_of_mem_asymptoticValues K hR hcard hRpow hxmem
  -- pass to the limit `e → 0⁺`
  have hcontdiv : ContinuousAt (fun e : ℝ ↦ 6 / (w + e) - 2) 0 := by
    refine ContinuousAt.sub (ContinuousAt.div continuousAt_const ?_ ?_) continuousAt_const
    · exact continuousAt_const.add continuousAt_id
    · simpa using ne_of_gt hw0
  have hconv : Filter.Tendsto (fun e : ℝ ↦ R ^ (6 / (w + e) - 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (R ^ (6 / w - 2))) := by
    have hcomp : ContinuousAt (fun e : ℝ ↦ R ^ (6 / (w + e) - 2)) 0 :=
      (Real.continuousAt_const_rpow (ne_of_gt hR0)).comp hcontdiv
    have := hcomp.continuousWithinAt (s := Set.Ioi (0 : ℝ))
    simpa using this.tendsto
  refine le_of_tendsto hconv ?_
  filter_upwards [self_mem_nhdsWithin] with e he
  exact hstep e he

/-- **AVW Theorem 4.1**, for the border-rank measure of the certificate values.  Since the
border rank of a power dominates its asymptotic rank, every border-rank certificate value is at
least the corresponding asymptotic-rank value, so this form follows from the previous one. -/
theorem rpow_coordinateGalacticExponent_le_asymptoticIndependenceNumber {R : ℝ}
    (hR : 1 ≤ R) (hcard : ∀ i, ((Fintype.card (κ i) : ℕ) : ℝ) ≤ R)
    (hRpow : ∀ m, R ^ m ≤ Tensor.asymptoticRank (Tensor.power (coordinateTensor T) m))
    (hne : (coordinateGalacticValues K T).Nonempty) :
    R ^ (6 / coordinateGalacticExponent K T - 2) ≤ asymptoticIndependenceNumber T := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
  set w : ℝ := coordinateGalacticExponent K T with hw
  have hw2 : 2 ≤ w := two_le_coordinateGalacticExponent K hne
  have hw0 : (0 : ℝ) < w := by linarith
  have hstep : ∀ e : ℝ, 0 < e → R ^ (6 / (w + e) - 2) ≤ asymptoticIndependenceNumber T := by
    intro e he
    obtain ⟨x, hxmem, hxlt⟩ := exists_lt_of_csInf_lt hne (show w < w + e by linarith)
    have hx2 : 2 ≤ x := two_le_of_mem_coordinateGalacticValues K hxmem
    have hx0 : (0 : ℝ) < x := by linarith
    have hmono : 6 / (w + e) - 2 ≤ 6 / x - 2 := by
      have : 6 / (w + e) ≤ 6 / x := by
        apply div_le_div_of_nonneg_left (by norm_num) hx0
        linarith
      linarith
    refine le_trans (Real.rpow_le_rpow_of_exponent_le hR hmono) ?_
    exact le_asymptoticIndependenceNumber_rpow_of_mem_values K hR hcard hRpow hxmem
  have hcontdiv : ContinuousAt (fun e : ℝ ↦ 6 / (w + e) - 2) 0 := by
    refine ContinuousAt.sub (ContinuousAt.div continuousAt_const ?_ ?_) continuousAt_const
    · exact continuousAt_const.add continuousAt_id
    · simpa using ne_of_gt hw0
  have hconv : Filter.Tendsto (fun e : ℝ ↦ R ^ (6 / (w + e) - 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (R ^ (6 / w - 2))) := by
    have hcomp : ContinuousAt (fun e : ℝ ↦ R ^ (6 / (w + e) - 2)) 0 :=
      (Real.continuousAt_const_rpow (ne_of_gt hR0)).comp hcontdiv
    have := hcomp.continuousWithinAt (s := Set.Ioi (0 : ℝ))
    simpa using this.tendsto
  refine le_of_tendsto hconv ?_
  filter_upwards [self_mem_nhdsWithin] with e he
  exact hstep e he

/-! ## Corollary 4.3, in the explicit form -/

/-- Arithmetic of the constant: for `s < 1` the exponent `6/(s+2)` is strictly above `2`. -/
theorem two_lt_six_div_add_two {s : ℝ} (hs2 : 0 < s + 2) (hs : s < 1) : 2 < 6 / (s + 2) := by
  rw [lt_div_iff₀ hs2]
  linarith

/-- **AVW Corollary 4.3**, explicit form.  If the asymptotic independence number of the table `T`
is at most `R^s`, where `R > 1` bounds the leg dimensions and every `R^m` is dominated by the
asymptotic rank of the `m`th power, then the coordinate galactic exponent of `T` is at least the
*explicit* constant `6/(s+2)`.  For `s < 1` that constant is strictly above `2`
(`two_lt_six_div_add_two`), which is the form AVW state; the theorem itself needs only
`0 < s + 2`.

Proof sketch: for every certificate value `x`, Theorem 4.1 gives `R^{6/x−2} ≤ Ī(T) ≤ R^s`; since
`R > 1` the exponents compare, `6/x − 2 ≤ s`, that is `6/(s+2) ≤ x`.  Taking the infimum over `x`
needs no limiting argument, which is why this form --- and not the infimum form of Theorem 4.1 ---
is the interface for the later sections. -/
theorem six_div_add_two_le_coordinateGalacticAsymptoticExponent {R s : ℝ}
    (hR : 1 < R) (hcard : ∀ i, ((Fintype.card (κ i) : ℕ) : ℝ) ≤ R)
    (hRpow : ∀ m, R ^ m ≤ Tensor.asymptoticRank (Tensor.power (coordinateTensor T) m))
    (hs2 : 0 < s + 2) (hIs : asymptoticIndependenceNumber T ≤ R ^ s)
    (hne : (coordinateGalacticAsymptoticValues K T).Nonempty) :
    6 / (s + 2) ≤ coordinateGalacticAsymptoticExponent K T := by
  refine le_csInf hne fun x hx ↦ ?_
  have hx2 : 2 ≤ x := two_le_of_mem_coordinateGalacticAsymptoticValues K hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hbar := le_asymptoticIndependenceNumber_rpow_of_mem_asymptoticValues K hR.le hcard hRpow hx
  have hexp : 6 / x - 2 ≤ s := (Real.rpow_le_rpow_left_iff hR).mp (le_trans hbar hIs)
  have hkey : 6 / x ≤ s + 2 := by linarith
  rw [div_le_iff₀ hx0] at hkey
  rw [div_le_iff₀ hs2]
  linarith [hkey]

/-- Border-rank companion of `six_div_add_two_le_coordinateGalacticAsymptoticExponent`. -/
theorem six_div_add_two_le_coordinateGalacticExponent {R s : ℝ}
    (hR : 1 < R) (hcard : ∀ i, ((Fintype.card (κ i) : ℕ) : ℝ) ≤ R)
    (hRpow : ∀ m, R ^ m ≤ Tensor.asymptoticRank (Tensor.power (coordinateTensor T) m))
    (hs2 : 0 < s + 2) (hIs : asymptoticIndependenceNumber T ≤ R ^ s)
    (hne : (coordinateGalacticValues K T).Nonempty) :
    6 / (s + 2) ≤ coordinateGalacticExponent K T := by
  refine le_csInf hne fun x hx ↦ ?_
  have hx2 : 2 ≤ x := two_le_of_mem_coordinateGalacticValues K hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hbar := le_asymptoticIndependenceNumber_rpow_of_mem_values K hR.le hcard hRpow hx
  have hexp : 6 / x - 2 ≤ s := (Real.rpow_le_rpow_left_iff hR).mp (le_trans hbar hIs)
  have hkey : 6 / x ≤ s + 2 := by linarith
  rw [div_le_iff₀ hx0] at hkey
  rw [div_le_iff₀ hs2]
  linarith [hkey]

/-- **AVW Corollary 4.3**, in the form the barrier program consumes: a tensor whose asymptotic
independence number is at most `R^s` with `s < 1` cannot be used by the Galactic method to prove
any exponent bound below the explicit constant `6/(s+2) > 2`. -/
theorem two_lt_coordinateGalacticExponent_of_le_rpow {R s : ℝ}
    (hR : 1 < R) (hcard : ∀ i, ((Fintype.card (κ i) : ℕ) : ℝ) ≤ R)
    (hRpow : ∀ m, R ^ m ≤ Tensor.asymptoticRank (Tensor.power (coordinateTensor T) m))
    (hs2 : 0 < s + 2) (hs : s < 1) (hIs : asymptoticIndependenceNumber T ≤ R ^ s)
    (hne : (coordinateGalacticValues K T).Nonempty) :
    2 < coordinateGalacticExponent K T :=
  lt_of_lt_of_le (two_lt_six_div_add_two hs2 hs)
    (six_div_add_two_le_coordinateGalacticExponent K hR hcard hRpow hs2 hIs hne)

end Barrier

/-! ## The concise form: `R = R̃(T)`

Conciseness enters the whole development exactly once, to supply the two hypotheses above with
`R = R̃(T)`: the leg dimensions are at most `R̃(T)`
(`Tensor.card_le_asymptoticRank`, through conciseness of every Kronecker power), and
`R̃(T)^m ≤ R̃(T^{⊗m})` (`Tensor.asymptoticRank_pow_le_asymptoticRank_power`, the half of AVW's
`R̃(T^{⊗n}) = R̃(T)^n` that does not need multiplicativity of asymptotic rank). -/

section Concise

variable (K : Type u) [Field K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] [∀ i, Nonempty (κ i)]
variable {T : (∀ i, κ i) → K}

/-- A concise table has asymptotic rank at least `1`. -/
theorem one_le_asymptoticRank_of_isCoordinateConcise
    (hconc : ∀ i, Tensor.IsCoordinateConcise T i) :
    1 ≤ Tensor.asymptoticRank (coordinateTensor T) := by
  refine le_trans ?_ (Tensor.card_le_asymptoticRank (hconc Leg.X))
  have : 0 < Fintype.card (κ Leg.X) := Fintype.card_pos
  exact_mod_cast this

/-- Powers of the asymptotic rank of a concise table are dominated by the asymptotic ranks of the
powers. -/
theorem asymptoticRank_pow_le_of_isCoordinateConcise
    (hconc : ∀ i, Tensor.IsCoordinateConcise T i) (m : ℕ) :
    Tensor.asymptoticRank (coordinateTensor T) ^ m ≤
      Tensor.asymptoticRank (Tensor.power (coordinateTensor T) m) :=
  Tensor.asymptoticRank_pow_le_asymptoticRank_power (coordinateTensor T)
    (fun k ↦ Tensor.one_le_rank_power_coordinateTensor (hconc Leg.X) k) m

/-- **AVW Theorem 4.1**, in the displayed form: for a concise coefficient table `T`,

```text
Ī(T) ≥ R̃(T)^{6/ω_g(T) − 2},
```

with `ω_g` the asymptotic-rank coordinate galactic exponent.  Conciseness is used exactly once,
to bound the three leg dimensions by `R̃(T)`. -/
theorem rpow_coordinateGalacticAsymptoticExponent_le_asymptoticIndependenceNumber_of_concise
    (hconc : ∀ i, Tensor.IsCoordinateConcise T i)
    (hne : (coordinateGalacticAsymptoticValues K T).Nonempty) :
    Tensor.asymptoticRank (coordinateTensor T) ^
        (6 / coordinateGalacticAsymptoticExponent K T - 2) ≤
      asymptoticIndependenceNumber T :=
  rpow_coordinateGalacticAsymptoticExponent_le_asymptoticIndependenceNumber K
    (one_le_asymptoticRank_of_isCoordinateConcise K hconc)
    (fun i ↦ Tensor.card_le_asymptoticRank (hconc i))
    (asymptoticRank_pow_le_of_isCoordinateConcise K hconc) hne

/-- **AVW Theorem 4.1** for the border-rank measure of the certificate values. -/
theorem rpow_coordinateGalacticExponent_le_asymptoticIndependenceNumber_of_concise
    (hconc : ∀ i, Tensor.IsCoordinateConcise T i)
    (hne : (coordinateGalacticValues K T).Nonempty) :
    Tensor.asymptoticRank (coordinateTensor T) ^
        (6 / coordinateGalacticExponent K T - 2) ≤
      asymptoticIndependenceNumber T :=
  rpow_coordinateGalacticExponent_le_asymptoticIndependenceNumber K
    (one_le_asymptoticRank_of_isCoordinateConcise K hconc)
    (fun i ↦ Tensor.card_le_asymptoticRank (hconc i))
    (asymptoticRank_pow_le_of_isCoordinateConcise K hconc) hne

/-- **AVW Corollary 4.3**, in the displayed form and with the explicit constant: for a concise
table `T` and a constant `s < 1`, if `Ī(T) ≤ R̃(T)^s` then the Galactic method applied to `T`
cannot prove any exponent below `6/(s+2) > 2`.

The hypothesis `1 < R̃(T)` is not cosmetic: a table of asymptotic rank `1` carries no information
about the exponent, and `R̃(T)^s` would be `1` for every `s`. -/
theorem six_div_add_two_le_coordinateGalacticExponent_of_concise {s : ℝ}
    (hconc : ∀ i, Tensor.IsCoordinateConcise T i)
    (hR : 1 < Tensor.asymptoticRank (coordinateTensor T))
    (hs2 : 0 < s + 2)
    (hIs : asymptoticIndependenceNumber T ≤ Tensor.asymptoticRank (coordinateTensor T) ^ s)
    (hne : (coordinateGalacticValues K T).Nonempty) :
    6 / (s + 2) ≤ coordinateGalacticExponent K T :=
  six_div_add_two_le_coordinateGalacticExponent K hR
    (fun i ↦ Tensor.card_le_asymptoticRank (hconc i))
    (asymptoticRank_pow_le_of_isCoordinateConcise K hconc) hs2 hIs hne

/-- **AVW Corollary 4.3**, final form: `Ī(T) ≤ R̃(T)^s` with `s < 1` forces
`ω_g^{coord}(T) ≥ 6/(s+2) > 2`. -/
theorem two_lt_coordinateGalacticExponent_of_concise {s : ℝ}
    (hconc : ∀ i, Tensor.IsCoordinateConcise T i)
    (hR : 1 < Tensor.asymptoticRank (coordinateTensor T))
    (hs2 : 0 < s + 2) (hs : s < 1)
    (hIs : asymptoticIndependenceNumber T ≤ Tensor.asymptoticRank (coordinateTensor T) ^ s)
    (hne : (coordinateGalacticValues K T).Nonempty) :
    2 < coordinateGalacticExponent K T :=
  lt_of_lt_of_le (two_lt_six_div_add_two hs2 hs)
    (six_div_add_two_le_coordinateGalacticExponent_of_concise K hconc hR hs2 hIs hne)

/-- **AVW Corollary 4.3, first sentence.**  If the Galactic method with a concise `T` reaches the
exponent `2`, then the asymptotic independence number of `T` is exactly its asymptotic rank.

Proof sketch: Theorem 4.1 at `ω_g = 2` reads `Ī(T) ≥ R̃(T)^{6/2 − 2} = R̃(T)`, and
`Tensor.asymptoticIndependenceNumber_le_asymptoticRank` is the converse inequality. -/
theorem asymptoticIndependenceNumber_eq_asymptoticRank_of_coordinateGalacticExponent_eq_two
    (hconc : ∀ i, Tensor.IsCoordinateConcise T i)
    (hne : (coordinateGalacticValues K T).Nonempty)
    (h2 : coordinateGalacticExponent K T = 2) :
    asymptoticIndependenceNumber T = Tensor.asymptoticRank (coordinateTensor T) := by
  refine le_antisymm (asymptoticIndependenceNumber_le_asymptoticRank T) ?_
  have hbar := rpow_coordinateGalacticExponent_le_asymptoticIndependenceNumber_of_concise K
    hconc hne
  rw [h2] at hbar
  norm_num at hbar
  exact hbar

end Concise






/-! ## A tiny regression client: the trivial certificate

The definition of a coordinate galactic certificate is satisfiable, and the smallest instance is
the tensor `⟨a,b,c⟩` certifying itself with `(n, F) = (1, 1)`, all weights zero and the identity
embedding.  It is the coefficient-level counterpart of
`AlgebraicComplexity.galacticCertificate_matrixMultiplication`, and it makes the nonemptiness
hypotheses of the barrier theorems demonstrably satisfiable. -/

section TrivialCertificate

variable (K : Type u) [CommSemiring K]

/-- Reading a one-letter word as a letter, on the variables of `⟨a,b,c⟩`. -/
private def mmOneWord (a b c : ℕ) (i : Leg) (x : Fin 1 × MMIndex a b c i) :
    Fin 1 → MMIndex a b c i := fun _ ↦ x.2

/-- The retraction of `mmOneWord`. -/
private def mmOneWordInv (a b c : ℕ) (i : Leg) (q : Fin 1 → MMIndex a b c i) :
    Fin 1 × MMIndex a b c i := (0, q 0)

/-- **The trivial coordinate galactic certificate.**  The table of `⟨a,b,c⟩` is its own
minimum-weight part for the zero weighting, and one copy of `⟨a,b,c⟩` fills its variables exactly.

Proof sketch: with all weights `0` and threshold `0` the minimum-weight part is the table itself
(`Tensor.minimumWeightPart_of_weight`), the first Kronecker power reads a one-letter word as a
letter, and the block table of a single copy is the table itself. -/
theorem coordinateGalacticCertificate_mmCoefficients (a b c : ℕ) :
    CoordinateGalacticCertificate K (mmCoefficients K a b c) 1 a b c 1 := by
  refine ⟨fun _ _ ↦ 0, 0, mmOneWord a b c, mmOneWordInv a b c, ?_, ?_, ?_⟩
  · intro i x
    exact Prod.ext (Subsingleton.elim _ _) rfl
  · intro p _
    exact Nat.zero_le _
  · funext p
    have hz : Tensor.monomialTotalWeight
        (fun (i : Leg) (_ : Fin 1 → MMIndex a b c i) ↦ (0 : ℕ)) p = 0 := rfl
    rw [Tensor.MonomialIndependence.minimumWeightPart_of_weight hz]
    have hrange : ∀ i, mmOneWord a b c i (mmOneWordInv a b c i (p i)) = p i := by
      intro i
      funext t
      rw [Subsingleton.elim t 0]
      rfl
    rw [Tensor.coordinateExtend, if_pos hrange]
    have hblock : (fun i ↦ (mmOneWordInv a b c i (p i)).2) = fun i ↦ p i 0 := rfl
    rw [show (fun i ↦ (mmOneWordInv a b c i (p i))) =
        blockTriple (0 : Fin 1) (fun i ↦ p i 0) from rfl,
      coordinateDirectSum_blockTriple, coordinatePower_apply, Fin.prod_univ_one]

end TrivialCertificate

section TrivialCertificateField

variable (K : Type u) [Field K]

/-- The certificate value set of `⟨a,b,c⟩` is nonempty as soon as the volume is nondegenerate, so
its coordinate galactic exponent is a genuine infimum. -/
theorem coordinateGalacticValues_mmCoefficients_nonempty {a b c : ℕ} (habc : 2 ≤ a * b * c) :
    (coordinateGalacticValues K (mmCoefficients K a b c)).Nonempty :=
  ⟨_, ⟨1, a, b, c, 1, coordinateGalacticCertificate_mmCoefficients K a b c, habc, le_rfl, rfl⟩⟩

/-- Asymptotic-rank companion of `coordinateGalacticValues_mmCoefficients_nonempty`. -/
theorem coordinateGalacticAsymptoticValues_mmCoefficients_nonempty {a b c : ℕ}
    (habc : 2 ≤ a * b * c) :
    (coordinateGalacticAsymptoticValues K (mmCoefficients K a b c)).Nonempty :=
  ⟨_, ⟨1, a, b, c, 1, coordinateGalacticCertificate_mmCoefficients K a b c, habc, le_rfl, rfl⟩⟩

end TrivialCertificateField

/-! ## Milestones M1 and M2: balanced certificates, and zeroing outs as certificates

This section is plan items **M1** and **M2** of `BARRIER_FRAMEWORK.md`.  Both are small bridges
between the certificate calculus above and the shape in which a concrete extraction is actually
produced downstream.

**M1, the balanced case.**  `CoordinateGalacticCertificate.le_asymptoticIndependenceNumber_pow`
--- [AlmanVassilevskaWilliams2018, Lemma 4.4] fed by
[AlmanVassilevskaWilliams2018, Corollary 4.2] --- reads `F · abc / max{a,b,c} ≤ Ī(T)^n`.  When the
extracted matrix-multiplication tensor is *balanced*, `a = b = c`, the volume-over-maximum factor
collapses to `a²`, and the resulting `F · a² ≤ Ī(T)^n` is the form the later sections consume.
No positivity of `a` is needed: for `a = 0` both sides of the collapse are `0`, since division by
zero in `ℝ` returns `0`.

**M2, zeroing out as a certificate.**  A monomial degeneration with indicator weights is a zeroing
out (`Tensor.MonomialIndependence.minimumWeightPart_indicator_eq_coordinateZeroOut`), so a client
that has produced an explicit *zeroing out* of the Kronecker power `T^{⊗n}` onto `F` embedded copies of `⟨a,b,c⟩` has
already produced a coordinate galactic certificate: take `w i v = 0` for the surviving variables
`v ∈ A i` and `w i v = 1` for the deleted ones, and threshold `d = 0`.  The threshold condition is
then vacuous, because `0` is a lower bound for every `ℕ`-valued weight.  This is the interface that
`Examples/CoppersmithWinogradEasyCoordinate.lean` (plan item **M5**) and
`Tensor/CoordinateBlockWord.lean` (plan item **M3**) target.

The arithmetic companion of M1, `R ≤ F·M^f → R^{2/f} ≤ F·M²` for `f ≥ 2`, is pure real analysis
and lives in the shared analysis leaf as
`AlgebraicComplexity.Growth.rpow_two_div_le_of_le_mul_rpow`.

**The pivot-bijection certificate.**  Every barrier client so far discharges the nonemptiness
hypothesis of Corollary 4.3 by the *same* zeroing out: keep a single `X` variable `x₀`, keep a set
of `Y` variables and a set of `Z` variables matched by a bijection `e`, and observe that the
surviving terms are exactly `x₀ y z` with `z = e y`, each with coefficient `1`.  That is one copy
of `⟨1,1,|A_Y|⟩`, so `coordinateGalacticCertificate_of_pivot_bijection` turns the single
hypothesis "on the retained variables `T` is the indicator of the graph of `e`" into a certificate,
with the legwise injections, their retractions and the `n = 1` bookkeeping done once and for all.
-/

section BalancedCertificate

variable (K : Type u) [CommSemiring K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- **M1: the balanced form of [AlmanVassilevskaWilliams2018, Lemma 4.4].**  A coordinate galactic
certificate that extracts `F` copies of the *cubic* tensor `⟨a,a,a⟩` from `T^{⊗n}` forces

```text
F · a² ≤ Ī(T)^n.
```

Proof sketch: `CoordinateGalacticCertificate.le_asymptoticIndependenceNumber_pow` gives
`F · (a·a·a)/max{a, max{a,a}} ≤ Ī(T)^n`, and `max_self` collapses the denominator to `a`.  The
quotient `a³/a` equals `a²` for `a ≠ 0`, and for `a = 0` both sides are `0` because `ℝ`-division by
zero returns `0`; so no positivity hypothesis on `a` is required. -/
theorem CoordinateGalacticCertificate.sq_le_asymptoticIndependenceNumber_pow
    [NoZeroDivisors K] [Nontrivial K] {T : (∀ i, κ i) → K} {n a F : ℕ}
    (h : CoordinateGalacticCertificate K T n a a a F) (hn : n ≠ 0) :
    (F : ℝ) * (a : ℝ) ^ 2 ≤ asymptoticIndependenceNumber T ^ n := by
  have hstep := h.le_asymptoticIndependenceNumber_pow K hn
  rw [max_self, max_self] at hstep
  have hquot : (((a * a * a : ℕ) : ℝ) / ((a : ℕ) : ℝ)) = (a : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · norm_num
    · have hane : ((a : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
      push_cast
      field_simp
  rwa [hquot] at hstep

omit [∀ i, Fintype (κ i)] in
/-- **M2: a zeroing out of the power onto `F` embedded copies of `⟨a,b,c⟩` is a coordinate galactic
certificate.**  If the coefficient table of `T^{⊗n}`, zeroed out to the legwise variable sets `A`,
*is* the table of `F` disjoint copies of `⟨a,b,c⟩` embedded by the legwise injections `f` (with
retractions `g`) and extended by zero, then `T` has a coordinate galactic certificate with data
`(n,a,b,c,F)`.

Proof sketch: use the indicator weights `w i v = 0` for `v ∈ A i` and `w i v = 1` otherwise, with
threshold `d = 0`.  The threshold condition `∀ p, T^{⊗n} p ≠ 0 → 0 ≤ w-weight of p` is vacuous, and
`Tensor.MonomialIndependence.minimumWeightPart_indicator_eq_coordinateZeroOut` identifies the
minimum-weight part of those weights at threshold `0` with the zeroing out, which is the assumed
equality. -/
theorem coordinateGalacticCertificate_of_zeroOut {T : (∀ i, κ i) → K} {n a b c F : ℕ}
    (A : ∀ i, Finset (Fin n → κ i))
    (f : ∀ i, Fin F × MMIndex a b c i → (Fin n → κ i))
    (g : ∀ i, (Fin n → κ i) → Fin F × MMIndex a b c i)
    (hgf : ∀ i x, g i (f i x) = x)
    (heq : coordinateZeroOut (coordinatePower T n) A =
      coordinateExtend f g (coordinateDirectSum fun _ : Fin F ↦ mmCoefficients K a b c)) :
    CoordinateGalacticCertificate K T n a b c F :=
  ⟨fun i v ↦ if v ∈ A i then 0 else 1, 0, f, g, hgf, fun _ _ ↦ Nat.zero_le _, by
    rw [MonomialIndependence.minimumWeightPart_indicator_eq_coordinateZeroOut]
    exact heq⟩

/-- **The composite M1 ∘ M2**, and the statement plan item **M6** calls: a balanced zeroing out of
`T^{⊗n}` onto `F` embedded copies of `⟨a,a,a⟩` forces `F · a² ≤ Ī(T)^n`. -/
theorem sq_le_asymptoticIndependenceNumber_pow_of_zeroOut [NoZeroDivisors K] [Nontrivial K]
    {T : (∀ i, κ i) → K} {n a F : ℕ} (hn : n ≠ 0)
    (A : ∀ i, Finset (Fin n → κ i))
    (f : ∀ i, Fin F × MMIndex a a a i → (Fin n → κ i))
    (g : ∀ i, (Fin n → κ i) → Fin F × MMIndex a a a i)
    (hgf : ∀ i x, g i (f i x) = x)
    (heq : coordinateZeroOut (coordinatePower T n) A =
      coordinateExtend f g (coordinateDirectSum fun _ : Fin F ↦ mmCoefficients K a a a)) :
    (F : ℝ) * (a : ℝ) ^ 2 ≤ asymptoticIndependenceNumber T ^ n :=
  (coordinateGalacticCertificate_of_zeroOut K A f g hgf heq).sq_le_asymptoticIndependenceNumber_pow
    K hn

/-- The legwise injection of the variables of one copy of `⟨1,1,|A_Y|⟩` into the one-letter words
of `T`: the single `X` variable goes to the pivot `x₀`, the `Y` variable numbered `k` to the `k`-th
element of `A_Y`, and the `Z` variable numbered `k` to its partner `e k` in `A_Z`. -/
private noncomputable def pivotEmbed {κ : Leg → Type v} (A : ∀ i, Finset (κ i)) (x₀ : κ .X)
    (e : ↥(A .Y) ≃ ↥(A .Z)) :
    ∀ i, Fin 1 × MMIndex 1 1 (A .Y).card i → (Fin 1 → κ i)
  | .X => fun _ _ ↦ x₀
  | .Y => fun w _ ↦ ((A .Y).equivFin.symm w.2.2 : κ .Y)
  | .Z => fun w _ ↦ (e ((A .Y).equivFin.symm w.2.1) : κ .Z)

/-- The retraction of `pivotEmbed`, presented explicitly so that no choice is needed.  Words
outside the retained sets are sent to an arbitrary index, which is available because `A_Y` is
assumed nonempty. -/
private noncomputable def pivotRetract {κ : Leg → Type v} [∀ i, DecidableEq (κ i)]
    (A : ∀ i, Finset (κ i)) (e : ↥(A .Y) ≃ ↥(A .Z)) (hY : 0 < (A .Y).card) :
    ∀ i, (Fin 1 → κ i) → Fin 1 × MMIndex 1 1 (A .Y).card i
  | .X => fun _ ↦ (0, (0, 0))
  | .Y => fun u ↦ (0, (0, if h : u 0 ∈ A .Y then (A .Y).equivFin ⟨u 0, h⟩ else ⟨0, hY⟩))
  | .Z => fun u ↦ (0, (if h : u 0 ∈ A .Z then (A .Y).equivFin (e.symm ⟨u 0, h⟩) else ⟨0, hY⟩, 0))

omit [∀ i, Fintype (κ i)] in
private theorem pivotRetract_pivotEmbed (A : ∀ i, Finset (κ i)) (x₀ : κ .X)
    (e : ↥(A .Y) ≃ ↥(A .Z)) (hY : 0 < (A .Y).card)
    (i : Leg) (w : Fin 1 × MMIndex 1 1 (A .Y).card i) :
    pivotRetract A e hY i (pivotEmbed A x₀ e i w) = w := by
  obtain ⟨u, y⟩ := w
  have hu : u = 0 := Subsingleton.elim _ _
  subst hu
  cases i with
  | X =>
      obtain ⟨v, v'⟩ := y
      exact Prod.ext rfl (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))
  | Y =>
      obtain ⟨v, k⟩ := y
      have hv : v = 0 := Subsingleton.elim _ _
      subst hv
      have hmem : (((A .Y).equivFin.symm k : ↥(A .Y)) : κ .Y) ∈ A .Y :=
        ((A .Y).equivFin.symm k).2
      simp [pivotEmbed, pivotRetract, hmem]
  | Z =>
      obtain ⟨k, v⟩ := y
      have hv : v = 0 := Subsingleton.elim _ _
      subst hv
      have hmem : ((e ((A .Y).equivFin.symm k) : ↥(A .Z)) : κ .Z) ∈ A .Z :=
        (e ((A .Y).equivFin.symm k)).2
      simp [pivotEmbed, pivotRetract, hmem]

omit [∀ i, Fintype (κ i)] in
/-- The range condition of the zero-extension along `pivotEmbed` says exactly that all three
letters of a word are retained. -/
private theorem pivotEmbed_range_iff (A : ∀ i, Finset (κ i)) (x₀ : κ .X) (hx : A .X = {x₀})
    (e : ↥(A .Y) ≃ ↥(A .Z)) (hY : 0 < (A .Y).card) (p : ∀ i, Fin 1 → κ i) :
    (∀ i, pivotEmbed A x₀ e i (pivotRetract A e hY i (p i)) = p i) ↔ ∀ i, p i 0 ∈ A i := by
  have hxmem : ∀ v : κ .X, v ∈ A .X ↔ v = x₀ := by simp [hx]
  constructor
  · intro h i
    have h0 := congrFun (h i) 0
    cases i with
    | X => exact (hxmem _).mpr (h0 ▸ rfl)
    | Y => exact h0 ▸ ((A .Y).equivFin.symm _).2
    | Z => exact h0 ▸ (e ((A .Y).equivFin.symm _)).2
  · intro h i
    funext k
    rw [Subsingleton.elim k 0]
    cases i with
    | X => exact ((hxmem _).mp (h .X)).symm
    | Y => simp [pivotEmbed, pivotRetract, h .Y]
    | Z => simp [pivotEmbed, pivotRetract, h .Z]

/-- **The pivot-bijection certificate.**  Suppose the coefficient table `T` can be zeroed out to
legwise variable sets `A` in which

* the `X` leg keeps the single *pivot* variable `x₀` (`hx`),
* the retained `Y` and `Z` variables are matched by a bijection `e` (which forces `A_Y` and `A_Z`
  to have the same, nonzero, cardinality), and
* on the retained variables `T` is the indicator of the graph of `e`, i.e. `T (x₀ y z) = 1` when
  `z = e y` and `0` otherwise (`hT`).

Then the surviving terms are the `|A_Y|` terms `x₀ y (e y)`, which are one copy of `⟨1,1,|A_Y|⟩`,
and `T` has a coordinate galactic certificate with data `(n,a,b,c,F) = (1,1,1,|A_Y|,1)`.

This is the shape in which *every* barrier client discharges the nonemptiness hypothesis of AVW
Corollary 4.3, so the legwise injections `pivotEmbed`, their retractions `pivotRetract`, and the
identification of `coordinatePower T 1` with `T` are performed here once.

Proof sketch: `coordinateGalacticCertificate_of_zeroOut` reduces the claim to the equality of the
zeroing out with the zero-extension of one block of `⟨1,1,|A_Y|⟩`.  Both sides vanish unless every
letter is retained (`pivotEmbed_range_iff`), and on the retained words matrix-multiplication
compatibility of `⟨1,1,c⟩` — whose first and third equations live in `Fin 1` — is exactly
`z = e y`, which `hT` matches term by term. -/
theorem coordinateGalacticCertificate_of_pivot_bijection {T : (∀ i, κ i) → K}
    (A : ∀ i, Finset (κ i)) (x₀ : κ .X) (hx : A .X = {x₀}) (hY : (A .Y).Nonempty)
    (e : ↥(A .Y) ≃ ↥(A .Z))
    (hT : ∀ (y : κ .Y) (hy : y ∈ A .Y), ∀ z ∈ A .Z,
      T (ofLegs x₀ y z) = if z = ((e ⟨y, hy⟩ : ↥(A .Z)) : κ .Z) then 1 else 0) :
    CoordinateGalacticCertificate K T 1 1 1 (A .Y).card 1 := by
  classical
  have hcpos : 0 < (A .Y).card := Finset.card_pos.mpr hY
  refine coordinateGalacticCertificate_of_zeroOut K
    (fun i ↦ Finset.univ.filter fun u : Fin 1 → κ i ↦ u 0 ∈ A i)
    (pivotEmbed A x₀ e) (pivotRetract A e hcpos) (pivotRetract_pivotEmbed A x₀ e hcpos) ?_
  have hBmem : ∀ p : ∀ i, Fin 1 → κ i,
      (∀ i, p i ∈ Finset.univ.filter fun u : Fin 1 → κ i ↦ u 0 ∈ A i) ↔ ∀ i, p i 0 ∈ A i := by
    intro p; simp
  funext p
  rw [Tensor.coordinateZeroOut, Tensor.coordinateExtend]
  by_cases hp : ∀ i, p i 0 ∈ A i
  · rw [if_pos ((hBmem p).mpr hp),
      if_pos ((pivotEmbed_range_iff A x₀ hx e hcpos p).mpr hp), Tensor.coordinateDirectSum,
      if_pos fun i ↦ Subsingleton.elim _ _]
    have hlegs : (fun i ↦ p i 0) = ofLegs (p .X 0) (p .Y 0) (p .Z 0) := by
      funext i; cases i <;> rfl
    have hX : p .X 0 = x₀ := by
      have := hp .X; rw [hx] at this; simpa using this
    rw [coordinatePower_apply, Fin.prod_univ_one, hlegs, hX,
      hT (p .Y 0) (hp .Y) (p .Z 0) (hp .Z), mmCoefficients]
    have hcompat : MMCompatible (fun i ↦ (pivotRetract A e hcpos i (p i)).2) ↔
        p .Z 0 = ((e ⟨p .Y 0, hp .Y⟩ : ↥(A .Z)) : κ .Z) := by
      constructor
      · rintro ⟨-, h2, -⟩
        have h2' : (A .Y).equivFin ⟨p .Y 0, hp .Y⟩ =
            (A .Y).equivFin (e.symm ⟨p .Z 0, hp .Z⟩) := by
          simpa [pivotRetract, hp .Y, hp .Z] using h2
        have := congrArg (fun z ↦ ((e z : ↥(A .Z)) : κ .Z)) ((A .Y).equivFin.injective h2')
        simpa using this.symm
      · intro h
        refine ⟨Subsingleton.elim _ _, ?_, Subsingleton.elim _ _⟩
        have hz : (⟨p .Z 0, hp .Z⟩ : ↥(A .Z)) = e ⟨p .Y 0, hp .Y⟩ := Subtype.ext h
        simp [pivotRetract, hp .Y, hp .Z, hz]
    rw [if_congr hcompat rfl rfl]
  · rw [if_neg fun h ↦ hp ((hBmem p).mp h),
      if_neg fun h ↦ hp ((pivotEmbed_range_iff A x₀ hx e hcpos p).mp h)]

end BalancedCertificate

/-! ## Composing a certificate with a zeroing out of the source table

A laser extraction is usually performed on a *simplified* table: the classical
Coppersmith--Winograd analyses delete the extreme coordinate of `CW_q` before hashing, and the
extraction certificate they produce is a certificate for that smaller table.  Since a coordinate
galactic certificate is a monomial degeneration of a power of the table read in the table's own
variables, and a zeroing out is itself the minimum-weight part of indicator weights, the two
compose: a certificate for `T|_{A₀}` is a certificate for `T`.
-/

section ZeroOutSource

open MonomialIndependence

variable (K : Type u) [CommSemiring K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

omit [∀ i, Fintype (κ i)] in
/-- **A coordinate galactic certificate for a zeroing out is a certificate for the source table.**
If the table `T`, zeroed out to the legwise variable sets `A₀`, admits a coordinate galactic
certificate with data `(n,a,b,c,F)`, then so does `T` itself.

This is what lets a laser extraction be run on a simplified table --- for the generalized
Coppersmith--Winograd family, on the three middle constituents left after deleting the coordinate
`q + 1` --- and its certificate be read as a certificate for the full table.

Proof sketch: let `B i` be the words all of whose letters lie in `A₀ i`, so that
`(T|_{A₀})^{⊗n} = (T^{⊗n})|_B` (`Tensor.coordinatePower_coordinateZeroOut`).  Add to the given
weights `w` the indicator penalty `d + 1` on every leg word outside `B`.  A word all of whose three
legs lie in `B` keeps its old total weight and its old coefficient; any other word acquires total
weight at least `d + 1 > d` and is therefore dropped by the new minimum-weight part --- which is
exactly what the zeroing out did to it.  The two minimum-weight parts thus agree, and the threshold
condition is inherited on `B` and automatic off it. -/
theorem CoordinateGalacticCertificate.of_coordinateZeroOut {T : (∀ i, κ i) → K}
    {A₀ : ∀ i, Finset (κ i)} {n a b c F : ℕ}
    (h : CoordinateGalacticCertificate K (coordinateZeroOut T A₀) n a b c F) :
    CoordinateGalacticCertificate K T n a b c F := by
  classical
  obtain ⟨w, d, f, g, hgf, hmin, heq⟩ := h
  set B : ∀ i, Finset (Fin n → κ i) := fun i ↦ Fintype.piFinset fun _ : Fin n ↦ A₀ i with hBdef
  set w' : ∀ i, (Fin n → κ i) → ℕ :=
    fun i v ↦ w i v + (if v ∈ B i then 0 else d + 1) with hw'def
  have hpow : coordinatePower (coordinateZeroOut T A₀) n =
      coordinateZeroOut (coordinatePower T n) B :=
    coordinatePower_coordinateZeroOut T A₀ n
  have hweq : ∀ p : ∀ i, Fin n → κ i, (∀ i, p i ∈ B i) →
      monomialTotalWeight w' p = monomialTotalWeight w p := by
    intro p hp
    simp only [monomialTotalWeight, hw'def, if_pos (hp Leg.X), if_pos (hp Leg.Y),
      if_pos (hp Leg.Z), Nat.add_zero]
  have hwout : ∀ p : ∀ i, Fin n → κ i, ¬ (∀ i, p i ∈ B i) → d < monomialTotalWeight w' p := by
    intro p hp
    rw [not_forall] at hp
    obtain ⟨i, hi⟩ := hp
    have hi' : d + 1 ≤ w' i (p i) := by
      simp only [hw'def, if_neg hi]
      omega
    cases i <;> · simp only [monomialTotalWeight] at hi' ⊢; omega
  refine ⟨w', d, f, g, hgf, ?_, ?_⟩
  · intro p hp
    by_cases hmem : ∀ i, p i ∈ B i
    · rw [hweq p hmem]
      refine hmin p ?_
      rw [hpow, coordinateZeroOut_of_mem hmem]
      exact hp
    · exact (hwout p hmem).le
  · rw [← heq]
    funext p
    by_cases hmem : ∀ i, p i ∈ B i
    · simp only [minimumWeightPart, hweq p hmem, hpow, coordinateZeroOut_of_mem hmem]
    · have hne : monomialTotalWeight w' p ≠ d := (hwout p hmem).ne'
      simp only [minimumWeightPart, if_neg hne]
      rcases eq_or_ne (monomialTotalWeight w p) d with he | he
      · rw [if_pos he, hpow, coordinateZeroOut_of_notMem hmem]
      · rw [if_neg he]

end ZeroOutSource

end AlgebraicComplexity
