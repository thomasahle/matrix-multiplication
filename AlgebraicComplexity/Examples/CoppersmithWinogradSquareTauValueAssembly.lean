/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSquareAssembly
import AlgebraicComplexity.Examples.CoppersmithWinogradSquareHashing
import AlgebraicComplexity.MatrixMultiplication.CyclicValueTensor
import AlgebraicComplexity.MatrixMultiplication.TauValueCalculus
import AlgebraicComplexity.MatrixMultiplication.TauValueIndexedDirectSum

/-!
# `τ`-value assembly after outer hashing of the CW square

This module is the value-facing bridge for the outer Coppersmith--Winograd square construction.
The hashing layer already restricts a concrete tensor power to a **genuine indexed direct sum**
of isolated constituents.  If each constituent carries a power-one `TauValueCertificate`, this
file combines those certificates, transports them through the hashing restriction, and records
the result as a certificate of the original square tensor at the correct outer power.

The construction is deliberately agnostic about how a constituent certificate was obtained.
It therefore accepts exact restrictions, polynomial degenerations, or future stronger leaf
procedures through the common `TauValueCertificate` interface.  In particular, the modern
symmetric `(112)` extraction can be plugged in without encoding "zeroing" into the definition of
value.

No entropy estimate, constituent formula, or numerical parameter choice occurs here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u w

/-- The finite type of marked CW-square addresses retained by one outer hashing seed. -/
noncomputable abbrev CWSquareOuterSurvivor
    {R : Type w} [Field R]
    (H : PartitionHashEncoding (R := R) cwSquareSupport)
    (a b c d k : ℕ) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (cwSquareDepth a b c d k + 1))) :=
  H.markedLegwiseIsolatedPowerAddresses
    (cwSquareDepth a b c d k)
    (cwSquareAmbientWords a b c d k)
    (cwSquareMarkedWords a b c d k) B seed

noncomputable section

variable (K : Type u) [CommRing K]

/-! ## One grouped constituent -/

/-- Combine an arbitrary cyclic `(112)` degeneration of the required power with the ordinary
matrix-multiplication part of one grouped CW-square constituent.

The inner certificate may itself have many unequal rectangular outputs; their dimensions are
multiplied by the common ordinary square side.  Thus this construction is not specialized to the
current equal-square symmetric leaf.

Proof sketch: use the trivial power-one certificate of the ordinary matrix tensor and
`TauValueCertificate.externalOfDegenerates` to form the Cartesian product with the inner target
family.  The checked grouped-chunk restriction supplies the source transport. -/
noncomputable def cwSquareGroupedChunkTauValueCertificate
    (τ : ℝ) (q a b c d k : ℕ)
    (hq : 0 < q) (hordinary : 0 < cwSquareStride a b c 0)
    (hd : 0 < d) (hk : 0 < k)
    (inner : CyclicDegenerationCertificate K
      (cw112PartitionedTensor K q).realize τ)
    (hinnerPower : inner.power = d * k) :
    TauValueCertificate K
      (cwSquareGroupedChunkProduct (K := K) q a b c d k hordinary hk) := by
  let D := cwSquareOrdinaryDimension q b c k
  have hD : 0 < D := by
    unfold D cwSquareOrdinaryDimension
    positivity
  let ordinaryCertificate :=
    TauValueCertificate.matrixMultiplication K hD hD hD
  let innerCertificate : TauValueCertificate K
      (cyclicPowerProduct K (cw112PartitionedTensor K q).realize inner.power) :=
    { power := 1
      copies := inner.copies
      xSize := inner.xSize
      ySize := inner.ySize
      zSize := inner.zSize
      power_pos := Nat.one_pos
      copies_pos := inner.copies_pos
      xSize_pos := inner.xSize_pos
      ySize_pos := inner.ySize_pos
      zSize_pos := inner.zSize_pos
      degenerates :=
        (PolynomialDegenerates.of_restricts
          (Isomorphic.power_one
            (cyclicPowerProduct K (cw112PartitionedTensor K q).realize inner.power)).restricts).trans
          inner.degenerates }
  have hproduct : TauValueCertificate K
      (Tensor.external
        (AlgebraicComplexity.matrixMultiplication (K := K) D D D)
        (cyclicPowerProduct K (cw112PartitionedTensor K q).realize inner.power)) :=
    TauValueCertificate.externalOfDegenerates K
      ordinaryCertificate.xSize ordinaryCertificate.ySize ordinaryCertificate.zSize
      innerCertificate.xSize innerCertificate.ySize innerCertificate.zSize
      Nat.one_pos ordinaryCertificate.copies_pos innerCertificate.copies_pos
      ordinaryCertificate.xSize_pos ordinaryCertificate.ySize_pos
      ordinaryCertificate.zSize_pos innerCertificate.xSize_pos
      innerCertificate.ySize_pos innerCertificate.zSize_pos
      ordinaryCertificate.degenerates innerCertificate.degenerates
  have hsplit : Restricts
      (cwSquareGroupedChunkProduct (K := K) q a b c d k hordinary hk)
      (Tensor.external
        (AlgebraicComplexity.matrixMultiplication (K := K) D D D)
        (cyclicPowerProduct K (cw112PartitionedTensor K q).realize inner.power)) := by
    exact (cwSquareGroupedChunkProduct_restricts_ordinaryCyclic (K := K)
      q a b c hordinary hd hk).trans
        ((Isomorphic.refl
          (AlgebraicComplexity.matrixMultiplication (K := K) D D D)).external
          (Isomorphic.cyclicPowerProduct_congr (K := K)
            (cw112PartitionedTensor K q).realize hinnerPower.symm)).restricts
  exact TauValueCertificate.ofRestricts hsplit hproduct

/-- A grouped constituent assembled from a cyclic leaf has source power one. -/
@[simp] theorem cwSquareGroupedChunkTauValueCertificate_power
    (τ : ℝ) (q a b c d k : ℕ)
    (hq : 0 < q) (hordinary : 0 < cwSquareStride a b c 0)
    (hd : 0 < d) (hk : 0 < k)
    (inner : CyclicDegenerationCertificate K
      (cw112PartitionedTensor K q).realize τ)
    (hinnerPower : inner.power = d * k) :
    (cwSquareGroupedChunkTauValueCertificate
      K τ q a b c d k hq hordinary hd hk inner hinnerPower).power = 1 := by
  unfold cwSquareGroupedChunkTauValueCertificate
  rfl

/-- The grouped constituent term factors into its ordinary matrix contribution and the inner
cyclic certificate's unnormalized matrix-volume sum.

The inner cyclic *term* is the `(3·power)`th root of the second factor.  Keeping the factor
unnormalized here is essential: the outer certificate subsequently takes the root determined by
the complete square-word length.

Proof sketch: unfold only the numerical fields of the product certificate, cancel its power-one
normalization, and apply the Cartesian volume-sum factorization from `TauValueCalculus`. -/
theorem cwSquareGroupedChunkTauValueCertificate_term
    (τ σ : ℝ) (q a b c d k : ℕ)
    (hq : 0 < q) (hordinary : 0 < cwSquareStride a b c 0)
    (hd : 0 < d) (hk : 0 < k)
    (inner : CyclicDegenerationCertificate K
      (cw112PartitionedTensor K q).realize τ)
    (hinnerPower : inner.power = d * k) :
    (cwSquareGroupedChunkTauValueCertificate
      K τ q a b c d k hq hordinary hd hk inner hinnerPower).term σ =
      (((cwSquareOrdinaryDimension q b c k *
          cwSquareOrdinaryDimension q b c k *
          cwSquareOrdinaryDimension q b c k : ℕ) : ℝ) ^ σ) *
        matrixMultiplicationVolumePowerSum
          inner.xSize inner.ySize inner.zSize σ := by
  let D := cwSquareOrdinaryDimension q b c k
  change tauValueTerm σ 1
      (fun i : Fin (1 * inner.copies) ↦
        D * inner.xSize (finProdFinEquiv.symm i).2)
      (fun i : Fin (1 * inner.copies) ↦
        D * inner.ySize (finProdFinEquiv.symm i).2)
      (fun i : Fin (1 * inner.copies) ↦
        D * inner.zSize (finProdFinEquiv.symm i).2) = _
  unfold tauValueTerm
  rw [Nat.cast_one, inv_one, Real.rpow_one,
    matrixMultiplicationVolumePowerSum_finProdFinEquiv
      (fun _ : Fin 1 ↦ D) (fun _ : Fin 1 ↦ D) (fun _ : Fin 1 ↦ D)
      inner.xSize inner.ySize inner.zSize,
    matrixMultiplicationVolumePowerSum_const]
  simp only [Nat.cast_one, one_mul, D, Nat.cast_mul]

/-! ## Transport to every isolated outer constituent -/

/-- Every address retained by outer hashing inherits the grouped-chunk value certificate.

Proof sketch: inverse-decode the selected address to a marked supported word.  The constituent at
that word is isomorphic to the explicit grouped chunk product, so value-certificate monotonicity
transports the grouped certificate without changing any numerical target data. -/
noncomputable def cwSquareOuterSurvivorTauValueCertificate
    {R : Type w} [Field R]
    (H : PartitionHashEncoding (R := R) cwSquareSupport)
    (τ : ℝ) (q a b c d k : ℕ)
    (hq : 0 < q) (hordinary : 0 < cwSquareStride a b c 0)
    (hd : 0 < d) (hk : 0 < k)
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (cwSquareDepth a b c d k + 1)))
    (s : CWSquareOuterSurvivor H a b c d k B seed)
    (inner : CyclicDegenerationCertificate K
      (cw112PartitionedTensor K q).realize τ)
    (hinnerPower : inner.power = d * k) :
    TauValueCertificate K
      ((cwSquareAmbientPartitionedPower K q a b c d k).constituent s.1) := by
  have hexists :=
    H.exists_markedSourceWord_of_mem_markedLegwiseIsolatedPowerAddresses
      (cwSquareDepth a b c d k)
      (cwSquareAmbientWords a b c d k)
      (cwSquareMarkedWords a b c d k) B seed s.2
  let word := Classical.choose hexists
  have hword : word ∈ cwSquareMarkedWords a b c d k :=
    (Classical.choose_spec hexists).1
  have haddress : PartitionHashEncoding.supportWordAddress
      (cwSquareDepth a b c d k) word = s.1 :=
    (Classical.choose_spec hexists).2
  have hisomorphic : Isomorphic
      ((cwSquareAmbientPartitionedPower K q a b c d k).constituent s.1)
      (cwSquareGroupedChunkProduct (K := K) q a b c d k hordinary hk) := by
    change Isomorphic
      (((cwSquarePartitionedTensor K q).positivePower
        (cwSquareDepth a b c d k)).constituent s.1) _
    rw [← haddress]
    exact cwSquareMarkedWord_constituent_isomorphic_chunks
      (K := K) q hordinary hd hk word hword
  exact TauValueCertificate.ofIsomorphic hisomorphic
    (cwSquareGroupedChunkTauValueCertificate
      K τ q a b c d k hq hordinary hd hk inner hinnerPower)

/-- Transport to a selected address preserves the grouped certificate's power one. -/
@[simp] theorem cwSquareOuterSurvivorTauValueCertificate_power
    {R : Type w} [Field R]
    (H : PartitionHashEncoding (R := R) cwSquareSupport)
    (τ : ℝ) (q a b c d k : ℕ)
    (hq : 0 < q) (hordinary : 0 < cwSquareStride a b c 0)
    (hd : 0 < d) (hk : 0 < k)
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (cwSquareDepth a b c d k + 1)))
    (s : CWSquareOuterSurvivor H a b c d k B seed)
    (inner : CyclicDegenerationCertificate K
      (cw112PartitionedTensor K q).realize τ)
    (hinnerPower : inner.power = d * k) :
    (cwSquareOuterSurvivorTauValueCertificate
      K H τ q a b c d k hq hordinary hd hk B seed s inner hinnerPower).power = 1 := by
  unfold cwSquareOuterSurvivorTauValueCertificate
  exact cwSquareGroupedChunkTauValueCertificate_power
    K τ q a b c d k hq hordinary hd hk inner hinnerPower

/-- Transport to a selected address preserves the grouped certificate's numerical term. -/
theorem cwSquareOuterSurvivorTauValueCertificate_term
    {R : Type w} [Field R]
    (H : PartitionHashEncoding (R := R) cwSquareSupport)
    (τ σ : ℝ) (q a b c d k : ℕ)
    (hq : 0 < q) (hordinary : 0 < cwSquareStride a b c 0)
    (hd : 0 < d) (hk : 0 < k)
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (cwSquareDepth a b c d k + 1)))
    (s : CWSquareOuterSurvivor H a b c d k B seed)
    (inner : CyclicDegenerationCertificate K
      (cw112PartitionedTensor K q).realize τ)
    (hinnerPower : inner.power = d * k) :
    (cwSquareOuterSurvivorTauValueCertificate
      K H τ q a b c d k hq hordinary hd hk B seed s inner hinnerPower).term σ =
      (cwSquareGroupedChunkTauValueCertificate
        K τ q a b c d k hq hordinary hd hk inner hinnerPower).term σ := by
  unfold cwSquareOuterSurvivorTauValueCertificate
  rfl

/-- Assemble arbitrary power-one certificates for all isolated outer constituents into one
certificate of the original CW square.

The resulting certificate records source power `cwSquareDepth a b c d k + 1`, exactly the tensor
power on which outer hashing operates.

Proof sketch: combine the constituent certificates over their genuine indexed direct sum, pull
the result back through `cwSquarePower_restricts_markedIndexedDirectSum`, and reinterpret a
power-one certificate of the displayed tensor power as a certificate of the base square tensor.
-/
noncomputable def cwSquareTauValueCertificateOfOuterSurvivors
    {R : Type w} [Field R] [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) cwSquareSupport)
    (q a b c d k : ℕ) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cwSquareDepth a b c d k + 1)))
    [Nonempty (CWSquareOuterSurvivor H a b c d k B seed)]
    (certificate : ∀ s : CWSquareOuterSurvivor H a b c d k B seed,
      TauValueCertificate K
        ((cwSquareAmbientPartitionedPower K q a b c d k).constituent s.1))
    (hpower : ∀ s, (certificate s).power = 1) :
    TauValueCertificate K (cwSquarePartitionedTensor K q).realize := by
  let directCertificate :=
    TauValueCertificate.indexedDirectSumPowerOne certificate hpower
  let powerCertificate : TauValueCertificate K
      (Tensor.power (cwSquarePartitionedTensor K q).realize
        (cwSquareDepth a b c d k + 1)) :=
    TauValueCertificate.ofRestricts
      (cwSquarePower_restricts_markedIndexedDirectSum
        K q a b c d k H B hB seed)
      directCertificate
  exact TauValueCertificate.ofPowerOneOnPower
    (cwSquareDepth a b c d k + 1) (Nat.succ_pos _) powerCertificate rfl

/-- The assembled certificate has exactly the outer hashing power. -/
@[simp] theorem cwSquareTauValueCertificateOfOuterSurvivors_power
    {R : Type w} [Field R] [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) cwSquareSupport)
    (q a b c d k : ℕ) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cwSquareDepth a b c d k + 1)))
    [Nonempty (CWSquareOuterSurvivor H a b c d k B seed)]
    (certificate : ∀ s : CWSquareOuterSurvivor H a b c d k B seed,
      TauValueCertificate K
        ((cwSquareAmbientPartitionedPower K q a b c d k).constituent s.1))
    (hpower : ∀ s, (certificate s).power = 1) :
    (cwSquareTauValueCertificateOfOuterSurvivors
      K H q a b c d k B hB seed certificate hpower).power =
        cwSquareDepth a b c d k + 1 := by
  rfl

/-- **Exact finite value assembled by outer hashing.**  The certificate term is the outer-power
root of the sum of all isolated constituent terms.

This is the finite form of value superadditivity needed by the CW-square proof.  It applies only
after hashing has produced a genuine direct sum, so it requires no power expansion of a formal
binary tensor sum.

Proof sketch: `indexedDirectSumPowerOne_term` adds the constituent terms exactly; restriction
transport preserves the target family; `term_ofPowerOneOnPower` supplies the final outer root. -/
theorem cwSquareTauValueCertificateOfOuterSurvivors_term
    {R : Type w} [Field R] [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) cwSquareSupport)
    (q a b c d k : ℕ) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cwSquareDepth a b c d k + 1)))
    [Nonempty (CWSquareOuterSurvivor H a b c d k B seed)]
    (certificate : ∀ s : CWSquareOuterSurvivor H a b c d k B seed,
      TauValueCertificate K
        ((cwSquareAmbientPartitionedPower K q a b c d k).constituent s.1))
    (hpower : ∀ s, (certificate s).power = 1) (τ : ℝ) :
    (cwSquareTauValueCertificateOfOuterSurvivors
      K H q a b c d k B hB seed certificate hpower).term τ =
      (∑ s, (certificate s).term τ) ^
        (((cwSquareDepth a b c d k + 1 : ℕ) : ℝ)⁻¹) := by
  change tauValueTerm τ (cwSquareDepth a b c d k + 1)
      (TauValueCertificate.indexedDirectSumPowerOne certificate hpower).xSize
      (TauValueCertificate.indexedDirectSumPowerOne certificate hpower).ySize
      (TauValueCertificate.indexedDirectSumPowerOne certificate hpower).zSize = _
  unfold tauValueTerm
  congr 1
  rw [TauValueCertificate.matrixMultiplicationVolumePowerSum_indexedDirectSumPowerOne]
  apply Finset.sum_congr rfl
  intro s _hs
  rw [TauValueCertificate.term, tauValueTerm, hpower s,
    Nat.cast_one, inv_one, Real.rpow_one]

/-! ## Complete finite square certificate from a cyclic inner leaf -/

/-- Combine one cyclic inner `(112)` certificate with every survivor of one outer hash seed,
obtaining a value certificate of the original CW square.

The hypothesis `inner.power = d*k` is the sole synchronization condition between the inner and
outer profiles.  No formula for `d`, entropy, or matrix dimensions is built into this semantic
constructor. -/
noncomputable def cwSquareTauValueCertificateOfCyclicInner
    {R : Type w} [Field R] [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) cwSquareSupport)
    (τ : ℝ) (q a b c d k : ℕ)
    (hq : 0 < q) (hordinary : 0 < cwSquareStride a b c 0)
    (hd : 0 < d) (hk : 0 < k)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cwSquareDepth a b c d k + 1)))
    [Nonempty (CWSquareOuterSurvivor H a b c d k B seed)]
    (inner : CyclicDegenerationCertificate K
      (cw112PartitionedTensor K q).realize τ)
    (hinnerPower : inner.power = d * k) :
    TauValueCertificate K (cwSquarePartitionedTensor K q).realize :=
  cwSquareTauValueCertificateOfOuterSurvivors
    K H q a b c d k B hB seed
    (fun s ↦ cwSquareOuterSurvivorTauValueCertificate
      K H τ q a b c d k hq hordinary hd hk B seed s inner hinnerPower)
    (fun s ↦ cwSquareOuterSurvivorTauValueCertificate_power
      K H τ q a b c d k hq hordinary hd hk B seed s inner hinnerPower)

/-- The complete finite certificate records the exact outer square-word power. -/
@[simp] theorem cwSquareTauValueCertificateOfCyclicInner_power
    {R : Type w} [Field R] [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) cwSquareSupport)
    (τ : ℝ) (q a b c d k : ℕ)
    (hq : 0 < q) (hordinary : 0 < cwSquareStride a b c 0)
    (hd : 0 < d) (hk : 0 < k)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cwSquareDepth a b c d k + 1)))
    [Nonempty (CWSquareOuterSurvivor H a b c d k B seed)]
    (inner : CyclicDegenerationCertificate K
      (cw112PartitionedTensor K q).realize τ)
    (hinnerPower : inner.power = d * k) :
    (cwSquareTauValueCertificateOfCyclicInner
      K H τ q a b c d k hq hordinary hd hk B hB seed inner hinnerPower).power =
        cwSquareDepth a b c d k + 1 := by
  unfold cwSquareTauValueCertificateOfCyclicInner
  exact cwSquareTauValueCertificateOfOuterSurvivors_power
    K H q a b c d k B hB seed _ _

/-- **Exact finite CW-square value formula with a semantic cyclic leaf.**

The base inside the outer root is

`outer survivors × ordinary-volume^σ × inner volume power sum`.

This is the finite algebraic identity needed before applying separate asymptotic lower bounds to
the outer survivor count and the inner cyclic term.

Proof sketch: apply the generic outer term formula, replace every selected constituent term by
the common grouped term, sum the constant family, and use the grouped Cartesian factorization. -/
theorem cwSquareTauValueCertificateOfCyclicInner_term
    {R : Type w} [Field R] [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) cwSquareSupport)
    (τ σ : ℝ) (q a b c d k : ℕ)
    (hq : 0 < q) (hordinary : 0 < cwSquareStride a b c 0)
    (hd : 0 < d) (hk : 0 < k)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cwSquareDepth a b c d k + 1)))
    [Nonempty (CWSquareOuterSurvivor H a b c d k B seed)]
    (inner : CyclicDegenerationCertificate K
      (cw112PartitionedTensor K q).realize τ)
    (hinnerPower : inner.power = d * k) :
    (cwSquareTauValueCertificateOfCyclicInner
      K H τ q a b c d k hq hordinary hd hk B hB seed inner hinnerPower).term σ =
      (((Fintype.card (CWSquareOuterSurvivor H a b c d k B seed) : ℕ) : ℝ) *
        ((((cwSquareOrdinaryDimension q b c k *
            cwSquareOrdinaryDimension q b c k *
            cwSquareOrdinaryDimension q b c k : ℕ) : ℝ) ^ σ) *
          matrixMultiplicationVolumePowerSum
            inner.xSize inner.ySize inner.zSize σ)) ^
        (((cwSquareDepth a b c d k + 1 : ℕ) : ℝ)⁻¹) := by
  unfold cwSquareTauValueCertificateOfCyclicInner
  rw [cwSquareTauValueCertificateOfOuterSurvivors_term]
  congr 1
  simp_rw [cwSquareOuterSurvivorTauValueCertificate_term]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    cwSquareGroupedChunkTauValueCertificate_term]

end

end AlgebraicComplexity.Examples
