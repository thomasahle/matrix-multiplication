/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSquareCounting
import AlgebraicComplexity.Examples.CoppersmithWinogradSquareOrdinarySymmetry
import AlgebraicComplexity.Examples.CoppersmithWinograd112Partition
import AlgebraicComplexity.MatrixMultiplication.PartitionedTypeAssembly
import AlgebraicComplexity.MatrixMultiplication.PartitionedTypeExtraction
import AlgebraicComplexity.MatrixMultiplication.CyclicProductPowerCoherence

/-!
# Grouping constituents in a typed Coppersmith--Winograd square word

The outer hashing argument retains words of one symmetric joint type on the fifteen constituents
of `CW_q ⊗ CW_q`.  Subsequent value estimates are easiest for one ordered representative: all
ordinary constituents first, followed by equal consecutive chunks of the exceptional `112`,
`211`, and `121` orientations.  This order matches `cyclicPowerProduct`: identity, `cycle`, then
`cycle⁻¹`.

This file constructs that representative, proves its exact joint type, and uses the generic
position-relabeling theorem to show that every marked word indexes an isomorphic constituent.
It contains no entropy estimates and no numerical parameter choices.  The next assembly layer
can therefore reason about the four consecutive chunks without losing any of the copies retained
by hashing.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## Named support letters -/

/-- The canonical `112` support letter. -/
abbrev cwSquare112S : CWSquareSupport :=
  ⟨cwSquareAddress 1 1 2, by
    rw [cwSquareSupport_eq_antidiagonal]
    decide⟩

/-- The cyclic `121` support letter. -/
abbrev cwSquare121S : CWSquareSupport :=
  ⟨cwSquareAddress 1 2 1, by
    rw [cwSquareSupport_eq_antidiagonal]
    decide⟩

/-- The cyclic `211` support letter. -/
abbrev cwSquare211S : CWSquareSupport :=
  ⟨cwSquareAddress 2 1 1, by
    rw [cwSquareSupport_eq_antidiagonal]
    decide⟩

/-! ## One grouped representative -/

/-- A chosen marked word containing only the ordinary `004`, `013`, and `022` classes. -/
noncomputable def cwSquareOrdinaryWord
    (a b c k : ℕ) (hordinary : 0 < cwSquareStride a b c 0) (hk : 0 < k) :
    PositiveWord CWSquareSupport (cwSquareDepth a b c 0 k) :=
  (cwSquareMarkedWords_nonempty hordinary hk).choose

/-- The chosen ordinary word has the advertised joint multiplicities. -/
theorem cwSquareOrdinaryWord_type
    (a b c k : ℕ) (hordinary : 0 < cwSquareStride a b c 0) (hk : 0 < k) :
    WordType.multiplicity
        (positiveWordEquiv CWSquareSupport (cwSquareDepth a b c 0 k)
          (cwSquareOrdinaryWord a b c k hordinary hk)) =
      cwSquareNaturalType a b c 0 k := by
  exact mem_positiveTypeClass.mp
    (cwSquareMarkedWords_nonempty hordinary hk).choose_spec

/-- Recursive parameter for a nonempty chunk containing `d*k` copies of one exceptional
orientation. -/
def cwSquareExceptionalDepth (d k : ℕ) : ℕ := d * k - 1

/-- A positive exceptional chunk has exactly `d*k` letters. -/
theorem cwSquareExceptionalDepth_add_one
    {d k : ℕ} (hd : 0 < d) (hk : 0 < k) :
    cwSquareExceptionalDepth d k + 1 = d * k := by
  unfold cwSquareExceptionalDepth
  have hproduct : 0 < d * k := Nat.mul_pos hd hk
  omega

/-- Recursive parameter of the raw four-chunk word before transporting it to the standard
`cwSquareDepth` expression. -/
abbrev cwSquareGroupedRawDepth (a b c d k : ℕ) : ℕ :=
  ((cwSquareDepth a b c 0 k + cwSquareExceptionalDepth d k + 1) +
      cwSquareExceptionalDepth d k + 1) +
    cwSquareExceptionalDepth d k + 1

/-- Appending the ordinary chunk and the three exceptional orientation chunks. -/
noncomputable abbrev cwSquareGroupedWordRaw
    (a b c d k : ℕ)
    (hordinary : 0 < cwSquareStride a b c 0) (hk : 0 < k) :
    PositiveWord CWSquareSupport (cwSquareGroupedRawDepth a b c d k) :=
  positiveWordAppend
    (positiveWordAppend
      (positiveWordAppend
        (cwSquareOrdinaryWord a b c k hordinary hk)
        (cwSquareExceptionalDepth d k)
        (positiveWordConst cwSquare112S (cwSquareExceptionalDepth d k)))
      (cwSquareExceptionalDepth d k)
      (positiveWordConst cwSquare211S (cwSquareExceptionalDepth d k)))
    (cwSquareExceptionalDepth d k)
    (positiveWordConst cwSquare121S (cwSquareExceptionalDepth d k))

/-- The raw grouped-word parameter is the standard depth of the full symmetric profile.

Proof sketch: the ordinary chunk contributes `(3a+6b+3c)k` letters and each exceptional
orientation contributes `dk`; their sum is `(3a+6b+3c+3d)k`. -/
theorem cwSquareGroupedRawDepth_eq
    {a b c d k : ℕ}
    (hordinary : 0 < cwSquareStride a b c 0)
    (hd : 0 < d) (hk : 0 < k) :
    cwSquareGroupedRawDepth a b c d k = cwSquareDepth a b c d k := by
  have hfull : 0 < cwSquareStride a b c d := by
    unfold cwSquareStride at hordinary ⊢
    omega
  have hordinaryDepth := cwSquareDepth_add_one hordinary hk
  have hexceptionalDepth := cwSquareExceptionalDepth_add_one hd hk
  have hfullDepth := cwSquareDepth_add_one hfull hk
  have hmass :
      cwSquareStride a b c d * k =
        cwSquareStride a b c 0 * k + d * k + d * k + d * k := by
    unfold cwSquareStride
    ring
  unfold cwSquareGroupedRawDepth
  omega

/-- The ordered representative, transported to the same recursive depth used by outer hashing. -/
noncomputable def cwSquareGroupedWord
    (a b c d k : ℕ)
    (hordinary : 0 < cwSquareStride a b c 0)
    (hd : 0 < d) (hk : 0 < k) :
    PositiveWord CWSquareSupport (cwSquareDepth a b c d k) :=
  positiveWordCast (cwSquareGroupedRawDepth_eq hordinary hd hk)
    (cwSquareGroupedWordRaw a b c d k hordinary hk)

/-- The grouped representative has exactly the full symmetric joint profile.

Proof sketch: multiplicity is additive under each of the three concatenations.  The ordinary
prefix has the profile with exceptional count zero, and the three constant suffixes contribute
`dk` at `112`, `211`, and `121` respectively.  A finite support case split then gives the stated
profile on all fifteen addresses. -/
theorem cwSquareGroupedWord_type
    {a b c d k : ℕ}
    (hordinary : 0 < cwSquareStride a b c 0)
    (hd : 0 < d) (hk : 0 < k) :
    WordType.multiplicity
        (positiveWordEquiv CWSquareSupport (cwSquareDepth a b c d k)
          (cwSquareGroupedWord a b c d k hordinary hd hk)) =
      cwSquareNaturalType a b c d k := by
  rw [cwSquareGroupedWord,
    WordType.multiplicity_positiveWordCast]
  unfold cwSquareGroupedWordRaw
  unfold cwSquareGroupedRawDepth
  rw [WordType.multiplicity_positiveWordAppend,
    WordType.multiplicity_positiveWordAppend,
    WordType.multiplicity_positiveWordAppend,
    cwSquareOrdinaryWord_type,
    WordType.multiplicity_positiveWordConst,
    WordType.multiplicity_positiveWordConst,
    WordType.multiplicity_positiveWordConst]
  rw [cwSquareExceptionalDepth_add_one hd hk]
  funext s
  rcases s with ⟨s, hs⟩
  rw [cwSquareSupport_eq_antidiagonal] at hs
  simp only [cwSquareAntidiagonal, Finset.mem_insert,
    Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [cwSquareNaturalType, cwSquareClassCount,
      cwSquare004Orbit, cwSquare013Orbit, cwSquare022Orbit,
      cwSquare112Orbit, cwSquareAddress_eq_iff]

/-! ## Tensor decomposition of the grouped representative -/

/-- Tensor selected by the ordinary prefix of the grouped square word. -/
noncomputable abbrev cwSquareOrdinaryChunkTensor
    {K : Type u} [CommRing K]
    (q a b c k : ℕ)
    (hordinary : 0 < cwSquareStride a b c 0) (hk : 0 < k) :=
  (cwSquarePartitionedTensor K q).positiveSupportWordTensor
    (cwSquareDepth a b c 0 k)
    (cwSquareOrdinaryWord a b c k hordinary hk)

/-- Common side length obtained by multiplying all ordinary constituent dimensions in the
symmetric profile: each leg sees two `013` orientations and one `022` orientation. -/
def cwSquareOrdinaryDimension (q b c k : ℕ) : ℕ :=
  (2 * q) ^ (2 * b * k) * (q ^ 2 + 2) ^ (c * k)

/-- Elementary power identity used after enumerating any of the three symmetric ordinary
dimension products. -/
private theorem cwSquareOrdinaryDimension_product_identity (q b c k : ℕ) :
    (((2 * q) ^ b) ^ k) *
        (((q ^ 2 + 2) ^ c) ^ k * (((2 * q) ^ b) ^ k)) =
      cwSquareOrdinaryDimension q b c k := by
  let L := 2 * q
  let Q := q ^ 2 + 2
  change (L ^ b) ^ k * ((Q ^ c) ^ k * (L ^ b) ^ k) =
    L ^ (2 * b * k) * Q ^ (c * k)
  rw [← pow_mul L b k, ← pow_mul Q c k]
  calc
    L ^ (b * k) * (Q ^ (c * k) * L ^ (b * k)) =
        (L ^ (b * k) * L ^ (b * k)) * Q ^ (c * k) := by ac_rfl
    _ = L ^ (b * k + b * k) * Q ^ (c * k) := by rw [← pow_add]
    _ = L ^ (2 * b * k) * Q ^ (c * k) := by
      congr 2
      ring

/-- The first matrix dimension along the grouped ordinary word is
`(2q)^(2bk) (q²+2)^(ck)`.

Proof sketch: a word product depends only on multiplicity.  Replace the chosen word by its proved
`cwSquareNaturalType a b c 0 k`, enumerate the fifteen support addresses, and multiply the two
`2q` contributions and the single `q²+2` contribution assigned to the first leg. -/
theorem cwSquareOrdinaryWord_product_m
    (q a b c k : ℕ)
    (hordinary : 0 < cwSquareStride a b c 0) (hk : 0 < k) :
    positiveWordProduct (fun s : CWSquareSupport ↦ cwSquareOrdinaryM q s.1)
        (cwSquareDepth a b c 0 k)
        (cwSquareOrdinaryWord a b c k hordinary hk) =
      cwSquareOrdinaryDimension q b c k := by
  have hword : cwSquareOrdinaryWord a b c k hordinary hk ∈
      positiveTypeClass CWSquareSupport (cwSquareDepth a b c 0 k)
        (cwSquareNaturalType a b c 0 k) :=
    mem_positiveTypeClass.mpr
      (cwSquareOrdinaryWord_type a b c k hordinary hk)
  rw [positiveWordProduct_eq_prod_pow _ hword]
  change (∏ s : CWSquareSupport,
    cwSquareOrdinaryM q s.1 ^ cwSquareNaturalType a b c 0 k s) =
      cwSquareOrdinaryDimension q b c k
  classical
  calc
    (∏ s : CWSquareSupport,
        cwSquareOrdinaryM q s.1 ^ cwSquareNaturalType a b c 0 k s) =
        ∏ s ∈ cwSquareSupport,
          cwSquareOrdinaryM q s ^ (cwSquareClassCount a b c 0 s * k) :=
      (Finset.prod_subtype cwSquareSupport (fun _ ↦ Iff.rfl)
        (fun s ↦ cwSquareOrdinaryM q s ^
          (cwSquareClassCount a b c 0 s * k))).symm
    _ = cwSquareOrdinaryDimension q b c k := by
      rw [cwSquareSupport_eq_antidiagonal]
      unfold cwSquareAntidiagonal
      rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_singleton]
      simp [cwSquareOrdinaryM, cwSquareClassCount, cwSquare004Orbit,
        cwSquare013Orbit, cwSquare022Orbit, cwSquare112Orbit,
        cwSquareAddress_eq_iff]
      simpa only [pow_mul] using
        cwSquareOrdinaryDimension_product_identity q b c k

/-- The middle matrix dimension along the grouped ordinary word is
`(2q)^(2bk) (q²+2)^(ck)`.

Proof sketch: as for `cwSquareOrdinaryWord_product_m`, replace the word by its exact symmetric
type.  On the Y leg the two `013` contributions occur at `130` and `310`, while the `022`
contribution occurs at `220`; all remaining ordinary factors are one. -/
theorem cwSquareOrdinaryWord_product_n
    (q a b c k : ℕ)
    (hordinary : 0 < cwSquareStride a b c 0) (hk : 0 < k) :
    positiveWordProduct (fun s : CWSquareSupport ↦ cwSquareOrdinaryN q s.1)
        (cwSquareDepth a b c 0 k)
        (cwSquareOrdinaryWord a b c k hordinary hk) =
      cwSquareOrdinaryDimension q b c k := by
  have hword : cwSquareOrdinaryWord a b c k hordinary hk ∈
      positiveTypeClass CWSquareSupport (cwSquareDepth a b c 0 k)
        (cwSquareNaturalType a b c 0 k) :=
    mem_positiveTypeClass.mpr
      (cwSquareOrdinaryWord_type a b c k hordinary hk)
  rw [positiveWordProduct_eq_prod_pow _ hword]
  change (∏ s : CWSquareSupport,
    cwSquareOrdinaryN q s.1 ^ cwSquareNaturalType a b c 0 k s) =
      cwSquareOrdinaryDimension q b c k
  classical
  calc
    (∏ s : CWSquareSupport,
        cwSquareOrdinaryN q s.1 ^ cwSquareNaturalType a b c 0 k s) =
        ∏ s ∈ cwSquareSupport,
          cwSquareOrdinaryN q s ^ (cwSquareClassCount a b c 0 s * k) :=
      (Finset.prod_subtype cwSquareSupport (fun _ ↦ Iff.rfl)
        (fun s ↦ cwSquareOrdinaryN q s ^
          (cwSquareClassCount a b c 0 s * k))).symm
    _ = cwSquareOrdinaryDimension q b c k := by
      rw [cwSquareSupport_eq_antidiagonal]
      unfold cwSquareAntidiagonal
      rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_singleton]
      simp [cwSquareOrdinaryN, cwSquareClassCount, cwSquare004Orbit,
        cwSquare013Orbit, cwSquare022Orbit, cwSquare112Orbit]
      simpa only [pow_mul] using
        cwSquareOrdinaryDimension_product_identity q b c k

/-- The third matrix dimension along the grouped ordinary word is
`(2q)^(2bk) (q²+2)^(ck)`.

Proof sketch: the symmetric profile supplies the same factors on every leg.  On Z they occur at
`013`, `031`, and `022`; enumerating the finite support reduces the claim to the common elementary
power identity. -/
theorem cwSquareOrdinaryWord_product_p
    (q a b c k : ℕ)
    (hordinary : 0 < cwSquareStride a b c 0) (hk : 0 < k) :
    positiveWordProduct (fun s : CWSquareSupport ↦ cwSquareOrdinaryP q s.1)
        (cwSquareDepth a b c 0 k)
        (cwSquareOrdinaryWord a b c k hordinary hk) =
      cwSquareOrdinaryDimension q b c k := by
  have hword : cwSquareOrdinaryWord a b c k hordinary hk ∈
      positiveTypeClass CWSquareSupport (cwSquareDepth a b c 0 k)
        (cwSquareNaturalType a b c 0 k) :=
    mem_positiveTypeClass.mpr
      (cwSquareOrdinaryWord_type a b c k hordinary hk)
  rw [positiveWordProduct_eq_prod_pow _ hword]
  change (∏ s : CWSquareSupport,
    cwSquareOrdinaryP q s.1 ^ cwSquareNaturalType a b c 0 k s) =
      cwSquareOrdinaryDimension q b c k
  classical
  calc
    (∏ s : CWSquareSupport,
        cwSquareOrdinaryP q s.1 ^ cwSquareNaturalType a b c 0 k s) =
        ∏ s ∈ cwSquareSupport,
          cwSquareOrdinaryP q s ^ (cwSquareClassCount a b c 0 s * k) :=
      (Finset.prod_subtype cwSquareSupport (fun _ ↦ Iff.rfl)
        (fun s ↦ cwSquareOrdinaryP q s ^
          (cwSquareClassCount a b c 0 s * k))).symm
    _ = cwSquareOrdinaryDimension q b c k := by
      rw [cwSquareSupport_eq_antidiagonal]
      unfold cwSquareAntidiagonal
      rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_singleton]
      simp [cwSquareOrdinaryP, cwSquareClassCount, cwSquare004Orbit,
        cwSquare013Orbit, cwSquare022Orbit, cwSquare112Orbit]
      simpa only [pow_mul] using
        cwSquareOrdinaryDimension_product_identity q b c k

/-- The entire ordinary prefix restricts to a square matrix-multiplication tensor of side
`(2q)^(2bk) (q²+2)^(ck)`.

Proof sketch: apply the generic constituent-word extraction theorem to the total ordinary-or-zero
restriction API.  The chosen word has zero exceptional multiplicity, so its three dimension
products are the positive values computed above rather than zero. -/
theorem cwSquareOrdinaryChunkTensor_restricts
    {K : Type u} [CommRing K]
    (q a b c k : ℕ)
    (hordinary : 0 < cwSquareStride a b c 0) (hk : 0 < k) :
    Restricts
      (cwSquareOrdinaryChunkTensor (K := K) q a b c k hordinary hk)
      (matrixMultiplication (K := K)
        (cwSquareOrdinaryDimension q b c k)
        (cwSquareOrdinaryDimension q b c k)
        (cwSquareOrdinaryDimension q b c k)) := by
  have h := Tensor.Restricts.positiveSupportWordTensor_matrixMultiplication
    (cwSquarePartitionedTensor K q)
    (fun s : CWSquareSupport ↦ cwSquareOrdinaryM q s.1)
    (fun s : CWSquareSupport ↦ cwSquareOrdinaryN q s.1)
    (fun s : CWSquareSupport ↦ cwSquareOrdinaryP q s.1)
    (cwSquareConstituent_restricts_ordinaryOrZero K q)
    (cwSquareDepth a b c 0 k)
    (cwSquareOrdinaryWord a b c k hordinary hk)
  exact h.trans
    (Tensor.Isomorphic.matrixMultiplication_congr
      (K := K)
      (cwSquareOrdinaryWord_product_m q a b c k hordinary hk)
      (cwSquareOrdinaryWord_product_n q a b c k hordinary hk)
      (cwSquareOrdinaryWord_product_p q a b c k hordinary hk)).restricts

/-- Constant chunk of one exceptional square-support orientation. -/
noncomputable abbrev cwSquareExceptionalChunkTensor
    {K : Type u} [CommRing K]
    (q d k : ℕ) (orientation : CWSquareSupport) :=
  (cwSquarePartitionedTensor K q).positiveSupportWordTensor
    (cwSquareExceptionalDepth d k)
    (positiveWordConst orientation (cwSquareExceptionalDepth d k))

/-- Product of the three constant exceptional chunks, ordered as identity, forward cycle, and
inverse cycle. -/
noncomputable abbrev cwSquareExceptionalChunkProduct
    {K : Type u} [CommRing K] (q d k : ℕ) :=
  Tensor.external (K := K)
    (Tensor.external (K := K)
      (cwSquareExceptionalChunkTensor (K := K) q d k cwSquare112S)
      (cwSquareExceptionalChunkTensor (K := K) q d k cwSquare211S))
    (cwSquareExceptionalChunkTensor (K := K) q d k cwSquare121S)

/-- The three exceptional constant chunks restrict to the canonical cyclic power product of the
typed `112` C-tensor.

Proof sketch: a constant supported word is canonically a tensor power of its constituent.  Use the
cyclic square-constituent isomorphisms to rewrite the `211` and `121` powers as the forward and
inverse orientations of the `112` power; `power_permute_positive` commutes those orientations with
the canonical power representation.  Finally apply the finite `112` restriction on all three
orientations and take their external product. -/
theorem cwSquareExceptionalChunkProduct_restricts_cyclicPowerProduct
    {K : Type u} [CommRing K] (q : ℕ) {d k : ℕ}
    (hd : 0 < d) (hk : 0 < k) :
    Restricts
      (cwSquareExceptionalChunkProduct (K := K) q d k)
      (cyclicPowerProduct K (cw112PartitionedTensor K q).realize (d * k)) := by
  let depth := cwSquareExceptionalDepth d k
  let square112 := (cwSquarePartitionedTensor K q).constituent cwSquare112
  let squareFamily := LegModuleFamily.of (K := K)
    (fun c ↦ CWSquareBlockSpace K q c (cwSquare112 c))
  have hcount : depth + 1 = d * k := cwSquareExceptionalDepth_add_one hd hk
  have hbase : Restricts square112 (cw112PartitionedTensor K q).realize := by
    exact cwSquareConstituent_112_restricts_partitioned K q
  have h112 : Restricts
      (cwSquareExceptionalChunkTensor (K := K) q d k cwSquare112S)
      (Tensor.power (cw112PartitionedTensor K q).realize (depth + 1)) := by
    exact (Tensor.PartitionedTensor.Isomorphic.positiveSupportWordTensor_const_power
      (cwSquarePartitionedTensor K q) cwSquare112S depth).restricts.trans
        (hbase.power (depth + 1))
  have h211 : Restricts
      (cwSquareExceptionalChunkTensor (K := K) q d k cwSquare211S)
      (Tensor.permute cycle
        (Tensor.power (cw112PartitionedTensor K q).realize (depth + 1))) := by
    have horient : Isomorphic
        (Tensor.power
          ((cwSquarePartitionedTensor K q).constituent cwSquare211) (depth + 1))
        (Tensor.permute cycle (Tensor.power square112 (depth + 1))) :=
      ((cwSquareConstituent_211_isomorphic_cycle K q).power (depth + 1)).trans
        (Tensor.Isomorphic.power_permute_positive squareFamily square112 depth cycle)
    exact (Tensor.PartitionedTensor.Isomorphic.positiveSupportWordTensor_const_power
      (cwSquarePartitionedTensor K q) cwSquare211S depth).restricts.trans
        (horient.restricts.trans ((hbase.power (depth + 1)).permute cycle))
  have h121 : Restricts
      (cwSquareExceptionalChunkTensor (K := K) q d k cwSquare121S)
      (Tensor.permute cycle.symm
        (Tensor.power (cw112PartitionedTensor K q).realize (depth + 1))) := by
    have horient : Isomorphic
        (Tensor.power
          ((cwSquarePartitionedTensor K q).constituent cwSquare121) (depth + 1))
        (Tensor.permute cycle.symm (Tensor.power square112 (depth + 1))) :=
      ((cwSquareConstituent_121_isomorphic_cycleSymm K q).power (depth + 1)).trans
        (Tensor.Isomorphic.power_permute_positive squareFamily square112 depth cycle.symm)
    exact (Tensor.PartitionedTensor.Isomorphic.positiveSupportWordTensor_const_power
      (cwSquarePartitionedTensor K q) cwSquare121S depth).restricts.trans
        (horient.restricts.trans ((hbase.power (depth + 1)).permute cycle.symm))
  have hproduct := (h112.external h211).external h121
  have hcyclic : Restricts
      (cwSquareExceptionalChunkProduct (K := K) q d k)
      (cyclicPowerProduct K (cw112PartitionedTensor K q).realize (depth + 1)) := by
    simpa only [cwSquareExceptionalChunkProduct, cyclicPowerProduct] using hproduct
  exact hcyclic.trans
    (Tensor.Isomorphic.cyclicPowerProduct_congr
      (K := K) (cw112PartitionedTensor K q).realize hcount).restricts

/-- Tensor selected by the complete raw grouped word. -/
noncomputable abbrev cwSquareGroupedRawTensor
    {K : Type u} [CommRing K]
  (q a b c d k : ℕ)
    (hordinary : 0 < cwSquareStride a b c 0) (hk : 0 < k) :=
  (cwSquarePartitionedTensor K q).positiveSupportWordTensor
    (((cwSquareDepth a b c 0 k + cwSquareExceptionalDepth d k + 1) +
        cwSquareExceptionalDepth d k + 1) +
      cwSquareExceptionalDepth d k + 1)
    (positiveWordAppend
      (positiveWordAppend
        (positiveWordAppend
          (cwSquareOrdinaryWord a b c k hordinary hk)
          (cwSquareExceptionalDepth d k)
          (positiveWordConst cwSquare112S (cwSquareExceptionalDepth d k)))
        (cwSquareExceptionalDepth d k)
        (positiveWordConst cwSquare211S (cwSquareExceptionalDepth d k)))
      (cwSquareExceptionalDepth d k)
      (positiveWordConst cwSquare121S (cwSquareExceptionalDepth d k)))

/-- Explicit left-associated product of the ordinary chunk and the three cyclic exceptional
chunks. -/
noncomputable abbrev cwSquareGroupedChunkProduct
    {K : Type u} [CommRing K]
    (q a b c d k : ℕ)
    (hordinary : 0 < cwSquareStride a b c 0) (hk : 0 < k) :=
  Tensor.external (K := K)
    (Tensor.external (K := K)
      (Tensor.external (K := K)
        (cwSquareOrdinaryChunkTensor (K := K) q a b c k hordinary hk)
        (cwSquareExceptionalChunkTensor (K := K) q d k cwSquare112S))
      (cwSquareExceptionalChunkTensor (K := K) q d k cwSquare211S))
    (cwSquareExceptionalChunkTensor (K := K) q d k cwSquare121S)

/-- Reassociate the four grouped chunks into the ordinary prefix times the three-factor
exceptional product.

Proof sketch: pass through the completely right-associated four-factor product using the generic
external-product associator, then apply the inverse associator only inside the exceptional
factor.  No tensor data or constituent property is used. -/
theorem cwSquareGroupedChunkProduct_isomorphic_ordinaryExceptional
    {K : Type u} [CommRing K]
    (q a b c d k : ℕ)
    (hordinary : 0 < cwSquareStride a b c 0) (hk : 0 < k) :
    Isomorphic
      (cwSquareGroupedChunkProduct (K := K) q a b c d k hordinary hk)
      (Tensor.external
        (cwSquareOrdinaryChunkTensor (K := K) q a b c k hordinary hk)
        (cwSquareExceptionalChunkProduct (K := K) q d k)) := by
  let O := cwSquareOrdinaryChunkTensor (K := K) q a b c k hordinary hk
  let E₁ := cwSquareExceptionalChunkTensor (K := K) q d k cwSquare112S
  let E₂ := cwSquareExceptionalChunkTensor (K := K) q d k cwSquare211S
  let E₃ := cwSquareExceptionalChunkTensor (K := K) q d k cwSquare121S
  change Isomorphic
    (Tensor.external (Tensor.external (Tensor.external O E₁) E₂) E₃)
    (Tensor.external O (Tensor.external (Tensor.external E₁ E₂) E₃))
  exact
    (Tensor.Isomorphic.external_assoc (Tensor.external O E₁) E₂ E₃).trans
      ((Tensor.Isomorphic.external_assoc O E₁ (Tensor.external E₂ E₃)).trans
        ((Tensor.Isomorphic.refl O).external
          (Tensor.Isomorphic.external_assoc_symm E₁ E₂ E₃)))

/-- The grouped four-chunk tensor restricts to the external product of its ordinary square
matrix tensor and the canonical cyclic exceptional power.

Proof sketch: first reassociate the four chunks as ordinary times exceptional.  Apply the exact
ordinary matrix-multiplication restriction to the first factor and the checked shared-`Z`
restriction of the `112/211/121` chunks to the second. -/
theorem cwSquareGroupedChunkProduct_restricts_ordinaryCyclic
    {K : Type u} [CommRing K]
    (q a b c : ℕ) {d k : ℕ}
    (hordinary : 0 < cwSquareStride a b c 0)
    (hd : 0 < d) (hk : 0 < k) :
    Restricts
      (cwSquareGroupedChunkProduct (K := K) q a b c d k hordinary hk)
      (Tensor.external
        (matrixMultiplication (K := K)
          (cwSquareOrdinaryDimension q b c k)
          (cwSquareOrdinaryDimension q b c k)
          (cwSquareOrdinaryDimension q b c k))
        (cyclicPowerProduct K (cw112PartitionedTensor K q).realize (d * k))) := by
  exact
    (cwSquareGroupedChunkProduct_isomorphic_ordinaryExceptional
      q a b c d k hordinary hk).restricts.trans
      ((cwSquareOrdinaryChunkTensor_restricts
          q a b c k hordinary hk).external
        (cwSquareExceptionalChunkProduct_restricts_cyclicPowerProduct
          q hd hk))

/-- The constituent tensor selected by the raw grouped word is isomorphic to the explicitly
parenthesized external product of its four consecutive chunks.

This theorem is purely associativity bookkeeping.  In particular, it does not yet use any
matrix-multiplication restriction for the ordinary prefix or any value theorem for `112`. -/
theorem cwSquareGroupedWordRaw_isomorphic_chunks
    {K : Type u} [CommRing K]
    (q a b c d k : ℕ)
    (hordinary : 0 < cwSquareStride a b c 0) (hk : 0 < k) :
    Isomorphic
      (cwSquareGroupedRawTensor (K := K) q a b c d k hordinary hk)
      (cwSquareGroupedChunkProduct (K := K) q a b c d k hordinary hk) := by
  have h := Tensor.PartitionedTensor.Isomorphic.positiveSupportWordTensor_append_four
    (cwSquarePartitionedTensor K q)
    (cwSquareOrdinaryWord a b c k hordinary hk)
    (positiveWordConst cwSquare112S (cwSquareExceptionalDepth d k))
    (positiveWordConst cwSquare211S (cwSquareExceptionalDepth d k))
    (positiveWordConst cwSquare121S (cwSquareExceptionalDepth d k))
  exact h.symm

/-- The constituent selected by the length-cast grouped word is isomorphic to its explicit
four-chunk product.

Proof sketch: unfold the constituent at a supported word, transport the word and its dependent
block spaces back across `cwSquareGroupedRawDepth_eq`, and then apply the raw four-chunk
associativity theorem. -/
theorem cwSquareGroupedWord_isomorphic_chunks
    {K : Type u} [CommRing K]
    (q a b c d k : ℕ)
    (hordinary : 0 < cwSquareStride a b c 0)
    (hd : 0 < d) (hk : 0 < k) :
    Isomorphic
      (((cwSquarePartitionedTensor K q).positivePower
          (cwSquareDepth a b c d k)).constituent
        (positiveSupportWordBlockAddress cwSquareSupport
          (cwSquareDepth a b c d k)
          (cwSquareGroupedWord a b c d k hordinary hd hk)))
      (cwSquareGroupedChunkProduct (K := K)
        q a b c d k hordinary hk) := by
  have hconst :=
    Tensor.PartitionedTensor.positivePower_constituent_positiveSupportWordBlockAddress
      (cwSquarePartitionedTensor K q)
      (cwSquareDepth a b c d k)
      (cwSquareGroupedWord a b c d k hordinary hd hk)
  have hcast :=
    Tensor.PartitionedTensor.Isomorphic.positiveSupportWordTensor_cast
      (cwSquarePartitionedTensor K q)
      (cwSquareGroupedRawDepth_eq hordinary hd hk)
      (cwSquareGroupedWordRaw a b c d k hordinary hk)
  exact (Tensor.Isomorphic.of_eq hconst).trans
    (hcast.trans
      (cwSquareGroupedWordRaw_isomorphic_chunks
        q a b c d k hordinary hk))

/-- Every marked support word selects a constituent isomorphic to the ordered representative.

This is the exact finite bridge needed after outer hashing: it preserves every retained summand
while making the three exceptional orientations consecutive for shared-`Z` cyclic extraction. -/
theorem cwSquareMarkedWord_constituent_isomorphic_grouped
    {K : Type u} [CommRing K]
    (q : ℕ) {a b c d k : ℕ}
    (hordinary : 0 < cwSquareStride a b c 0)
    (hd : 0 < d) (hk : 0 < k)
    (word : PositiveWord CWSquareSupport (cwSquareDepth a b c d k))
    (hword : word ∈ cwSquareMarkedWords a b c d k) :
    Isomorphic
      (((cwSquarePartitionedTensor K q).positivePower
          (cwSquareDepth a b c d k)).constituent
        (positiveSupportWordBlockAddress cwSquareSupport
          (cwSquareDepth a b c d k) word))
      (((cwSquarePartitionedTensor K q).positivePower
          (cwSquareDepth a b c d k)).constituent
        (positiveSupportWordBlockAddress cwSquareSupport
          (cwSquareDepth a b c d k)
          (cwSquareGroupedWord a b c d k hordinary hd hk))) := by
  apply Tensor.Isomorphic.positivePower_constituent_of_same_type
  exact (mem_positiveTypeClass.mp hword).trans
    (cwSquareGroupedWord_type hordinary hd hk).symm

/-- Every marked word constituent is isomorphic to the explicit ordinary/exceptional chunk
product.

This combines type-preserving position relabeling with the checked dependent cast and
four-factor reassociation of the grouped representative. -/
theorem cwSquareMarkedWord_constituent_isomorphic_chunks
    {K : Type u} [CommRing K]
    (q : ℕ) {a b c d k : ℕ}
    (hordinary : 0 < cwSquareStride a b c 0)
    (hd : 0 < d) (hk : 0 < k)
    (word : PositiveWord CWSquareSupport (cwSquareDepth a b c d k))
    (hword : word ∈ cwSquareMarkedWords a b c d k) :
    Isomorphic
      (((cwSquarePartitionedTensor K q).positivePower
          (cwSquareDepth a b c d k)).constituent
        (positiveSupportWordBlockAddress cwSquareSupport
          (cwSquareDepth a b c d k) word))
      (cwSquareGroupedChunkProduct (K := K)
        q a b c d k hordinary hk) :=
  (cwSquareMarkedWord_constituent_isomorphic_grouped
      q hordinary hd hk word hword).trans
    (cwSquareGroupedWord_isomorphic_chunks
      q a b c d k hordinary hd hk)

end AlgebraicComplexity.Examples
