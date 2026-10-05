/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.IteratedProduct
import AlgebraicComplexity.Tensor.PartitionedPowerConstituent
import AlgebraicComplexity.Tensor.PartitionedProductRealization
import AlgebraicComplexity.Tensor.PartitionedReindex

/-!
# Positive powers of partitioned tensors

Iterating the external product of a partitioned tensor produces blocks indexed, on each leg, by
nonempty words of original block labels.  This is the representation used by laser-method
zeroing: a word of supported constituent addresses determines three correlated block-label words,
while different constituent words may still share a label word on one or two legs.

The main theorem identifies this partitioned positive power with the canonical `Tensor.power`
used by asymptotic rank.  Thus combinatorial extraction from word blocks applies to the same
tensor powers whose ranks occur in the definition of the matrix-multiplication exponent.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Reassociate the block spaces selected by two consecutive positive words. -/
def positivePowerBlockAppendEquiv (c : Leg)
    (left : PositiveWord (A c) n) :
    (m : ℕ) → (right : PositiveWord (A c) m) →
      TensorProduct K
          (PositivePowerBlockSpace K V n c left)
          (PositivePowerBlockSpace K V m c right) ≃ₗ[K]
        PositivePowerBlockSpace K V (n + m + 1) c
          (positiveWordAppend left m right)
  | 0, _right => LinearEquiv.refl K _
  | m + 1, right =>
      (TensorProduct.assoc K
        (PositivePowerBlockSpace K V n c left)
        (PositivePowerBlockSpace K V m c right.1)
        (V c right.2)).symm.trans
      (TensorProduct.congr
        (positivePowerBlockAppendEquiv c left m right.1)
        (LinearEquiv.refl K (V c right.2)))

/-- Block-space form indexed by the combined word: split the word into its two consecutive
regions and reassociate their block spaces back into the combined block space.  This definition
recurses with the explicit word-splitting equivalence, so it computes on appended words. -/
def positivePowerBlockAppendEquivAt (n : ℕ) :
    (m : ℕ) → (c : Leg) → (word : PositiveWord (A c) (n + m + 1)) →
      TensorProduct K
        (PositivePowerBlockSpace K V n c
          ((positiveWordAppendEquiv (A c) n m).symm word).1)
        (PositivePowerBlockSpace K V m c
          ((positiveWordAppendEquiv (A c) n m).symm word).2) ≃ₗ[K]
        PositivePowerBlockSpace K V (n + m + 1) c word
  | 0, _c, _word => LinearEquiv.refl K _
  | m + 1, c, word =>
      (TensorProduct.assoc K
        (PositivePowerBlockSpace K V n c
          ((positiveWordAppendEquiv (A c) n m).symm word.1).1)
        (PositivePowerBlockSpace K V m c
          ((positiveWordAppendEquiv (A c) n m).symm word.1).2)
        (V c word.2)).symm.trans
      (TensorProduct.congr
        (positivePowerBlockAppendEquivAt n m c word.1)
        (LinearEquiv.refl K (V c word.2)))

/-- Transpose a positive word of full block addresses into one positive word of labels on each
leg.  This is the indexing equivalence underlying `PartitionedTensor.positivePower`. -/
def positiveWordBlockAddressEquiv (A : Leg → Type w) :
    (n : ℕ) → PositiveWord (BlockAddress A) n ≃
      BlockAddress (fun c ↦ PositiveWord (A c) n)
  | 0 => Equiv.refl _
  | n + 1 =>
      (Equiv.prodCongr (positiveWordBlockAddressEquiv A n) (Equiv.refl _)).trans
      (blockAddressProductEquiv
          (A := fun c ↦ PositiveWord (A c) n) (B := A))

/-- Concatenate two consecutive positive block-label words independently on every tensor leg. -/
def positiveWordBlockAppendEquiv (A : Leg → Type w) (n m : ℕ) :
    BlockAddress (ProductBlockIndex
      (fun c ↦ PositiveWord (A c) n) (fun c ↦ PositiveWord (A c) m)) ≃
      BlockAddress (fun c ↦ PositiveWord (A c) (n + m + 1)) :=
  Equiv.piCongrRight fun c ↦ positiveWordAppendEquiv (A c) n m

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
@[simp] theorem positiveWordBlockAppendEquiv_apply
    (address : BlockAddress (ProductBlockIndex
      (fun c ↦ PositiveWord (A c) n) (fun c ↦ PositiveWord (A c) m))) (c : Leg) :
    positiveWordBlockAppendEquiv A n m address c =
      positiveWordAppend (address c).1 m (address c).2 :=
  positiveWordAppendEquiv_apply (address c).1 (address c).2

/-- Transposing an address word and then reading one leg agrees with reading each address in the
function-word representation and projecting that leg. -/
theorem positiveWordEquiv_positiveWordBlockAddressEquiv
    (A : Leg → Type w) (n : ℕ) (q : PositiveWord (BlockAddress A) n) (c : Leg) :
    positiveWordEquiv (A c) n (positiveWordBlockAddressEquiv A n q c) =
      fun i ↦ positiveWordEquiv (BlockAddress A) n q i c := by
  induction n with
  | zero =>
      funext i
      fin_cases i
      rfl
  | succ n ih =>
      rcases q with ⟨q, s⟩
      change positiveWordEquiv (A c) (n + 1)
          (positiveWordBlockAddressEquiv A n q c, s c) =
        fun i ↦ (@Fin.snoc (n + 1) (fun _ ↦ BlockAddress A)
          (positiveWordEquiv (BlockAddress A) n q) s i) c
      change (fun i ↦ @Fin.snoc (n + 1) (fun _ ↦ A c)
          (positiveWordEquiv (A c) n (positiveWordBlockAddressEquiv A n q c))
          (s c) i) = _
      funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp
      · simpa using congrFun (ih q) j

/-- Positive words all of whose letters belong to a prescribed finite support. -/
def positiveSupportWords {I : Type w} [DecidableEq I]
    (support : Finset I) : (n : ℕ) → Finset (PositiveWord I n)
  | 0 => support
  | n + 1 => (positiveSupportWords support n).product support

/-- A positive word over the subtype `support` is equivalently a word over the ambient alphabet
all of whose letters lie in `support`. -/
def positiveSupportWordEquiv {I : Type w} [DecidableEq I] (support : Finset I) :
    (n : ℕ) → PositiveWord support n ≃
      {q : PositiveWord I n // q ∈ positiveSupportWords support n}
  | 0 => Equiv.refl _
  | n + 1 =>
      { toFun := fun q ↦
          ⟨((positiveSupportWordEquiv support n q.1).1, q.2.1),
            Finset.mem_product.mpr
              ⟨(positiveSupportWordEquiv support n q.1).2, q.2.2⟩⟩
        invFun := fun q ↦
          ((positiveSupportWordEquiv support n).symm
              ⟨q.1.1, (Finset.mem_product.mp q.2).1⟩,
            ⟨q.1.2, (Finset.mem_product.mp q.2).2⟩)
        left_inv := fun q ↦ by
          apply Prod.ext
          · exact (positiveSupportWordEquiv support n).symm_apply_apply q.1
          · rfl
        right_inv := fun q ↦ by
          apply Subtype.ext
          apply Prod.ext
          · exact congrArg Subtype.val
              ((positiveSupportWordEquiv support n).apply_symm_apply
                ⟨q.1.1, (Finset.mem_product.mp q.2).1⟩)
          · rfl }

/-- The ambient word underlying `positiveSupportWordEquiv` is letterwise subtype coercion. -/
@[simp] theorem positiveSupportWordEquiv_apply_val {I : Type w} [DecidableEq I]
    (support : Finset I) (n : ℕ) (q : PositiveWord support n) :
    (positiveSupportWordEquiv support n q).1 =
      positiveWordMap Subtype.val n q := by
  induction n with
  | zero => rfl
  | succ n ih =>
      apply Prod.ext
      · exact ih q.1
      · rfl

/-- Finite-set form of `positiveSupportWordEquiv`. -/
theorem positiveSupportWords_eq_image_univ_subtype {I : Type w}
    [Fintype I] [DecidableEq I] (support : Finset I) (n : ℕ) :
    positiveSupportWords support n =
      (Finset.univ : Finset (PositiveWord support n)).image
        (positiveWordMap Subtype.val n) := by
  classical
  ext q
  constructor
  · intro hq
    let lifted := (positiveSupportWordEquiv support n).symm ⟨q, hq⟩
    apply Finset.mem_image.mpr
    refine ⟨lifted, Finset.mem_univ _, ?_⟩
    rw [← positiveSupportWordEquiv_apply_val]
    exact congrArg Subtype.val
      ((positiveSupportWordEquiv support n).apply_symm_apply ⟨q, hq⟩)
  · intro hq
    obtain ⟨word, _hword, rfl⟩ := Finset.mem_image.mp hq
    rw [← positiveSupportWordEquiv_apply_val]
    exact (positiveSupportWordEquiv support n word).2

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- The recursive supported-word transpose agrees with the ambient address-word equivalence.
The recursive presentation is retained because it exposes the dependent block-space type of each
constituent definitionally. -/
theorem positiveSupportWordBlockAddress_eq_equiv_map
    (support : Finset (BlockAddress A)) (n : ℕ)
    (q : PositiveWord support n) :
    positiveSupportWordBlockAddress support n q =
      positiveWordBlockAddressEquiv A n (positiveWordMap Subtype.val n q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rcases q with ⟨q, s⟩
      funext c
      change (positiveSupportWordBlockAddress support n q c, s.1 c) =
        (positiveWordBlockAddressEquiv A n
          (positiveWordMap Subtype.val n q) c, s.1 c)
      rw [ih q]

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Reading a transposed supported word on one leg agrees with projecting every source address to
that leg. -/
theorem positiveWordEquiv_positiveSupportWordBlockAddress
    (support : Finset (BlockAddress A)) (n : ℕ)
    (q : PositiveWord support n) (c : Leg) :
    positiveWordEquiv (A c) n (positiveSupportWordBlockAddress support n q c) =
      fun i ↦ (positiveWordEquiv support n q i).1 c := by
  induction n with
  | zero =>
      funext i
      fin_cases i
      rfl
  | succ n ih =>
      rcases q with ⟨q, s⟩
      change positiveWordEquiv (A c) (n + 1)
          (positiveSupportWordBlockAddress support n q c, s.1 c) =
        fun i ↦ (@Fin.snoc (n + 1) (fun _ ↦ support)
          (positiveWordEquiv support n q) s i).1 c
      change (fun i ↦ @Fin.snoc (n + 1) (fun _ ↦ A c)
          (positiveWordEquiv (A c) n
            (positiveSupportWordBlockAddress support n q c)) (s.1 c) i) = _
      funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp
      · simpa using congrFun (ih q) j

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Legwise transposition commutes with concatenating two supported address words. -/
theorem positiveSupportWordBlockAddress_append
    (support : Finset (BlockAddress A))
    (left : PositiveWord support n) (right : PositiveWord support m) :
    positiveSupportWordBlockAddress support (n + m + 1)
        (positiveWordAppend left m right) =
      fun c ↦ positiveWordAppend
        (positiveSupportWordBlockAddress support n left c) m
        (positiveSupportWordBlockAddress support m right c) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rcases right with ⟨right, last⟩
      funext c
      change (positiveSupportWordBlockAddress support (n + m + 1)
          (positiveWordAppend left m right) c, last.1 c) =
        (positiveWordAppend
          (positiveSupportWordBlockAddress support n left c) m
          (positiveSupportWordBlockAddress support m right c), last.1 c)
      rw [congrFun (ih right) c]

@[simp] theorem positiveSupportWords_zero {I : Type w} [DecidableEq I]
    (support : Finset I) : positiveSupportWords support 0 = support := rfl

@[simp] theorem positiveSupportWords_succ {I : Type w} [DecidableEq I]
    (support : Finset I) (n : ℕ) :
    positiveSupportWords support (n + 1) =
      (positiveSupportWords support n).product support := rfl

/-- Exact number of nonempty support words. -/
@[simp] theorem card_positiveSupportWords {I : Type w} [DecidableEq I]
    (support : Finset I) (n : ℕ) :
    (positiveSupportWords support n).card = support.card ^ (n + 1) := by
  induction n with
  | zero => exact (pow_one support.card).symm
  | succ n ih =>
      calc
        (positiveSupportWords support (n + 1)).card =
            (positiveSupportWords support n).card * support.card := by
          exact Finset.card_product _ _
        _ = support.card ^ (n + 1) * support.card := by rw [ih]
        _ = support.card ^ (n + 1 + 1) := (pow_succ _ _).symm

namespace PartitionedTensor

/-- Concatenate the block words of two consecutive regional partitions.  The construction only
renames and reassociates blocks; it neither adds nor removes supported constituents. -/
noncomputable def appendPositiveWordPartitions
    (left : PartitionedTensor (K := K)
      (A := fun c ↦ PositiveWord (A c) n) (PositivePowerBlockSpace K V n))
    (right : PartitionedTensor (K := K)
      (A := fun c ↦ PositiveWord (A c) m) (PositivePowerBlockSpace K V m)) :
    PartitionedTensor (K := K)
      (A := fun c ↦ PositiveWord (A c) (n + m + 1))
      (PositivePowerBlockSpace K V (n + m + 1)) :=
  (left.external right).reindex
    (fun c ↦ positiveWordAppendEquiv (A c) n m)
    (positivePowerBlockAppendEquivAt (K := K) (V := V) n m)

@[simp] theorem appendPositiveWordPartitions_support
    (left : PartitionedTensor (K := K)
      (A := fun c ↦ PositiveWord (A c) n) (PositivePowerBlockSpace K V n))
    (right : PartitionedTensor (K := K)
      (A := fun c ↦ PositiveWord (A c) m) (PositivePowerBlockSpace K V m)) :
    (appendPositiveWordPartitions left right).support =
      (left.external right).support.map
        (positiveWordBlockAppendEquiv A n m).toEmbedding :=
  rfl

/-- Reassociating the external product of two supported constituent words gives the constituent
at their concatenated block-word address. -/
theorem map_positivePowerBlockAppendEquiv_external_positiveSupportWordTensors
    (P : PartitionedTensor (K := K) (A := A) V)
    (left : PositiveWord P.support n) (right : PositiveWord P.support m) :
    map (fun c ↦ (positivePowerBlockAppendEquiv (K := K) (V := V) c
        (positiveSupportWordBlockAddress P.support n left c) m
        (positiveSupportWordBlockAddress P.support m right c)).toLinearMap)
      (Tensor.external (P.positiveSupportWordTensor n left)
        (P.positiveSupportWordTensor m right)) =
      (P.positivePower (n + m + 1)).constituent
        (fun c ↦ positiveWordAppend
          (positiveSupportWordBlockAddress P.support n left c) m
          (positiveSupportWordBlockAddress P.support m right c)) := by
  induction m with
  | zero =>
      change map (fun _c ↦ LinearMap.id)
          (Tensor.external (P.positiveSupportWordTensor n left) (P.constituent right.1)) =
        Tensor.external
          ((P.positivePower n).constituent
            (positiveSupportWordBlockAddress P.support n left))
          (P.constituent right.1)
      rw [map_id, P.positivePower_constituent_positiveSupportWordBlockAddress]
      rfl
  | succ m ih =>
      rcases right with ⟨right, last⟩
      change map (fun c ↦
          ((TensorProduct.assoc K
            (PositivePowerBlockSpace K V n c
              (positiveSupportWordBlockAddress P.support n left c))
            (PositivePowerBlockSpace K V m c
              (positiveSupportWordBlockAddress P.support m right c))
            (V c (last.1 c))).symm.trans
          (TensorProduct.congr
            (positivePowerBlockAppendEquiv (K := K) (V := V) c
              (positiveSupportWordBlockAddress P.support n left c) m
              (positiveSupportWordBlockAddress P.support m right c))
            (LinearEquiv.refl K (V c (last.1 c))))).toLinearMap)
        (Tensor.external (P.positiveSupportWordTensor n left)
          (Tensor.external (P.positiveSupportWordTensor m right) (P.constituent last.1))) = _
      change map (fun c ↦
          (TensorProduct.congr
            (positivePowerBlockAppendEquiv (K := K) (V := V) c
              (positiveSupportWordBlockAddress P.support n left c) m
              (positiveSupportWordBlockAddress P.support m right c))
            (LinearEquiv.refl K (V c (last.1 c)))).toLinearMap ∘ₗ
          (TensorProduct.assoc K
            (PositivePowerBlockSpace K V n c
              (positiveSupportWordBlockAddress P.support n left c))
            (PositivePowerBlockSpace K V m c
              (positiveSupportWordBlockAddress P.support m right c))
            (V c (last.1 c))).symm.toLinearMap)
        (Tensor.external (P.positiveSupportWordTensor n left)
          (Tensor.external (P.positiveSupportWordTensor m right) (P.constituent last.1))) = _
      rw [map_comp]
      simp only [LinearMap.comp_apply]
      rw [map_external_assoc_symm]
      change map (fun c ↦ TensorProduct.map
          (positivePowerBlockAppendEquiv (K := K) (V := V) c
            (positiveSupportWordBlockAddress P.support n left c) m
            (positiveSupportWordBlockAddress P.support m right c)).toLinearMap
          (LinearMap.id (R := K) (M := V c (last.1 c))))
        (Tensor.external
          (Tensor.external (P.positiveSupportWordTensor n left)
            (P.positiveSupportWordTensor m right))
          (P.constituent last.1)) = _
      rw [map_external, ih]
      rw [map_id]
      rfl

namespace Isomorphic

/-- Transporting the length index of a supported word does not change its selected constituent,
up to the canonical dependent identification of the iterated block spaces.

This lemma is intentionally phrased as an isomorphism instead of an equality: both the word type
and the ambient tensor-leg types depend on the length index. -/
theorem positiveSupportWordTensor_cast
    (P : PartitionedTensor (K := K) (A := A) V)
    {n m : ℕ} (h : n = m) (word : PositiveWord P.support n) :
    Isomorphic
      (P.positiveSupportWordTensor m (positiveWordCast h word))
      (P.positiveSupportWordTensor n word) := by
  subst m
  exact Isomorphic.refl _

/-- A constant supported address word selects a tensor isomorphic to the corresponding positive
iterated external power of its base constituent. -/
theorem positiveSupportWordTensor_const
    (P : PartitionedTensor (K := K) (A := A) V)
    (s : P.support) (n : ℕ) :
    Isomorphic
      (P.positiveSupportWordTensor n (positiveWordConst s n))
      (Tensor.iteratedExternal
        (LegModuleFamily.of (K := K) (fun c ↦ V c (s.1 c)))
        (P.constituent s.1) n) := by
  induction n with
  | zero => exact Isomorphic.refl _
  | succ n ih =>
      change Isomorphic
        (Tensor.external
          (P.positiveSupportWordTensor n (positiveWordConst s n))
          (P.constituent s.1))
        (Tensor.external
          (Tensor.iteratedExternal
            (LegModuleFamily.of (K := K) (fun c ↦ V c (s.1 c)))
            (P.constituent s.1) n)
          (P.constituent s.1))
      exact Isomorphic.external ih (Isomorphic.refl _)

/-- Constant supported words, stated in canonical tensor-power form. -/
theorem positiveSupportWordTensor_const_power
    (P : PartitionedTensor (K := K) (A := A) V)
    (s : P.support) (n : ℕ) :
    Isomorphic
      (P.positiveSupportWordTensor n (positiveWordConst s n))
      (Tensor.power (P.constituent s.1) (n + 1)) :=
  (positiveSupportWordTensor_const P s n).trans
    (Isomorphic.power_positive_iteratedExternal
      (LegModuleFamily.of (K := K) (fun c ↦ V c (s.1 c)))
      (P.constituent s.1) n).symm

/-- Reassociating two consecutive supported constituent words identifies their external product
with the tensor selected by the concatenated word. -/
theorem positiveSupportWordTensor_append
    (P : PartitionedTensor (K := K) (A := A) V)
    (left : PositiveWord P.support n) (right : PositiveWord P.support m) :
    Isomorphic
      (Tensor.external (P.positiveSupportWordTensor n left)
        (P.positiveSupportWordTensor m right))
      (P.positiveSupportWordTensor (n + m + 1)
        (positiveWordAppend left m right)) := by
  rw [← P.positivePower_constituent_positiveSupportWordBlockAddress
    (n + m + 1) (positiveWordAppend left m right)]
  rw [positiveSupportWordBlockAddress_append]
  refine ⟨fun c ↦ positivePowerBlockAppendEquiv (K := K) (V := V) c
    (positiveSupportWordBlockAddress P.support n left c) m
    (positiveSupportWordBlockAddress P.support m right c), ?_⟩
  change map (fun c ↦
      (positivePowerBlockAppendEquiv (K := K) (V := V) c
        (positiveSupportWordBlockAddress P.support n left c) m
        (positiveSupportWordBlockAddress P.support m right c)).toLinearMap)
      (Tensor.external (P.positiveSupportWordTensor n left)
        (P.positiveSupportWordTensor m right)) = _
  exact P.map_positivePowerBlockAppendEquiv_external_positiveSupportWordTensors
    left right

/-- Reassociating four consecutive supported constituent words identifies their left-associated
external product with the tensor selected by the iterated concatenation.

This small packaged form prevents clients from repeatedly asking the elaborator to normalize the
large dependent block-space types occurring between three applications of
`positiveSupportWordTensor_append`. -/
theorem positiveSupportWordTensor_append_four
    (P : PartitionedTensor (K := K) (A := A) V)
    (w₁ : PositiveWord P.support n₁) (w₂ : PositiveWord P.support n₂)
    (w₃ : PositiveWord P.support n₃) (w₄ : PositiveWord P.support n₄) :
    Isomorphic
      (Tensor.external
        (Tensor.external
          (Tensor.external
            (P.positiveSupportWordTensor n₁ w₁)
            (P.positiveSupportWordTensor n₂ w₂))
          (P.positiveSupportWordTensor n₃ w₃))
        (P.positiveSupportWordTensor n₄ w₄))
      (P.positiveSupportWordTensor
        (((n₁ + n₂ + 1) + n₃ + 1) + n₄ + 1)
        (positiveWordAppend
          (positiveWordAppend (positiveWordAppend w₁ n₂ w₂) n₃ w₃) n₄ w₄)) := by
  exact
    (Isomorphic.external
      (Isomorphic.external
        (positiveSupportWordTensor_append P w₁ w₂)
        (Isomorphic.refl (P.positiveSupportWordTensor n₃ w₃)))
      (Isomorphic.refl (P.positiveSupportWordTensor n₄ w₄))).trans
      ((Isomorphic.external
        (positiveSupportWordTensor_append P (positiveWordAppend w₁ n₂ w₂) w₃)
        (Isomorphic.refl (P.positiveSupportWordTensor n₄ w₄))).trans
        (positiveSupportWordTensor_append P
          (positiveWordAppend (positiveWordAppend w₁ n₂ w₂) n₃ w₃) w₄))

end Isomorphic

/-- The recursive partition support is exactly the image of supported address words under
legwise transposition. -/
theorem positivePower_support_eq_map_positiveSupportWords
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ) :
    (P.positivePower n).support =
      (positiveSupportWords P.support n).map
        (positiveWordBlockAddressEquiv A n).toEmbedding := by
  classical
  induction n with
  | zero =>
      ext q
      rw [Finset.mem_map_equiv]
      rfl
  | succ n ih =>
      rw [positivePower_succ, positiveSupportWords_succ]
      unfold PartitionedTensor.external
      rw [ih]
      let wordEmbedding := (positiveWordBlockAddressEquiv A n).toEmbedding
      let pairEmbedding := wordEmbedding.prodMap
        (Function.Embedding.refl (BlockAddress A))
      let blockEmbedding := (blockAddressProductEquiv
        (A := fun c ↦ PositiveWord (A c) n) (B := A)).toEmbedding
      have hproduct :
          (Finset.map wordEmbedding (positiveSupportWords P.support n)).product P.support =
            Finset.map pairEmbedding
              ((positiveSupportWords P.support n).product P.support) := by
        simpa [wordEmbedding, pairEmbedding] using
          (Finset.prodMap_map_product wordEmbedding
            (Function.Embedding.refl (BlockAddress A))
            (positiveSupportWords P.support n) P.support).symm
      rw [hproduct, Finset.map_map]
      have hembedding : pairEmbedding.trans blockEmbedding =
          (positiveWordBlockAddressEquiv A (n + 1)).toEmbedding := by
        apply Function.Embedding.ext
        rintro ⟨word, s⟩
        rfl
      rw [hembedding]
      change Finset.map (positiveWordBlockAddressEquiv A (n + 1)).toEmbedding
        ((positiveSupportWords P.support n).product P.support) = _
      rfl

/-- The support of a positive partitioned power is the image of words over the *supported*
source addresses under the recursive legwise transpose.  This form exposes a typed source word
directly and is usually the most convenient elimination principle for client proofs. -/
theorem positivePower_support_eq_image_positiveSupportWordBlockAddress
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ) :
    (P.positivePower n).support =
      (Finset.univ : Finset (PositiveWord P.support n)).image
        (positiveSupportWordBlockAddress P.support n) := by
  classical
  rw [positivePower_support_eq_map_positiveSupportWords,
    Finset.map_eq_image, positiveSupportWords_eq_image_univ_subtype,
    Finset.image_image]
  apply Finset.image_congr
  intro q _hq
  exact (positiveSupportWordBlockAddress_eq_equiv_map P.support n q).symm

/-- Every supported block of a positive partitioned power is represented by a supported source
address word. -/
theorem exists_positiveSupportWord_of_mem_positivePower_support
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ)
    {address : BlockAddress (fun c ↦ PositiveWord (A c) n)}
    (haddress : address ∈ (P.positivePower n).support) :
    ∃ q : PositiveWord P.support n,
      positiveSupportWordBlockAddress P.support n q = address := by
  rw [P.positivePower_support_eq_image_positiveSupportWordBlockAddress n] at haddress
  obtain ⟨q, _hq, hq⟩ := Finset.mem_image.mp haddress
  exact ⟨q, hq⟩

/-- A positive power has one supported address for every word of supported base addresses. -/
@[simp] theorem card_positivePower_support
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ) :
    (P.positivePower n).support.card = P.support.card ^ (n + 1) := by
  calc
    (P.positivePower n).support.card =
        ((positiveSupportWords P.support n).map
          (positiveWordBlockAddressEquiv A n).toEmbedding).card :=
      congrArg Finset.card (positivePower_support_eq_map_positiveSupportWords P n)
    _ = (positiveSupportWords P.support n).card :=
      Finset.card_map (positiveWordBlockAddressEquiv A n).toEmbedding
    _ = P.support.card ^ (n + 1) := card_positiveSupportWords P.support n

/-- Splitting a positive power into two consecutive nonempty regions identifies its support with
the external product of the two regional supports. -/
theorem positivePower_external_support_map_append
    (P : PartitionedTensor (K := K) (A := A) V) (n m : ℕ) :
    ((P.positivePower n).external (P.positivePower m)).support.map
        (positiveWordBlockAppendEquiv A n m).toEmbedding =
      (P.positivePower (n + m + 1)).support := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro address haddress
    obtain ⟨paired, hpaired, rfl⟩ := Finset.mem_map.mp haddress
    unfold PartitionedTensor.external at hpaired
    obtain ⟨pair, hpair, hpairAddress⟩ := Finset.mem_map.mp hpaired
    obtain ⟨hleft, hright⟩ := Finset.mem_product.mp hpair
    obtain ⟨leftWord, hleftWord⟩ :=
      P.exists_positiveSupportWord_of_mem_positivePower_support n hleft
    obtain ⟨rightWord, hrightWord⟩ :=
      P.exists_positiveSupportWord_of_mem_positivePower_support m hright
    rw [P.positivePower_support_eq_image_positiveSupportWordBlockAddress (n + m + 1)]
    apply Finset.mem_image.mpr
    refine ⟨positiveWordAppend leftWord m rightWord, Finset.mem_univ _, ?_⟩
    rw [positiveSupportWordBlockAddress_append]
    subst paired
    rw [hleftWord, hrightWord]
    funext c
    rcases pair with ⟨leftAddress, rightAddress⟩
    change positiveWordAppend (leftAddress c) m (rightAddress c) =
      positiveWordBlockAppendEquiv A n m
        (blockAddressProductEquiv (leftAddress, rightAddress)) c
    rw [positiveWordBlockAppendEquiv_apply]
    rfl
  · rw [Finset.card_map]
    simp only [PartitionedTensor.card_external_support,
      PartitionedTensor.card_positivePower_support]
    rw [← pow_add]
    apply le_of_eq
    congr 1
    omega

end PartitionedTensor

namespace Isomorphic

/-- A left-associated positive external power of a partitioned realization is canonically
isomorphic to the realization of its word-block partition. -/
theorem iteratedExternal_partitionedPositivePower
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ) :
    Isomorphic
      (iteratedExternal
        (LegModuleFamily.of.{u, max v w} (K := K) (PartitionedSpace K V)) P.realize n)
      (P.positivePower n).realize := by
  induction n with
  | zero => exact Isomorphic.refl P.realize
  | succ n ih =>
      change Isomorphic
        (Tensor.external
          (iteratedExternal
            (LegModuleFamily.of.{u, max v w} (K := K) (PartitionedSpace K V)) P.realize n)
          P.realize)
        ((P.positivePower n).external P).realize
      exact (Isomorphic.external ih (Isomorphic.refl P.realize)).trans
        (Isomorphic.partitionedExternal (P.positivePower n) P)

/-- Canonical tensor powers and the word-block positive partition represent isomorphic tensors.
This is the public bridge used by asymptotic laser extraction. -/
theorem power_partitionedPositivePower
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ) :
    Isomorphic (Tensor.power P.realize (n + 1)) (P.positivePower n).realize :=
  (Isomorphic.power_positive_iteratedExternal
    (LegModuleFamily.of.{u, max v w} (K := K) (PartitionedSpace K V)) P.realize n).trans
      (Isomorphic.iteratedExternal_partitionedPositivePower P n)

end Isomorphic

namespace Restricts

/-- Restriction form of the canonical-power/partitioned-power bridge. -/
theorem power_partitionedPositivePower
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ) :
    Restricts (Tensor.power P.realize (n + 1)) (P.positivePower n).realize :=
  (Isomorphic.power_partitionedPositivePower P n).restricts

end Restricts

end AlgebraicComplexity.Tensor
