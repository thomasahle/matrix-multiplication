/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedPowerRelabeling

set_option autoImplicit false

/-!
# Interchange of positive partitioned powers with external products

A positive partitioned power of an external product carries the same tensor as the external
product of the two positive powers; only the block labels are regrouped.  This module proves that
regrouping as an exact legwise partition reindex, together with the associator and middle-four
interchange it is built from.

## Why this formulation

Three equivalent statements can close the nested-power gap: lifting a partition reindex through
`positivePower`, conjugating a relabeling across such a reindex, or interchanging a power with an
external product.  The third is chosen here because the Coppersmith--Winograd client already owns
the corresponding *label* identity: a parent chunk splits into its two labelled children exactly by
positive-word concatenation, which is the committed `cwRecursiveChunkJoin_eq_standard`.  Composing
this interchange with that committed identity therefore needs no arithmetic on flattened base
positions, whereas a rechunk to the base tensor would have to redo it against a lexicographic
`Fin` flattening and would leave a perfect-shuffle permutation to identify.

## Design of the statements

Every result is phrased through `PartitionedTensor.ReindexEquiv`, which existentially quantifies
the family of block equivalences and exposes only the label equivalence.  That is deliberate: each
construction below composes several reindexes, so the block data is an iterated `TensorProduct`
shuffle that no client uses, while the label equivalence is exactly the datum a structure
relabeling is conjugated by.  Nothing here assumes anything about supports, tensor values, or the
base field beyond `CommSemiring`.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {B : Leg → Type w} [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {C : Leg → Type w} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
variable {D : Leg → Type w} [∀ c, Fintype (D c)] [∀ c, DecidableEq (D c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {W : ∀ c, B c → Type (max u v)}
variable [∀ c b, AddCommMonoid (W c b)] [∀ c b, Module K (W c b)]
variable {X : ∀ c, C c → Type (max u v)}
variable [∀ c d, AddCommMonoid (X c d)] [∀ c d, Module K (X c d)]
variable {Y : ∀ c, D c → Type (max u v)}
variable [∀ c d, AddCommMonoid (Y c d)] [∀ c d, Module K (Y c d)]

/-! ## Cross-type reindexing of external products -/

/-- Reindexing an external product independently on its two factors is the external product of the
two reindexed partitions, for arbitrary changes of block label type.

The committed `PartitionedTensor.external_reindex` is the special case in which both label
equivalences are permutations; that case cannot express a regrouping of labels, which is exactly
what the interchange laws below need. -/
theorem PartitionedTensor.external_reindex_congr
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W)
    (e : ∀ c, A c ≃ C c) (f : ∀ c d, V c ((e c).symm d) ≃ₗ[K] X c d)
    (g : ∀ c, B c ≃ D c) (h : ∀ c d, W c ((g c).symm d) ≃ₗ[K] Y c d) :
    (P.external Q).reindex
        (fun c ↦ Equiv.prodCongr (e c) (g c))
        (fun c q ↦ TensorProduct.congr (f c q.1) (h c q.2)) =
      (P.reindex e f).external (Q.reindex g h) := by
  classical
  apply PartitionedTensor.ext
  · change
      ((P.support.product Q.support).map
          (blockAddressProductEquiv (A := A) (B := B)).toEmbedding).map
            (blockAddressCongr
              (fun c ↦ Equiv.prodCongr (e c) (g c))).toEmbedding =
        ((P.support.map (blockAddressCongr e).toEmbedding).product
          (Q.support.map (blockAddressCongr g).toEmbedding)).map
            (blockAddressProductEquiv (A := C) (B := D)).toEmbedding
    ext address
    simp [blockAddressProductEquiv]
    rfl
  · funext address
    simp only [PartitionedTensor.reindex_constituent, PartitionedTensor.external,
      blockAddressCongr_symm_apply]
    change map (fun c ↦ TensorProduct.map
        (f c (address c).1).toLinearMap (h c (address c).2).toLinearMap)
      (Tensor.external
        (P.constituent (fun c ↦ (e c).symm (address c).1))
        (Q.constituent (fun c ↦ (g c).symm (address c).2))) = _
    rw [map_external]
    rfl

/-- Reindexing a left-associated triple external product by the associator gives the
right-associated product. -/
theorem PartitionedTensor.external_reindex_assoc
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W)
    (R : PartitionedTensor (K := K) (A := C) X) :
    ((P.external Q).external R).reindex
        (fun c ↦ Equiv.prodAssoc (A c) (B c) (C c))
        (fun c q ↦ TensorProduct.assoc K (V c q.1) (W c q.2.1) (X c q.2.2)) =
      P.external (Q.external R) := by
  classical
  apply PartitionedTensor.ext
  · ext address
    simp [PartitionedTensor.external, PartitionedTensor.reindex,
      blockAddressProductEquiv, and_assoc]
  · funext address
    simp only [PartitionedTensor.external]
    exact map_external_assoc _ _ _

/-- Reindexing a right-associated triple external product by the inverse associator gives the
left-associated product. -/
theorem PartitionedTensor.external_reindex_assoc_symm
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W)
    (R : PartitionedTensor (K := K) (A := C) X) :
    (P.external (Q.external R)).reindex
        (fun c ↦ (Equiv.prodAssoc (A c) (B c) (C c)).symm)
        (fun c q ↦ (TensorProduct.assoc K (V c q.1.1) (W c q.1.2) (X c q.2)).symm) =
      (P.external Q).external R := by
  classical
  apply PartitionedTensor.ext
  · ext address
    simp [PartitionedTensor.external, PartitionedTensor.reindex,
      blockAddressProductEquiv, and_assoc]
  · funext address
    simp only [PartitionedTensor.external]
    exact map_external_assoc_symm _ _ _

/-! ## Reindex equivalence -/

/-- Two partitioned tensors are *reindex-equivalent along `e`* when some legwise family of block
equivalences turns `e` into an exact partition reindex carrying the first onto the second.

The block equivalences are existentially quantified; the label equivalence is not. -/
def PartitionedTensor.ReindexEquiv
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W)
    (e : ∀ c, A c ≃ B c) : Prop :=
  ∃ f : ∀ c b, V c ((e c).symm b) ≃ₗ[K] W c b, P.reindex e f = Q

namespace PartitionedTensor.ReindexEquiv

/-- Every partitioned tensor is reindex-equivalent to itself along the identity. -/
theorem refl (P : PartitionedTensor (K := K) (A := A) V) :
    P.ReindexEquiv P (fun _ ↦ Equiv.refl _) :=
  ⟨fun c a ↦ LinearEquiv.refl K (V c a), P.reindex_refl⟩

/-- Reindex equivalences compose, and their label equivalences compose in the same order. -/
theorem trans {P : PartitionedTensor (K := K) (A := A) V}
    {Q : PartitionedTensor (K := K) (A := B) W}
    {R : PartitionedTensor (K := K) (A := C) X}
    {e : ∀ c, A c ≃ B c} {g : ∀ c, B c ≃ C c}
    (hPQ : P.ReindexEquiv Q e) (hQR : Q.ReindexEquiv R g) :
    P.ReindexEquiv R (fun c ↦ (e c).trans (g c)) := by
  obtain ⟨f, hf⟩ := hPQ
  obtain ⟨h, hh⟩ := hQR
  refine ⟨fun c d ↦ (f c ((g c).symm d)).trans (h c d), ?_⟩
  rw [← PartitionedTensor.reindex_trans P e f g h, hf, hh]

/-- Replace the label equivalence of a reindex equivalence by an equal one. -/
theorem congr_equiv {P : PartitionedTensor (K := K) (A := A) V}
    {Q : PartitionedTensor (K := K) (A := B) W}
    {e e' : ∀ c, A c ≃ B c} (he : e = e') (hPQ : P.ReindexEquiv Q e) :
    P.ReindexEquiv Q e' := he ▸ hPQ

/-- Reindex equivalences act componentwise on an external product. -/
theorem external {P : PartitionedTensor (K := K) (A := A) V}
    {P' : PartitionedTensor (K := K) (A := C) X}
    {Q : PartitionedTensor (K := K) (A := B) W}
    {Q' : PartitionedTensor (K := K) (A := D) Y}
    {e : ∀ c, A c ≃ C c} {g : ∀ c, B c ≃ D c}
    (hP : P.ReindexEquiv P' e) (hQ : Q.ReindexEquiv Q' g) :
    (P.external Q).ReindexEquiv (P'.external Q')
      (fun c ↦ Equiv.prodCongr (e c) (g c)) := by
  obtain ⟨f, hf⟩ := hP
  obtain ⟨h, hh⟩ := hQ
  refine ⟨fun c q ↦ TensorProduct.congr (f c q.1) (h c q.2), ?_⟩
  rw [PartitionedTensor.external_reindex_congr P Q e f g h, hf, hh]

/-- Associativity of the partitioned external product, as a reindex equivalence. -/
theorem assoc (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W)
    (R : PartitionedTensor (K := K) (A := C) X) :
    ((P.external Q).external R).ReindexEquiv (P.external (Q.external R))
      (fun c ↦ Equiv.prodAssoc (A c) (B c) (C c)) :=
  ⟨_, PartitionedTensor.external_reindex_assoc P Q R⟩

/-- Inverse associativity of the partitioned external product, as a reindex equivalence. -/
theorem assocSymm (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W)
    (R : PartitionedTensor (K := K) (A := C) X) :
    (P.external (Q.external R)).ReindexEquiv ((P.external Q).external R)
      (fun c ↦ (Equiv.prodAssoc (A c) (B c) (C c)).symm) :=
  ⟨_, PartitionedTensor.external_reindex_assoc_symm P Q R⟩

/-- Swapping the final two factors of a left-associated triple product, as a reindex
equivalence. -/
theorem swapRight (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W)
    (R : PartitionedTensor (K := K) (A := C) X) :
    ((P.external Q).external R).ReindexEquiv ((P.external R).external Q)
      (productBlockSwapRightEquiv (A := A) (B := B) (C := C)) :=
  ⟨_, PartitionedTensor.external_reindex_swap_right P Q R⟩

end PartitionedTensor.ReindexEquiv

/-! ## The middle-four interchange -/

/-- Interchange the two middle labels of a product of two product blocks. -/
def productBlockInterchangeEquiv : ∀ c,
    ProductBlockIndex (ProductBlockIndex A B) (ProductBlockIndex C D) c ≃
      ProductBlockIndex (ProductBlockIndex A C) (ProductBlockIndex B D) c :=
  fun _ ↦
    { toFun := fun q ↦ ((q.1.1, q.2.1), (q.1.2, q.2.2))
      invFun := fun q ↦ ((q.1.1, q.2.1), (q.1.2, q.2.2))
      left_inv := by rintro ⟨⟨a, b⟩, ⟨x, y⟩⟩; rfl
      right_inv := by rintro ⟨⟨a, x⟩, ⟨b, y⟩⟩; rfl }

/-- Middle-four interchange for partitioned external products.

Proof sketch: swap the trailing factor out of the way, reassociate the exposed triple, swap the
new trailing factor out, and reassociate back.  Every step is one of the committed product
commutors or the associator proved above. -/
theorem PartitionedTensor.ReindexEquiv.externalInterchange
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W)
    (R : PartitionedTensor (K := K) (A := C) X)
    (S : PartitionedTensor (K := K) (A := D) Y) :
    ((P.external Q).external (R.external S)).ReindexEquiv
      ((P.external R).external (Q.external S))
      (productBlockInterchangeEquiv (A := A) (B := B) (C := C) (D := D)) := by
  refine PartitionedTensor.ReindexEquiv.congr_equiv ?_
    (((PartitionedTensor.ReindexEquiv.swapRight P Q (R.external S)).trans
      ((PartitionedTensor.ReindexEquiv.assocSymm P R S).external
        (PartitionedTensor.ReindexEquiv.refl Q))).trans
      ((PartitionedTensor.ReindexEquiv.swapRight (P.external R) S Q).trans
        (PartitionedTensor.ReindexEquiv.assoc (P.external R) Q S)))
  funext c
  apply Equiv.ext
  rintro ⟨⟨a, b⟩, ⟨x, y⟩⟩
  rfl

/-! ## Positive powers distribute over external products -/

/-- Transpose a pair of positive words of the same length into a positive word of pairs. -/
def positiveWordProdEquiv (I J : Type w) :
    (n : ℕ) → (PositiveWord I n × PositiveWord J n) ≃ PositiveWord (I × J) n
  | 0 => Equiv.refl _
  | n + 1 =>
      ({ toFun := fun q ↦ ((q.1.1, q.2.1), (q.1.2, q.2.2))
         invFun := fun q ↦ ((q.1.1, q.2.1), (q.1.2, q.2.2))
         left_inv := by rintro ⟨⟨u, i⟩, ⟨v, j⟩⟩; rfl
         right_inv := by rintro ⟨⟨u, v⟩, ⟨i, j⟩⟩; rfl } :
        (PositiveWord I n × I) × (PositiveWord J n × J) ≃
          (PositiveWord I n × PositiveWord J n) × (I × J)).trans
        (Equiv.prodCongr (positiveWordProdEquiv I J n) (Equiv.refl (I × J)))

/-- The transposed word reads, at every position, as the pair of the two source letters. -/
theorem positiveWordEquiv_positiveWordProdEquiv (I J : Type w) :
    ∀ (n : ℕ) (u : PositiveWord I n) (v : PositiveWord J n),
      positiveWordEquiv (I × J) n (positiveWordProdEquiv I J n (u, v)) =
        fun i ↦ (positiveWordEquiv I n u i, positiveWordEquiv J n v i)
  | 0, u, v => by
      funext i
      fin_cases i
      rfl
  | n + 1, u, v => by
      have hfirst : (positiveWordProdEquiv I J (n + 1) (u, v)).1 =
          positiveWordProdEquiv I J n (u.1, v.1) := rfl
      have hsecond : (positiveWordProdEquiv I J (n + 1) (u, v)).2 = (u.2, v.2) := rfl
      funext i
      rw [positiveWordEquiv_succ_apply (I × J) n, positiveWordEquiv_succ_apply I n,
        positiveWordEquiv_succ_apply J n, hfirst, hsecond,
        positiveWordEquiv_positiveWordProdEquiv I J n u.1 v.1]
      refine Fin.lastCases ?_ (fun k ↦ ?_) i
      · simp only [Fin.snoc_last]
      · simp only [Fin.snoc_castSucc]

/-- A positive partitioned power of an external product is an exact legwise reindex of the
external product of the two positive powers.  The label equivalence is the word transpose.

Proof sketch: induct on the exponent.  A successor power is the external product of the preceding
power with the base, so the goal is a middle-four interchange followed by the inductive
equivalence on the prefix factor. -/
theorem PartitionedTensor.reindexEquiv_positivePower_external
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W) :
    ∀ n : ℕ,
      ((P.positivePower n).external (Q.positivePower n)).ReindexEquiv
        ((P.external Q).positivePower n)
        (fun c ↦ positiveWordProdEquiv (A c) (B c) n)
  | 0 => PartitionedTensor.ReindexEquiv.refl _
  | n + 1 => by
      refine PartitionedTensor.ReindexEquiv.congr_equiv ?_
        ((PartitionedTensor.ReindexEquiv.externalInterchange
            (P.positivePower n) P (Q.positivePower n) Q).trans
          ((PartitionedTensor.reindexEquiv_positivePower_external P Q n).external
            (PartitionedTensor.ReindexEquiv.refl (P.external Q))))
      funext c
      apply Equiv.ext
      rintro ⟨⟨u, a⟩, ⟨v, b⟩⟩
      rfl

/-! ## Letterwise relabeling of positive words -/

/-- Apply a letter equivalence at every position of a positive word. -/
def positiveWordCongrEquiv {I J : Type w} (e : I ≃ J) :
    (n : ℕ) → PositiveWord I n ≃ PositiveWord J n
  | 0 => e
  | n + 1 => Equiv.prodCongr (positiveWordCongrEquiv e n) e

/-- The letterwise relabeled word reads, at every position, as the relabeled source letter. -/
theorem positiveWordEquiv_positiveWordCongrEquiv {I J : Type w} (e : I ≃ J) :
    ∀ (n : ℕ) (u : PositiveWord I n),
      positiveWordEquiv J n (positiveWordCongrEquiv e n u) =
        fun i ↦ e (positiveWordEquiv I n u i)
  | 0, u => by
      funext i
      fin_cases i
      rfl
  | n + 1, u => by
      have hfirst : (positiveWordCongrEquiv e (n + 1) u).1 =
          positiveWordCongrEquiv e n u.1 := rfl
      have hsecond : (positiveWordCongrEquiv e (n + 1) u).2 = e u.2 := rfl
      funext i
      rw [positiveWordEquiv_succ_apply J n, positiveWordEquiv_succ_apply I n,
        hfirst, hsecond, positiveWordEquiv_positiveWordCongrEquiv e n u.1]
      refine Fin.lastCases ?_ (fun k ↦ ?_) i
      · simp only [Fin.snoc_last]
      · simp only [Fin.snoc_castSucc]

/-- A reindex equivalence of the base partitions induces one of every positive power, acting
letterwise on block-label words. -/
theorem PartitionedTensor.ReindexEquiv.positivePower
    {P : PartitionedTensor (K := K) (A := A) V}
    {Q : PartitionedTensor (K := K) (A := B) W}
    {e : ∀ c, A c ≃ B c} (h : P.ReindexEquiv Q e) :
    ∀ n : ℕ, (P.positivePower n).ReindexEquiv (Q.positivePower n)
      (fun c ↦ positiveWordCongrEquiv (e c) n)
  | 0 => h
  | n + 1 =>
      (PartitionedTensor.ReindexEquiv.positivePower h n).external h

/-! ## Transporting the exponent along an arithmetic identity -/

/-- Two positive partitioned powers with equal exponents are reindex-equivalent along the
corresponding type cast.  The exponent occurs in both the label type and the block spaces, so this
is stated as a reindex rather than an equality. -/
theorem PartitionedTensor.reindexEquiv_positivePower_cast
    (P : PartitionedTensor (K := K) (A := A) V) {m m' : ℕ} (hm : m = m') :
    (P.positivePower m).ReindexEquiv (P.positivePower m')
      (fun c ↦ Equiv.cast (congrArg (PositiveWord (A c)) hm)) := by
  subst hm
  exact PartitionedTensor.ReindexEquiv.congr_equiv (by funext c; rfl)
    (PartitionedTensor.ReindexEquiv.refl (P.positivePower m))

end AlgebraicComplexity.Tensor
