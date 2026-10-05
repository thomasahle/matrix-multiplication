/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedPower
import AlgebraicComplexity.Tensor.PartitionedRelabeling
import Mathlib.GroupTheory.Perm.Sign

/-!
# Position relabelings of partitioned tensor powers

Chunk permutations in recursive laser arguments must preserve both the word-indexed support and
the tensor carried by every block.  This module constructs those relabelings from the symmetric
monoidal structure already proved for external products.

The first generator swaps the final two chunks of a positive power.  It is then lifted through
prefixes to give every adjacent transposition.  Since adjacent transpositions generate the full
symmetric group, every permutation of the chunks is realized by a structure-preserving
relabeling.  No property of the base tensor or its support is assumed.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-! ## The standard action on word positions -/

/-- Permute the positions of a recursively represented positive word.  The inverse in
`arrowCongr` makes the resulting value at position `i` equal to the old value at `sigma i`. -/
def positiveWordPositionEquiv (I : Type w) (n : ℕ)
    (sigma : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (PositiveWord I n) :=
  (positiveWordEquiv I n).trans
    ((Equiv.arrowCongr sigma.symm (Equiv.refl I)).trans
      (positiveWordEquiv I n).symm)

@[simp] theorem positiveWordEquiv_position_apply
    (sigma : Equiv.Perm (Fin (n + 1))) (word : PositiveWord I n) :
    positiveWordEquiv I n (positiveWordPositionEquiv I n sigma word) =
      positiveWordEquiv I n word ∘ sigma := by
  simp [positiveWordPositionEquiv, Function.comp_def, Equiv.arrowCongr]

@[simp] theorem positiveWordPositionEquiv_one (I : Type w) (n : ℕ) :
    positiveWordPositionEquiv I n 1 = Equiv.refl _ := by
  apply Equiv.ext
  intro word
  apply (positiveWordEquiv I n).injective
  rw [positiveWordEquiv_position_apply]
  rfl

/-- Position relabeling is a left-to-right action, matching `StructureRelabeling.trans`. -/
theorem positiveWordPositionEquiv_mul
    (I : Type w) (n : ℕ) (sigma tau : Equiv.Perm (Fin (n + 1))) :
    positiveWordPositionEquiv I n (sigma * tau) =
      (positiveWordPositionEquiv I n sigma).trans
        (positiveWordPositionEquiv I n tau) := by
  apply Equiv.ext
  intro word
  apply (positiveWordEquiv I n).injective
  rw [positiveWordEquiv_position_apply]
  change positiveWordEquiv I n word ∘ (sigma * tau) =
    positiveWordEquiv I n
      (positiveWordPositionEquiv I n tau
        (positiveWordPositionEquiv I n sigma word))
  rw [positiveWordEquiv_position_apply, positiveWordEquiv_position_apply]
  rfl

@[simp] theorem positiveWordEquiv_last_apply
    (q : PositiveWord I (n + 1)) :
    positiveWordEquiv I (n + 1) q (Fin.last (n + 1)) = q.2 := by
  rw [positiveWordEquiv_succ_apply, Fin.snoc_last]

@[simp] theorem positiveWordEquiv_castSucc_apply
    (q : PositiveWord I (n + 1)) (i : Fin (n + 1)) :
    positiveWordEquiv I (n + 1) q i.castSucc =
      positiveWordEquiv I n q.1 i := by
  rw [positiveWordEquiv_succ_apply, Fin.snoc_castSucc]

private theorem positiveWordEquiv_two_last_apply
    (pre : PositiveWord I n) (a b : I) :
    positiveWordEquiv I (n + 1 + 1) ((pre, a), b)
        (Fin.last (n + 1 + 1)) = b := by
  let preword : PositiveWord I (n + 1) := (pre, a)
  let word : PositiveWord I (n + 1 + 1) := (preword, b)
  change positiveWordEquiv I (n + 1 + 1) word (Fin.last (n + 1 + 1)) = b
  rw [positiveWordEquiv_succ_apply I (n + 1) word, Fin.snoc_last]

private theorem positiveWordEquiv_two_penultimate_apply
    (pre : PositiveWord I n) (a b : I) :
    positiveWordEquiv I (n + 1 + 1) ((pre, a), b)
        (Fin.last (n + 1)).castSucc = a := by
  let preword : PositiveWord I (n + 1) := (pre, a)
  let word : PositiveWord I (n + 1 + 1) := (preword, b)
  change positiveWordEquiv I (n + 1 + 1) word
      (Fin.last (n + 1)).castSucc = a
  rw [positiveWordEquiv_succ_apply I (n + 1) word, Fin.snoc_castSucc]
  change positiveWordEquiv I (n + 1) preword (Fin.last (n + 1)) = a
  rw [positiveWordEquiv_succ_apply I n preword, Fin.snoc_last]

private theorem positiveWordEquiv_two_prefix_apply
    (pre : PositiveWord I n) (a b : I) (k : Fin (n + 1)) :
    positiveWordEquiv I (n + 1 + 1) ((pre, a), b)
        k.castSucc.castSucc = positiveWordEquiv I n pre k := by
  let preword : PositiveWord I (n + 1) := (pre, a)
  let word : PositiveWord I (n + 1 + 1) := (preword, b)
  change positiveWordEquiv I (n + 1 + 1) word k.castSucc.castSucc =
    positiveWordEquiv I n pre k
  rw [positiveWordEquiv_succ_apply I (n + 1) word, Fin.snoc_castSucc]
  change positiveWordEquiv I (n + 1) preword k.castSucc =
    positiveWordEquiv I n pre k
  rw [positiveWordEquiv_succ_apply I n preword, Fin.snoc_castSucc]

/-- On every leg, swap the final two labels of a word with at least two letters.  The equations
are deliberately expressed through the generic product commutors, so the dependent block-space
action computes without transports. -/
def positivePowerSwapLastPartEquiv :
    (n : ℕ) → ∀ c, Equiv.Perm (PositiveWord (A c) (n + 1))
  | 0 => productBlockCommEquiv (A := A) (B := A)
  | n + 1 => productBlockSwapRightEquiv
      (A := fun c ↦ PositiveWord (A c) n) (B := A) (C := A)

/-- The recursive final-factor commutor is exactly the transposition of the final two word
positions. -/
theorem positivePowerSwapLastPartEquiv_eq_positionSwap
    (A : Leg → Type w) (n : ℕ) (c : Leg) :
    positivePowerSwapLastPartEquiv (A := A) n c =
      positiveWordPositionEquiv (A c) (n + 1)
        (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ) := by
  apply Equiv.ext
  intro word
  apply (positiveWordEquiv (A c) (n + 1)).injective
  rw [positiveWordEquiv_position_apply]
  cases n with
  | zero =>
      rcases word with ⟨a, b⟩
      funext j
      fin_cases j <;> rfl
  | succ n =>
      rcases word with ⟨⟨pre, a⟩, b⟩
      funext j
      refine Fin.lastCases ?_ (fun j' ↦ ?_) j
      · simp [positivePowerSwapLastPartEquiv, productBlockSwapRightEquiv,
          positiveWordEquiv_two_penultimate_apply]
        change a = _
        rfl
      · refine Fin.lastCases ?_ (fun k ↦ ?_) j'
        · simp [positivePowerSwapLastPartEquiv, productBlockSwapRightEquiv,
            positiveWordEquiv_two_last_apply]
          change b = _
          rfl
        · simp [positivePowerSwapLastPartEquiv, productBlockSwapRightEquiv,
            Equiv.swap_apply_def, positiveWordEquiv_two_prefix_apply]
          change positiveWordEquiv (A c) n pre k = _
          rfl

/-- The block-space commutor accompanying `positivePowerSwapLastPartEquiv`. -/
noncomputable def positivePowerSwapLastBlockEquiv :
    (n : ℕ) → ∀ c word,
      PositivePowerBlockSpace K V (n + 1) c
          ((positivePowerSwapLastPartEquiv (A := A) n c).symm word) ≃ₗ[K]
        PositivePowerBlockSpace K V (n + 1) c word
  | 0 => productBlockSpaceCommEquiv (K := K) (V := V) (W := V)
  | n + 1 => productBlockSpaceSwapRightEquiv (K := K)
      (V := PositivePowerBlockSpace K V n) (W := V) (X := V)

/-- Swapping the final two chunks preserves the entire positive partitioned power, including its
finite support and every constituent. -/
theorem PartitionedTensor.positivePower_reindex_swapLast
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ) :
    (P.positivePower (n + 1)).reindex
        (positivePowerSwapLastPartEquiv (A := A) n)
        (positivePowerSwapLastBlockEquiv (K := K) (V := V) n) =
      P.positivePower (n + 1) := by
  classical
  cases n with
  | zero =>
      change (P.external P).reindex
          (productBlockCommEquiv (A := A) (B := A))
          (productBlockSpaceCommEquiv (K := K) (V := V) (W := V)) =
        P.external P
      exact PartitionedTensor.external_reindex_comm P P
  | succ n =>
      change (((P.positivePower n).external P).external P).reindex
          (productBlockSwapRightEquiv
            (A := fun c ↦ PositiveWord (A c) n) (B := A) (C := A))
          (productBlockSpaceSwapRightEquiv (K := K)
            (V := PositivePowerBlockSpace K V n) (W := V) (X := V)) =
        ((P.positivePower n).external P).external P
      exact PartitionedTensor.external_reindex_swap_right
        (P.positivePower n) P P

/-- Extending an adjacent transposition by a fixed final point commutes with `Fin.castSucc`. -/
theorem adjacentSwap_castSucc_apply (i : Fin n) (j : Fin (n + 1)) :
    Equiv.swap i.castSucc.castSucc i.succ.castSucc j.castSucc =
      (Equiv.swap i.castSucc i.succ j).castSucc := by
  by_cases hleft : j = i.castSucc
  · subst j
    rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
  by_cases hright : j = i.succ
  · subst j
    rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
  rw [Equiv.swap_apply_of_ne_of_ne hleft hright]
  rw [Equiv.swap_apply_of_ne_of_ne]
  · exact fun h ↦ hleft (Fin.castSucc_injective _ h)
  · exact fun h ↦ hright (Fin.castSucc_injective _ h)

namespace PartitionedTensor.StructureRelabeling

/-- Structure-preserving relabeling which swaps the final two chunks of a positive power. -/
noncomputable def positivePowerSwapLast
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ) :
    (P.positivePower (n + 1)).StructureRelabeling where
  partEquiv := positivePowerSwapLastPartEquiv (A := A) n
  blockEquiv := positivePowerSwapLastBlockEquiv (K := K) (V := V) n
  invariant := P.positivePower_reindex_swapLast n

/-- Lift a structure-preserving relabeling of a word prefix while fixing its final chunk. -/
noncomputable def positivePowerLiftPrefix
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ)
    (r : (P.positivePower n).StructureRelabeling) :
    (P.positivePower (n + 1)).StructureRelabeling := by
  change ((P.positivePower n).external P).StructureRelabeling
  exact r.external (StructureRelabeling.refl P)

/-- Every adjacent pair of positions in a positive word gives a structure-preserving relabeling.
For `positivePower n`, whose words have `n + 1` letters, the boundary index lies in `Fin n`. -/
noncomputable def positivePowerAdjacentSwap
    (P : PartitionedTensor (K := K) (A := A) V) :
    (n : ℕ) → Fin n → (P.positivePower n).StructureRelabeling
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.lastCases
      (positivePowerSwapLast P n)
      (fun j ↦ positivePowerLiftPrefix P n
        (positivePowerAdjacentSwap P n j)) i

/-- The concrete adjacent relabeling acts on every leg by the corresponding adjacent
transposition of word positions. -/
theorem positivePowerAdjacentSwap_partEquiv
    (P : PartitionedTensor (K := K) (A := A) V)
    (n : ℕ) (i : Fin n) (c : Leg) :
    (positivePowerAdjacentSwap P n i).partEquiv c =
      positiveWordPositionEquiv (A c) n
        (Equiv.swap i.castSucc i.succ) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp only [positivePowerAdjacentSwap, Fin.lastCases_last]
        exact positivePowerSwapLastPartEquiv_eq_positionSwap A n c
      · simp only [positivePowerAdjacentSwap, Fin.lastCases_castSucc]
        change Equiv.prodCongr
            ((positivePowerAdjacentSwap P n j).partEquiv c)
            (Equiv.refl (A c)) = _
        rw [ih j]
        apply Equiv.ext
        rintro ⟨pre, last⟩
        let sourceWord : PositiveWord (A c) (n + 1) := (pre, last)
        let movedPrefix : PositiveWord (A c) n :=
          positiveWordPositionEquiv (A c) n
            (Equiv.swap j.castSucc j.succ) pre
        let movedWord : PositiveWord (A c) (n + 1) := (movedPrefix, last)
        change movedWord = positiveWordPositionEquiv (A c) (n + 1)
          (Equiv.swap j.castSucc.castSucc j.succ.castSucc) sourceWord
        apply (positiveWordEquiv (A c) (n + 1)).injective
        rw [positiveWordEquiv_position_apply]
        funext k
        refine Fin.lastCases ?_ (fun k' ↦ ?_) k
        · change positiveWordEquiv (A c) (n + 1) movedWord
              (Fin.last (n + 1)) =
            positiveWordEquiv (A c) (n + 1) sourceWord
              ((Equiv.swap j.castSucc.castSucc j.succ.castSucc)
                (Fin.last (n + 1)))
          have hswap :
              (Equiv.swap j.castSucc.castSucc j.succ.castSucc)
                  (Fin.last (n + 1)) = Fin.last (n + 1) := by
            apply Equiv.swap_apply_of_ne_of_ne
            · exact (Fin.castSucc_lt_last j.castSucc).ne'
            · exact (Fin.castSucc_lt_last j.succ).ne'
          rw [hswap, positiveWordEquiv_last_apply,
            positiveWordEquiv_last_apply]
        · change positiveWordEquiv (A c) (n + 1) movedWord
              k'.castSucc =
            positiveWordEquiv (A c) (n + 1) sourceWord
              ((Equiv.swap j.castSucc.castSucc j.succ.castSucc) k'.castSucc)
          rw [adjacentSwap_castSucc_apply, positiveWordEquiv_castSucc_apply,
            positiveWordEquiv_castSucc_apply,
            positiveWordEquiv_position_apply]
          rfl

/-- Permutations of word positions already realized by structure-preserving relabelings form a
submonoid of the symmetric group.  This packaging lets us use Mathlib's generation theorem. -/
noncomputable def positivePowerPositionRelabelingSubmonoid
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ) :
    Submonoid (Equiv.Perm (Fin (n + 1))) where
  carrier := {sigma | ∃ r : (P.positivePower n).StructureRelabeling,
    ∀ c, r.partEquiv c = positiveWordPositionEquiv (A c) n sigma}
  one_mem' := by
    refine ⟨StructureRelabeling.refl _, ?_⟩
    intro c
    change Equiv.refl _ = positiveWordPositionEquiv (A c) n 1
    exact (positiveWordPositionEquiv_one (A c) n).symm
  mul_mem' := by
    rintro sigma tau ⟨r, hr⟩ ⟨s, hs⟩
    refine ⟨r.trans s, ?_⟩
    intro c
    change (r.partEquiv c).trans (s.partEquiv c) =
      positiveWordPositionEquiv (A c) n (sigma * tau)
    rw [hr c, hs c]
    exact (positiveWordPositionEquiv_mul (A c) n sigma tau).symm

theorem adjacentSwap_mem_positivePowerPositionRelabelingSubmonoid
    (P : PartitionedTensor (K := K) (A := A) V)
    (n : ℕ) (i : Fin n) :
    Equiv.swap i.castSucc i.succ ∈
      positivePowerPositionRelabelingSubmonoid P n := by
  refine ⟨positivePowerAdjacentSwap P n i, ?_⟩
  intro c
  exact positivePowerAdjacentSwap_partEquiv P n i c

/-- Every permutation of the chunks in a positive partitioned power is induced by a genuine
structure-preserving relabeling, including compatible equivalences of all dependent block
spaces. -/
theorem exists_positivePowerPositionRelabeling
    (P : PartitionedTensor (K := K) (A := A) V)
    (n : ℕ) (sigma : Equiv.Perm (Fin (n + 1))) :
    ∃ r : (P.positivePower n).StructureRelabeling,
      ∀ c, r.partEquiv c = positiveWordPositionEquiv (A c) n sigma := by
  have hclosure :
      Submonoid.closure
          (Set.range fun i : Fin n ↦ Equiv.swap i.castSucc i.succ) ≤
        positivePowerPositionRelabelingSubmonoid P n := by
    apply Submonoid.closure_le.mpr
    rintro _ ⟨i, rfl⟩
    exact adjacentSwap_mem_positivePowerPositionRelabelingSubmonoid P n i
  apply hclosure
  rw [Equiv.Perm.mclosure_swap_castSucc_succ n]
  trivial

/-- A chosen structure-preserving relabeling for an arbitrary chunk permutation. -/
noncomputable def positivePowerPositionRelabeling
    (P : PartitionedTensor (K := K) (A := A) V)
    (n : ℕ) (sigma : Equiv.Perm (Fin (n + 1))) :
    (P.positivePower n).StructureRelabeling :=
  (exists_positivePowerPositionRelabeling P n sigma).choose

@[simp] theorem positivePowerPositionRelabeling_partEquiv
    (P : PartitionedTensor (K := K) (A := A) V)
    (n : ℕ) (sigma : Equiv.Perm (Fin (n + 1))) (c : Leg) :
    (positivePowerPositionRelabeling P n sigma).partEquiv c =
      positiveWordPositionEquiv (A c) n sigma :=
  (exists_positivePowerPositionRelabeling P n sigma).choose_spec c

/-- Permuting all positions of a supported address word preserves the corresponding constituent
of a partitioned tensor power up to legwise linear isomorphism.

The same permutation acts on all three legs.  This common-position requirement is exactly what
distinguishes a legitimate reordering of tensor factors from three unrelated permutations of
the block words.

Proof sketch: the chosen `positivePowerPositionRelabeling` preserves the whole partitioned
power.  Its part equivalence sends the transpose of the original support word to the transpose
of the permuted support word, coordinate by coordinate.  Apply
`StructureRelabeling.constituent_isomorphic` at that destination address. -/
theorem positivePower_constituent_isomorphic_position
    (P : PartitionedTensor (K := K) (A := A) V)
    (n : ℕ) (sigma : Equiv.Perm (Fin (n + 1)))
    (word : PositiveWord P.support n) :
    Isomorphic
      ((P.positivePower n).constituent
        (positiveSupportWordBlockAddress P.support n word))
      ((P.positivePower n).constituent
        (positiveSupportWordBlockAddress P.support n
          (positiveWordPositionEquiv P.support n sigma word))) := by
  let r := positivePowerPositionRelabeling P n sigma
  let sourceAddress := positiveSupportWordBlockAddress P.support n word
  have haddress :
      blockAddressCongr r.partEquiv sourceAddress =
        positiveSupportWordBlockAddress P.support n
          (positiveWordPositionEquiv P.support n sigma word) := by
    funext c
    apply (positiveWordEquiv (A c) n).injective
    funext i
    rw [blockAddressCongr_apply,
      positiveWordEquiv_positiveSupportWordBlockAddress]
    change
      positiveWordEquiv (A c) n
          (r.partEquiv c (sourceAddress c)) i =
        (positiveWordEquiv P.support n
          (positiveWordPositionEquiv P.support n sigma word) i).1 c
    rw [show r.partEquiv c = positiveWordPositionEquiv (A c) n sigma by
      simp [r]]
    rw [positiveWordEquiv_position_apply,
      positiveWordEquiv_position_apply,
      positiveWordEquiv_positiveSupportWordBlockAddress]
    rfl
  have h := r.constituent_isomorphic
    (blockAddressCongr r.partEquiv sourceAddress)
  rw [(blockAddressCongr r.partEquiv).symm_apply_apply, haddress] at h
  exact h

end PartitionedTensor.StructureRelabeling
end AlgebraicComplexity.Tensor
