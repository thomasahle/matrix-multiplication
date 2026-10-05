/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.IndexedDirectSum
import AlgebraicComplexity.Tensor.PartitionedReindex

/-!
# Box restrictions and the eight-way hole decomposition

The recursive hole-repair argument starts from a broken copy of a partitioned tensor.  Relative
to target part sets, every leg is split into its holes and non-holes, producing eight disjoint
boxes.  The all-non-hole box is supplied by the broken copy; the other seven boxes are recursive
subproblems.

This module proves that decomposition as an exact tensor identity.  It contains no asymptotics
and is independent of the tensor's coefficients.
-/

namespace AlgebraicComplexity.Tensor

open scoped BigOperators

universe u v w x y

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- One side of a target/hole partition.  `true` selects non-holes and `false` selects holes
inside the target. -/
def splitPart {B : Type*} [DecidableEq B]
    (target holes : Finset B) (nonHole : Bool) : Finset B :=
  if nonHole then target \ holes else target ∩ holes

@[simp] theorem mem_splitPart_true {B : Type*} [DecidableEq B]
    {target holes : Finset B} {b : B} :
    b ∈ splitPart target holes true ↔ b ∈ target ∧ b ∉ holes := by
  simp [splitPart]

@[simp] theorem mem_splitPart_false {B : Type*} [DecidableEq B]
    {target holes : Finset B} {b : B} :
    b ∈ splitPart target holes false ↔ b ∈ target ∧ b ∈ holes := by
  simp [splitPart]

/-- The legwise part sets belonging to one of the eight hole/non-hole masks. -/
def splitBoxParts (target holes : ∀ c, Finset (A c)) (mask : Leg → Bool) :
    ∀ c, Finset (A c) :=
  fun c ↦ splitPart (target c) (holes c) (mask c)

/-- The mask selecting non-holes on every leg. -/
def allNonHoleMask : Leg → Bool := fun _ ↦ true

omit [∀ c, Fintype (A c)] in
@[simp] theorem splitBoxParts_allNonHole
    (target holes : ∀ c, Finset (A c)) :
    splitBoxParts target holes allNonHoleMask = fun c ↦ target c \ holes c := by
  funext c
  simp [splitBoxParts, splitPart, allNonHoleMask]

/-- Restrict a partitioned tensor to a Cartesian box of block labels. -/
def PartitionedTensor.box
    (P : PartitionedTensor (K := K) (A := A) V)
    (parts : ∀ c, Finset (A c)) : PartitionedTensor (K := K) (A := A) V :=
  P.select fun c a ↦ a ∈ parts c

/-! ## Structure-preserving relabellings -/

section ReindexBox

variable {B : Leg → Type x} [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {W : ∀ c, B c → Type y}
variable [∀ c b, AddCommMonoid (W c b)] [∀ c b, Module K (W c b)]

/-- Reindexing a partitioned tensor commutes with restricting its three block-label sets. -/
theorem PartitionedTensor.reindex_box
    (P : PartitionedTensor (K := K) (A := A) V)
    (e : ∀ c, A c ≃ B c)
    (f : ∀ c b, V c ((e c).symm b) ≃ₗ[K] W c b)
    (parts : ∀ c, Finset (A c)) :
    (P.box parts).reindex e f =
      (P.reindex e f).box (relabelParts e parts) := by
  classical
  unfold PartitionedTensor.box
  rw [PartitionedTensor.reindex_select]
  apply PartitionedTensor.ext
  · ext address
    simp
  · rfl

end ReindexBox

/-- A legwise block relabelling which preserves a partitioned tensor, including the linear
identifications of the individual block spaces.  This is the exact tensor-level form of the
structure-preservation hypothesis in the hole-repair theorem. -/
structure PartitionedTensor.StructureRelabeling
    (P : PartitionedTensor (K := K) (A := A) V) where
  partEquiv : ∀ c, Equiv.Perm (A c)
  blockEquiv : ∀ c b, V c ((partEquiv c).symm b) ≃ₗ[K] V c b
  invariant : P.reindex partEquiv blockEquiv = P

namespace PartitionedTensor.StructureRelabeling

variable {P : PartitionedTensor (K := K) (A := A) V}

/-- The identity relabeling preserves every partitioned tensor. -/
noncomputable def refl
    (P : PartitionedTensor (K := K) (A := A) V) : P.StructureRelabeling where
  partEquiv := fun _ ↦ Equiv.refl _
  blockEquiv := fun c a ↦ LinearEquiv.refl K (V c a)
  invariant := P.reindex_refl

/-- Compose two structure-preserving relabelings.  Label equivalences act from left to right,
and the dependent block equivalences follow the same order. -/
noncomputable def trans (r s : P.StructureRelabeling) :
    P.StructureRelabeling where
  partEquiv := fun c ↦ (r.partEquiv c).trans (s.partEquiv c)
  blockEquiv := fun c a ↦
    (r.blockEquiv c ((s.partEquiv c).symm a)).trans (s.blockEquiv c a)
  invariant := by
    rw [← P.reindex_trans r.partEquiv r.blockEquiv
      s.partEquiv s.blockEquiv, r.invariant, s.invariant]

/-- A structure-preserving relabelling transports every block box to the relabelled box. -/
theorem reindex_box_eq (r : P.StructureRelabeling)
    (parts : ∀ c, Finset (A c)) :
    (P.box parts).reindex r.partEquiv r.blockEquiv =
      P.box (relabelParts r.partEquiv parts) := by
  calc
    (P.box parts).reindex r.partEquiv r.blockEquiv =
        (P.reindex r.partEquiv r.blockEquiv).box
          (relabelParts r.partEquiv parts) :=
      P.reindex_box r.partEquiv r.blockEquiv parts
    _ = P.box (relabelParts r.partEquiv parts) := by rw [r.invariant]

/-- Semantic form: relabelled boxes are tensor-isomorphic. -/
theorem box_isomorphic (r : P.StructureRelabeling)
    (parts : ∀ c, Finset (A c)) :
    Isomorphic (P.box parts).realize
      (P.box (relabelParts r.partEquiv parts)).realize := by
  have h := Isomorphic.partitionedReindex
    (P.box parts) r.partEquiv r.blockEquiv
  rw [r.reindex_box_eq parts] at h
  exact h

/-- A structure-preserving relabeling identifies every source constituent with the constituent
at its relabeled address.

The source address is written as the inverse image of `address`, matching the convention used by
`PartitionedTensor.reindex`.  This orientation is convenient for tensor powers: a permutation of
word positions transports the constituent indexed by the old word to the constituent indexed by
the permuted word.

Proof sketch: evaluate the tensor-level invariance equation at `address`.  By definition of
`reindex`, its constituent is obtained by applying the three local block equivalences to the
constituent at the inverse-image address, which is exactly the witness required by
`Tensor.Isomorphic`. -/
theorem constituent_isomorphic (r : P.StructureRelabeling)
    (address : BlockAddress A) :
    Isomorphic
      (P.constituent ((blockAddressCongr r.partEquiv).symm address))
      (P.constituent address) := by
  refine ⟨fun c ↦ r.blockEquiv c (address c), ?_⟩
  have h := congrArg (fun Q ↦ Q.constituent address) r.invariant
  change
    map (fun c ↦ (r.blockEquiv c (address c)).toLinearMap)
        (P.constituent ((blockAddressCongr r.partEquiv).symm address)) =
      P.constituent address
  simpa only [PartitionedTensor.reindex_constituent] using h

end PartitionedTensor.StructureRelabeling

/-- Equivalences transport complements of finite block sets to complements. -/
theorem relabelParts_univ_sdiff
    (e : ∀ c, Equiv.Perm (A c)) (holes : ∀ c, Finset (A c)) :
    relabelParts e (fun c ↦ Finset.univ \ holes c) =
      fun c ↦ Finset.univ \ relabelParts e holes c := by
  classical
  funext c
  ext a
  simp

/-- Two successive box restrictions intersect their surviving block sets. -/
theorem PartitionedTensor.box_box
    (P : PartitionedTensor (K := K) (A := A) V)
    (outer inner : ∀ c, Finset (A c)) :
    (P.box outer).box inner = P.box (fun c ↦ outer c ∩ inner c) := by
  classical
  apply PartitionedTensor.ext
  · ext address
    simp only [PartitionedTensor.box, PartitionedTensor.mem_select_support,
      Finset.mem_inter]
    constructor
    · rintro ⟨⟨hP, houter⟩, hinner⟩
      exact ⟨hP, fun c ↦ ⟨houter c, hinner c⟩⟩
    · rintro ⟨hP, hboth⟩
      exact ⟨⟨hP, fun c ↦ (hboth c).1⟩, fun c ↦ (hboth c).2⟩
  · rfl

@[simp] theorem PartitionedTensor.mem_box_support
    (P : PartitionedTensor (K := K) (A := A) V)
    (parts : ∀ c, Finset (A c)) (address : BlockAddress A) :
    address ∈ (P.box parts).support ↔
      address ∈ P.support ∧ ∀ c, address c ∈ parts c := by
  simp [PartitionedTensor.box]

namespace Restricts

/-- Box selection is exact variable zeroing on the three tensor legs. -/
theorem partitionedBox
    (P : PartitionedTensor (K := K) (A := A) V)
    (parts : ∀ c, Finset (A c)) :
    Restricts P.realize (P.box parts).realize :=
  partitionedSelect P fun c a ↦ a ∈ parts c

/-- A broken copy can be structure-preservingly relabelled and then zeroed to the part of an
arbitrary target box not hit by the moved holes.  This is the tensor-level all-non-hole input at
one recursive repair node. -/
theorem brokenBox_to_target_sdiff_movedHoles
    (P : PartitionedTensor (K := K) (A := A) V)
    (r : P.StructureRelabeling)
    (target holes : ∀ c, Finset (A c)) :
    Restricts
      (P.box (fun c ↦ Finset.univ \ holes c)).realize
      (P.box (fun c ↦ target c \ relabelParts r.partEquiv holes c)).realize := by
  classical
  let available : ∀ c, Finset (A c) := fun c ↦ Finset.univ \ holes c
  let movedHoles : ∀ c, Finset (A c) := relabelParts r.partEquiv holes
  let movedAvailable : ∀ c, Finset (A c) :=
    fun c ↦ Finset.univ \ movedHoles c
  have hmoved : relabelParts r.partEquiv available = movedAvailable := by
    dsimp [available, movedAvailable, movedHoles]
    exact relabelParts_univ_sdiff r.partEquiv holes
  have hrelabel : Restricts (P.box available).realize
      (P.box movedAvailable).realize := by
    have hiso := r.box_isomorphic available
    rw [hmoved] at hiso
    exact hiso.restricts
  have hselect : Restricts (P.box movedAvailable).realize
      ((P.box movedAvailable).box target).realize :=
    partitionedBox (P.box movedAvailable) target
  have hbox : (P.box movedAvailable).box target =
      P.box (fun c ↦ target c \ movedHoles c) := by
    rw [P.box_box movedAvailable target]
    apply PartitionedTensor.ext
    · ext address
      simp only [PartitionedTensor.mem_box_support, Finset.mem_inter,
        movedAvailable, Finset.mem_sdiff, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hP, h⟩
        exact ⟨hP, fun c ↦ ⟨(h c).2, (h c).1⟩⟩
      · rintro ⟨hP, h⟩
        exact ⟨hP, fun c ↦ ⟨(h c).2, (h c).1⟩⟩
    · rfl
  rw [hbox] at hselect
  exact hrelabel.trans hselect

/-- The previous theorem in the exact all-non-hole-box form consumed by one recursive node. -/
theorem brokenBox_to_allNonHole_splitBox
    (P : PartitionedTensor (K := K) (A := A) V)
    (r : P.StructureRelabeling)
    (target holes : ∀ c, Finset (A c)) :
    Restricts
      (P.box (fun c ↦ Finset.univ \ holes c)).realize
      (P.box (splitBoxParts target (relabelParts r.partEquiv holes)
        allNonHoleMask)).realize := by
  simpa only [splitBoxParts_allNonHole] using
    brokenBox_to_target_sdiff_movedHoles P r target holes

end Restricts

omit [∀ c, Fintype (A c)] in
private theorem mem_splitBoxParts_implies_mem_target
    (target holes : ∀ c, Finset (A c)) (mask : Leg → Bool)
    (address : BlockAddress A)
    (haddress : ∀ c, address c ∈ splitBoxParts target holes mask c) :
    ∀ c, address c ∈ target c := by
  intro c
  specialize haddress c
  cases hmask : mask c <;> simp [splitBoxParts, hmask] at haddress <;> exact haddress.1

omit [∀ c, Fintype (A c)] in
private theorem unique_split_mask
    (target holes : ∀ c, Finset (A c)) (address : BlockAddress A)
    (htarget : ∀ c, address c ∈ target c) :
    ∃! mask : Leg → Bool,
      ∀ c, address c ∈ splitBoxParts target holes mask c := by
  classical
  let chosen : Leg → Bool := fun c ↦ if address c ∈ holes c then false else true
  refine ⟨chosen, ?_, ?_⟩
  · intro c
    by_cases hc : address c ∈ holes c
    · simp [chosen, splitBoxParts, hc, htarget c]
    · simp [chosen, splitBoxParts, hc, htarget c]
  · intro mask hmask
    funext c
    specialize hmask c
    by_cases hc : address c ∈ holes c
    · have : mask c = false := by
        cases hmc : mask c
        · rfl
        · simp [splitBoxParts, hmc, hc] at hmask
      simp [chosen, hc, this]
    · have : mask c = true := by
        cases hmc : mask c
        · simp [splitBoxParts, hmc, hc] at hmask
        · rfl
      simp [chosen, hc, this]

omit [∀ c, Fintype (A c)] in
private theorem sum_splitMask_ite
    {M : Type*} [AddCommMonoid M]
    (target holes : ∀ c, Finset (A c)) (address : BlockAddress A) (value : M) :
    (∑ mask : Leg → Bool,
      if ∀ c, address c ∈ splitBoxParts target holes mask c then value else 0) =
      if ∀ c, address c ∈ target c then value else 0 := by
  classical
  by_cases htarget : ∀ c, address c ∈ target c
  · rw [if_pos htarget]
    obtain ⟨chosen, hchosen, hunique⟩ := unique_split_mask target holes address htarget
    rw [Finset.sum_eq_single chosen]
    · simp [hchosen]
    · intro mask _hmask hne
      rw [if_neg]
      intro hvalid
      exact hne (hunique mask hvalid)
    · simp
  · rw [if_neg htarget]
    apply Finset.sum_eq_zero
    intro mask _hmask
    rw [if_neg]
    intro hvalid
    exact htarget (mem_splitBoxParts_implies_mem_target target holes mask address hvalid)

/-- Exact eight-way decomposition of a target box into hole/non-hole boxes on all three legs. -/
theorem sum_splitBoxes_realize
    (P : PartitionedTensor (K := K) (A := A) V)
    (target holes : ∀ c, Finset (A c)) :
    (∑ mask : Leg → Bool, (P.box (splitBoxParts target holes mask)).realize) =
      (P.box target).realize := by
  classical
  unfold PartitionedTensor.box PartitionedTensor.realize PartitionedTensor.select realizePartition
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro address _haddress
  exact sum_splitMask_ite target holes address
    (map (blockInclude (K := K) (V := V) address) (P.constituent address))

namespace Restricts

/-- One exact recursive repair node.  If eight independent source tensors respectively restrict
to the eight hole/non-hole boxes, their indexed direct sum restricts to the unsplit target box.
In the recursive algorithm the all-`true` source is a relabelled broken copy and the other seven
sources are recursive calls. -/
theorem indexedDirectSum_splitBoxes_to_box
    {Source : (Leg → Bool) → Leg → Type x}
    [∀ mask c, AddCommMonoid (Source mask c)]
    [∀ mask c, Module K (Source mask c)]
    (P : PartitionedTensor (K := K) (A := A) V)
    (target holes : ∀ c, Finset (A c))
    (input : ∀ mask, Tensor3 K (Source mask))
    (hbox : ∀ mask, Restricts (input mask)
      (P.box (splitBoxParts target holes mask)).realize) :
    Restricts (Tensor.indexedDirectSum input) (P.box target).realize := by
  exact (Restricts.indexedDirectSum_to_sum hbox).trans
    (Restricts.of_eq (sum_splitBoxes_realize P target holes))

/-- Reindexed form of `indexedDirectSum_splitBoxes_to_box`.  The eight inputs may use any finite
index type equipped with an equivalence to the Boolean masks.  This is convenient for recursive
repair trees, where the index is `none` for the current broken copy and `some mask` for one of the
seven recursive children. -/
theorem indexedDirectSum_splitBoxes_to_box_equiv
    {I : Type x} [Fintype I]
    (branch : I ≃ (Leg → Bool))
    {Source : I → Leg → Type y}
    [∀ i c, AddCommMonoid (Source i c)]
    [∀ i c, Module K (Source i c)]
    (P : PartitionedTensor (K := K) (A := A) V)
    (target holes : ∀ c, Finset (A c))
    (input : ∀ i, Tensor3 K (Source i))
    (hbox : ∀ i, Restricts (input i)
      (P.box (splitBoxParts target holes (branch i))).realize) :
    Restricts (Tensor.indexedDirectSum input) (P.box target).realize := by
  apply (Restricts.indexedDirectSum_to_sum hbox).trans
  apply Restricts.of_eq
  calc
    (∑ i, (P.box (splitBoxParts target holes (branch i))).realize) =
        ∑ mask : Leg → Bool, (P.box (splitBoxParts target holes mask)).realize := by
      exact Fintype.sum_equiv branch _ _ (fun _ ↦ rfl)
    _ = (P.box target).realize := sum_splitBoxes_realize P target holes

end Restricts

end AlgebraicComplexity.Tensor
