/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.HoleRepair

/-!
# Retyping a finite partition box by its available labels

A box `P.box parts` still lives in the direct sums indexed by every ambient block label.  Hole
repair, however, must measure missing labels relative to the labels that actually belong to the
intact constituent.  This module replaces each finite allowed set `parts c` by its subtype and
proves that the ambient box restricts exactly to the resulting compact partitioned tensor.

The construction changes representation only.  It neither assumes nor proves any tensor-specific
counting statement.
-/

namespace AlgebraicComplexity.Tensor

open scoped DirectSum

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- The actual block-label type of one leg of a finite box. -/
abbrev BoxPart (parts : ∀ c, Finset (A c)) (c : Leg) :=
  {a : A c // a ∈ parts c}

/-- Block spaces after replacing ambient labels by the subtype of available labels. -/
abbrev BoxBlock (parts : ∀ c, Finset (A c)) (c : Leg) (a : BoxPart parts c) :=
  V c a.1

/-- Forget the membership proofs in a compact box address. -/
def boxPartAddressVal (parts : ∀ c, Finset (A c))
    (address : BlockAddress (BoxPart parts)) : BlockAddress A :=
  fun c ↦ (address c).1

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
@[simp] theorem boxPartAddressVal_apply (parts : ∀ c, Finset (A c))
    (address : BlockAddress (BoxPart parts)) (c : Leg) :
    boxPartAddressVal parts address c = (address c).1 :=
  rfl

/-- Every address in `P.box parts` canonically becomes an address over the compact part types. -/
noncomputable def boxSupportAddressEmbedding
    (P : PartitionedTensor (K := K) (A := A) V)
    (parts : ∀ c, Finset (A c)) :
    {address // address ∈ (P.box parts).support} ↪
      BlockAddress (BoxPart parts) where
  toFun address := fun c ↦
    ⟨address.1 c,
      ((PartitionedTensor.mem_box_support P parts address.1).mp address.2).2 c⟩
  inj' := by
    intro left right h
    apply Subtype.ext
    funext c
    exact congrArg Subtype.val (congrFun h c)

@[simp] theorem boxSupportAddressEmbedding_val_apply
    (P : PartitionedTensor (K := K) (A := A) V)
    (parts : ∀ c, Finset (A c))
    (address : {address // address ∈ (P.box parts).support}) (c : Leg) :
    ((boxSupportAddressEmbedding P parts address) c).1 = address.1 c :=
  rfl

@[simp] theorem boxPartAddressVal_boxSupportAddressEmbedding
    (P : PartitionedTensor (K := K) (A := A) V)
    (parts : ∀ c, Finset (A c))
    (address : {address // address ∈ (P.box parts).support}) :
    boxPartAddressVal parts (boxSupportAddressEmbedding P parts address) = address.1 := by
  rfl

/-- The compact partitioned tensor representing `P.box parts`.  Its part types have cardinality
exactly `(parts c).card`, rather than the cardinality of the ambient label alphabet. -/
noncomputable def compactBox
    (P : PartitionedTensor (K := K) (A := A) V)
    (parts : ∀ c, Finset (A c)) :
    PartitionedTensor (K := K) (A := BoxPart parts) (BoxBlock (V := V) parts) where
  support := Finset.univ.map (boxSupportAddressEmbedding P parts)
  constituent address := P.constituent (boxPartAddressVal parts address)

@[simp] theorem mem_compactBox_support_iff
    (P : PartitionedTensor (K := K) (A := A) V)
    (parts : ∀ c, Finset (A c))
    (address : BlockAddress (BoxPart parts)) :
    address ∈ (compactBox P parts).support ↔
      boxPartAddressVal parts address ∈ P.support := by
  classical
  constructor
  · intro haddress
    obtain ⟨source, _hsource, hsourceEq⟩ :=
      (Finset.mem_map.mp haddress)
    rw [← hsourceEq, boxPartAddressVal_boxSupportAddressEmbedding]
    exact ((PartitionedTensor.mem_box_support P parts source.1).mp source.2).1
  · intro haddress
    let source : {source // source ∈ (P.box parts).support} :=
      ⟨boxPartAddressVal parts address,
        (PartitionedTensor.mem_box_support P parts _).mpr
          ⟨haddress, fun c ↦ (address c).2⟩⟩
    apply Finset.mem_map.mpr
    refine ⟨source, Finset.mem_univ source, ?_⟩
    funext c
    apply Subtype.ext
    rfl

/-- Project the ambient partitioned space onto the available labels and reindex those labels by
their membership subtypes. -/
noncomputable def ambientToCompactBoxMap
    (parts : ∀ c, Finset (A c)) : ∀ c,
    PartitionedSpace K V c →ₗ[K]
      PartitionedSpace K (BoxBlock (V := V) parts) c := by
  classical
  exact fun c ↦ ∑ a : BoxPart parts c,
    DirectSum.lof K (BoxPart parts c) (BoxBlock (V := V) parts c) a ∘ₗ
      DirectSum.component K (A c) (V c) a.1

/-- On a block belonging to the box, the ambient projection is the corresponding compact block
inclusion. -/
theorem ambientToCompactBoxMap_comp_blockInclude
    (P : PartitionedTensor (K := K) (A := A) V)
    (parts : ∀ c, Finset (A c))
    (address : {address // address ∈ (P.box parts).support}) (c : Leg) :
    ambientToCompactBoxMap (K := K) (V := V) parts c ∘ₗ
        blockInclude (K := K) (V := V) address.1 c =
      blockInclude (K := K) (V := BoxBlock (V := V) parts)
        (boxSupportAddressEmbedding P parts address) c := by
  classical
  apply LinearMap.ext
  intro value
  simp only [LinearMap.comp_apply, ambientToCompactBoxMap,
    LinearMap.sum_apply, blockInclude]
  change (∑ a : BoxPart parts c,
      DirectSum.lof K (BoxPart parts c) (BoxBlock (V := V) parts c) a
        (DirectSum.component K (A c) (V c) a.1
          (DirectSum.lof K (A c) (V c) (address.1 c) value))) =
    DirectSum.lof K (BoxPart parts c) (BoxBlock (V := V) parts c)
      ⟨address.1 c,
        ((PartitionedTensor.mem_box_support P parts address.1).mp address.2).2 c⟩ value
  rw [Finset.sum_eq_single
    (⟨address.1 c,
      ((PartitionedTensor.mem_box_support P parts address.1).mp address.2).2 c⟩ :
        BoxPart parts c)]
  · change DirectSum.lof K (BoxPart parts c) (BoxBlock (V := V) parts c)
        ⟨address.1 c,
          ((PartitionedTensor.mem_box_support P parts address.1).mp address.2).2 c⟩
          (DirectSum.component K (A c) (V c) (address.1 c)
            (DirectSum.lof K (A c) (V c) (address.1 c) value)) =
      DirectSum.lof K (BoxPart parts c) (BoxBlock (V := V) parts c)
        ⟨address.1 c,
          ((PartitionedTensor.mem_box_support P parts address.1).mp address.2).2 c⟩ value
    rw [DirectSum.component.lof_self]
  · intro other _hother hne
    have hlabel : address.1 c ≠ other.1 := by
      intro heq
      apply hne
      apply Subtype.ext
      exact heq.symm
    simp [DirectSum.component.of, hlabel]
  · simp

/-- The explicit projection sends every embedded ambient-box constituent to the corresponding
embedded compact constituent. -/
theorem map_ambientToCompactBoxMap_block
    (P : PartitionedTensor (K := K) (A := A) V)
    (parts : ∀ c, Finset (A c))
    (address : {address // address ∈ (P.box parts).support}) :
    map (ambientToCompactBoxMap (K := K) (V := V) parts)
        (map (blockInclude (K := K) (V := V) address.1)
          (P.constituent address.1)) =
      map (blockInclude (K := K) (V := BoxBlock (V := V) parts)
          (boxSupportAddressEmbedding P parts address))
        ((compactBox P parts).constituent
          (boxSupportAddressEmbedding P parts address)) := by
  calc
    map (ambientToCompactBoxMap (K := K) (V := V) parts)
        (map (blockInclude (K := K) (V := V) address.1)
          (P.constituent address.1)) =
      map (fun c ↦ ambientToCompactBoxMap (K := K) (V := V) parts c ∘ₗ
        blockInclude (K := K) (V := V) address.1 c)
          (P.constituent address.1) := by
      rw [map_comp]
      rfl
    _ = map (blockInclude (K := K) (V := BoxBlock (V := V) parts)
          (boxSupportAddressEmbedding P parts address))
        (P.constituent address.1) := by
      congr 2
      funext c
      exact ambientToCompactBoxMap_comp_blockInclude P parts address c
    _ = map (blockInclude (K := K) (V := BoxBlock (V := V) parts)
          (boxSupportAddressEmbedding P parts address))
        ((compactBox P parts).constituent
          (boxSupportAddressEmbedding P parts address)) := by
      rfl

/-- Realizing an ambient box and projecting to the compact part types gives exactly
`compactBox`. -/
theorem map_ambientToCompactBoxMap_realize
    (P : PartitionedTensor (K := K) (A := A) V)
    (parts : ∀ c, Finset (A c)) :
    map (ambientToCompactBoxMap (K := K) (V := V) parts) (P.box parts).realize =
      (compactBox P parts).realize := by
  classical
  unfold PartitionedTensor.realize realizePartition
  rw [map_sum]
  let sourceTerm (address : {address // address ∈ (P.box parts).support}) :=
    map (ambientToCompactBoxMap (K := K) (V := V) parts)
      (map (blockInclude (K := K) (V := V) address.1)
        (P.constituent address.1))
  let targetTerm (address : BlockAddress (BoxPart parts)) :=
    map (blockInclude (K := K) (V := BoxBlock (V := V) parts) address)
      ((compactBox P parts).constituent address)
  calc
    ∑ address ∈ (P.box parts).support,
        map (ambientToCompactBoxMap (K := K) (V := V) parts)
          (map (blockInclude (K := K) (V := V) address)
            ((P.box parts).constituent address)) =
        ∑ address : {address // address ∈ (P.box parts).support},
          sourceTerm address := by
      simpa [sourceTerm, PartitionedTensor.box, PartitionedTensor.select] using
        (Finset.sum_subtype (P.box parts).support (fun _ ↦ Iff.rfl)
          (fun address ↦ map (ambientToCompactBoxMap (K := K) (V := V) parts)
            (map (blockInclude (K := K) (V := V) address)
              (P.constituent address))))
    _ = ∑ address : {address // address ∈ (P.box parts).support},
          targetTerm (boxSupportAddressEmbedding P parts address) := by
      apply Finset.sum_congr rfl
      intro address _haddress
      exact map_ambientToCompactBoxMap_block P parts address
    _ = ∑ address ∈ Finset.univ.map (boxSupportAddressEmbedding P parts),
          targetTerm address := by
      rw [Finset.sum_map]
    _ = ∑ address ∈ (compactBox P parts).support,
          map (blockInclude (K := K) (V := BoxBlock (V := V) parts) address)
            ((compactBox P parts).constituent address) := by
      rfl

/-! ## Damaged boxes inside one fixed compact ambient -/

/-- Labels of the compact available alphabet whose underlying ambient labels survive a further
box restriction. -/
noncomputable def compactBoxSubparts
    (available kept : ∀ c, Finset (A c)) (c : Leg) :
    Finset (BoxPart available c) := by
  classical
  exact Finset.univ.filter fun a ↦ a.1 ∈ kept c

omit [∀ c, Fintype (A c)] in
@[simp] theorem mem_compactBoxSubparts_iff
    (available kept : ∀ c, Finset (A c)) (c : Leg)
    (a : BoxPart available c) :
    a ∈ compactBoxSubparts available kept c ↔ a.1 ∈ kept c := by
  classical
  simp [compactBoxSubparts]

/-- An address of a smaller ambient box, regarded as an address over a fixed larger available
alphabet. -/
noncomputable def boxSubsetSupportAddressEmbedding
    (P : PartitionedTensor (K := K) (A := A) V)
    (available kept : ∀ c, Finset (A c))
    (hsubset : ∀ c, kept c ⊆ available c) :
    {address // address ∈ (P.box kept).support} ↪
      BlockAddress (BoxPart available) where
  toFun address := fun c ↦
    ⟨address.1 c, hsubset c
      (((PartitionedTensor.mem_box_support P kept address.1).mp address.2).2 c)⟩
  inj' := by
    intro left right h
    apply Subtype.ext
    funext c
    exact congrArg Subtype.val (congrFun h c)

@[simp] theorem boxSubsetSupportAddressEmbedding_val_apply
    (P : PartitionedTensor (K := K) (A := A) V)
    (available kept : ∀ c, Finset (A c))
    (hsubset : ∀ c, kept c ⊆ available c)
    (address : {address // address ∈ (P.box kept).support}) (c : Leg) :
    ((boxSubsetSupportAddressEmbedding P available kept hsubset address) c).1 =
      address.1 c :=
  rfl

/-- The support of a damaged box in the compact representation is exactly the retyped support
of the corresponding ambient damaged box. -/
theorem compactBox_box_support_eq_map
    (P : PartitionedTensor (K := K) (A := A) V)
    (available kept : ∀ c, Finset (A c))
    (hsubset : ∀ c, kept c ⊆ available c) :
    ((compactBox P available).box
      (compactBoxSubparts available kept)).support =
      Finset.univ.map
        (boxSubsetSupportAddressEmbedding P available kept hsubset) := by
  classical
  ext address
  simp only [PartitionedTensor.mem_box_support, mem_compactBox_support_iff,
    mem_compactBoxSubparts_iff, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hP, hkept⟩
    let source : {source // source ∈ (P.box kept).support} :=
      ⟨boxPartAddressVal available address,
        (PartitionedTensor.mem_box_support P kept _).mpr
          ⟨hP, hkept⟩⟩
    refine ⟨source, ?_⟩
    funext c
    apply Subtype.ext
    rfl
  · rintro ⟨source, hsource⟩
    have hsourceData :=
      (PartitionedTensor.mem_box_support P kept source.1).mp source.2
    rw [← hsource]
    have hval : boxPartAddressVal available
        (boxSubsetSupportAddressEmbedding P available kept hsubset source) =
          source.1 := by
      funext c
      rfl
    refine ⟨?_, ?_⟩
    · rw [hval]
      exact hsourceData.1
    · intro c
      exact hsourceData.2 c

/-- The ambient projection sends a block of a smaller box to its block in the fixed compact
available alphabet. -/
theorem ambientToCompactBoxMap_comp_blockInclude_of_subset
    (P : PartitionedTensor (K := K) (A := A) V)
    (available kept : ∀ c, Finset (A c))
    (hsubset : ∀ c, kept c ⊆ available c)
    (address : {address // address ∈ (P.box kept).support}) (c : Leg) :
    ambientToCompactBoxMap (K := K) (V := V) available c ∘ₗ
        blockInclude (K := K) (V := V) address.1 c =
      blockInclude (K := K) (V := BoxBlock (V := V) available)
        (boxSubsetSupportAddressEmbedding P available kept hsubset address) c := by
  classical
  apply LinearMap.ext
  intro value
  simp only [LinearMap.comp_apply, ambientToCompactBoxMap,
    LinearMap.sum_apply, blockInclude]
  change (∑ a : BoxPart available c,
      DirectSum.lof K (BoxPart available c) (BoxBlock (V := V) available c) a
        (DirectSum.component K (A c) (V c) a.1
          (DirectSum.lof K (A c) (V c) (address.1 c) value))) =
    DirectSum.lof K (BoxPart available c) (BoxBlock (V := V) available c)
      ⟨address.1 c, hsubset c
        (((PartitionedTensor.mem_box_support P kept address.1).mp address.2).2 c)⟩ value
  rw [Finset.sum_eq_single
    (⟨address.1 c, hsubset c
      (((PartitionedTensor.mem_box_support P kept address.1).mp address.2).2 c)⟩ :
        BoxPart available c)]
  · change DirectSum.lof K (BoxPart available c) (BoxBlock (V := V) available c)
        ⟨address.1 c, hsubset c
          (((PartitionedTensor.mem_box_support P kept address.1).mp address.2).2 c)⟩
          (DirectSum.component K (A c) (V c) (address.1 c)
            (DirectSum.lof K (A c) (V c) (address.1 c) value)) =
      DirectSum.lof K (BoxPart available c) (BoxBlock (V := V) available c)
        ⟨address.1 c, hsubset c
          (((PartitionedTensor.mem_box_support P kept address.1).mp address.2).2 c)⟩ value
    rw [DirectSum.component.lof_self]
  · intro other _hother hne
    have hlabel : address.1 c ≠ other.1 := by
      intro heq
      apply hne
      apply Subtype.ext
      exact heq.symm
    simp [DirectSum.component.of, hlabel]
  · simp

/-- Realizing a smaller ambient box and projecting into one fixed compact alphabet gives the
corresponding damaged box of that compact tensor. -/
theorem map_ambientToCompactBoxMap_realize_of_subset
    (P : PartitionedTensor (K := K) (A := A) V)
    (available kept : ∀ c, Finset (A c))
    (hsubset : ∀ c, kept c ⊆ available c) :
    map (ambientToCompactBoxMap (K := K) (V := V) available)
        (P.box kept).realize =
      ((compactBox P available).box
        (compactBoxSubparts available kept)).realize := by
  classical
  unfold PartitionedTensor.realize realizePartition
  rw [map_sum]
  rw [compactBox_box_support_eq_map P available kept hsubset]
  let sourceTerm (address : {address // address ∈ (P.box kept).support}) :=
    map (ambientToCompactBoxMap (K := K) (V := V) available)
      (map (blockInclude (K := K) (V := V) address.1)
        (P.constituent address.1))
  let targetTerm (address : BlockAddress (BoxPart available)) :=
    map (blockInclude (K := K) (V := BoxBlock (V := V) available) address)
      ((compactBox P available).constituent address)
  calc
    ∑ address ∈ (P.box kept).support,
        map (ambientToCompactBoxMap (K := K) (V := V) available)
          (map (blockInclude (K := K) (V := V) address)
            ((P.box kept).constituent address)) =
        ∑ address : {address // address ∈ (P.box kept).support},
          sourceTerm address := by
      simpa [sourceTerm, PartitionedTensor.box, PartitionedTensor.select] using
        (Finset.sum_subtype (P.box kept).support (fun _ ↦ Iff.rfl)
          (fun address ↦ map
            (ambientToCompactBoxMap (K := K) (V := V) available)
              (map (blockInclude (K := K) (V := V) address)
                (P.constituent address))))
    _ = ∑ address : {address // address ∈ (P.box kept).support},
        targetTerm
          (boxSubsetSupportAddressEmbedding P available kept hsubset address) := by
      apply Finset.sum_congr rfl
      intro address _haddress
      calc
        sourceTerm address =
            map (fun c ↦
              ambientToCompactBoxMap (K := K) (V := V) available c ∘ₗ
                blockInclude (K := K) (V := V) address.1 c)
              (P.constituent address.1) := by
          rw [map_comp]
          rfl
        _ = targetTerm
            (boxSubsetSupportAddressEmbedding P available kept hsubset address) := by
          dsimp only [targetTerm]
          congr 2
          funext c
          exact ambientToCompactBoxMap_comp_blockInclude_of_subset
            P available kept hsubset address c
    _ = ∑ address ∈ Finset.univ.map
          (boxSubsetSupportAddressEmbedding P available kept hsubset),
        targetTerm address := by
      rw [Finset.sum_map]
    _ = ∑ address ∈ Finset.univ.map
          (boxSubsetSupportAddressEmbedding P available kept hsubset),
        map (blockInclude (K := K) (V := BoxBlock (V := V) available) address)
          (((compactBox P available).box
            (compactBoxSubparts available kept)).constituent address) := by
      rfl

namespace Restricts

/-- The ambient representation of a finite box restricts to its compact, honestly-sized
partition representation. -/
theorem box_to_compactBox
    (P : PartitionedTensor (K := K) (A := A) V)
    (parts : ∀ c, Finset (A c)) :
    Restricts (P.box parts).realize (compactBox P parts).realize :=
  ⟨ambientToCompactBoxMap (K := K) (V := V) parts,
    map_ambientToCompactBoxMap_realize P parts⟩

/-- A damaged ambient box restricts to the corresponding damaged box of one fixed compact
available alphabet. -/
theorem box_to_compactBox_box
    (P : PartitionedTensor (K := K) (A := A) V)
    (available kept : ∀ c, Finset (A c))
    (hsubset : ∀ c, kept c ⊆ available c) :
    Restricts (P.box kept).realize
      ((compactBox P available).box
        (compactBoxSubparts available kept)).realize :=
  ⟨ambientToCompactBoxMap (K := K) (V := V) available,
    map_ambientToCompactBoxMap_realize_of_subset P available kept hsubset⟩

end Restricts

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
@[simp] theorem Fintype_card_BoxPart
    (parts : ∀ c, Finset (A c)) (c : Leg) :
    Fintype.card (BoxPart parts c) = (parts c).card := by
  exact Fintype.card_coe _

/-! ## Structure relabelings of compact boxes -/

/-- Restrict a permutation to an invariant finite set, with inverse values definitionally equal
to the ambient inverse permutation. -/
abbrev invariantFinsetSubtypePerm {α : Type*} [Fintype α] [DecidableEq α]
    (e : Equiv.Perm α) (parts : Finset α)
    (hinvariant : ∀ a, a ∈ parts ↔ e a ∈ parts) :
    Equiv.Perm {a : α // a ∈ parts} where
  toFun a := ⟨e a.1, (hinvariant a.1).1 a.2⟩
  invFun a := ⟨e.symm a.1, (hinvariant (e.symm a.1)).2 (by simpa using a.2)⟩
  left_inv a := by
    apply Subtype.ext
    exact e.symm_apply_apply a.1
  right_inv a := by
    apply Subtype.ext
    exact e.apply_symm_apply a.1

@[simp] theorem invariantFinsetSubtypePerm_apply_val
    {α : Type*} [Fintype α] [DecidableEq α]
    (e : Equiv.Perm α) (parts : Finset α)
    (hinvariant : ∀ a, a ∈ parts ↔ e a ∈ parts)
    (a : {a : α // a ∈ parts}) :
    (invariantFinsetSubtypePerm e parts hinvariant a).1 = e a.1 :=
  rfl

@[simp] theorem invariantFinsetSubtypePerm_symm_apply_val
    {α : Type*} [Fintype α] [DecidableEq α]
    (e : Equiv.Perm α) (parts : Finset α)
    (hinvariant : ∀ a, a ∈ parts ↔ e a ∈ parts)
    (a : {a : α // a ∈ parts}) :
    ((invariantFinsetSubtypePerm e parts hinvariant).symm a).1 = e.symm a.1 :=
  rfl

/-- Restrict an ambient structure relabeling to a finite invariant alphabet.  This is the
representation bridge needed by hole repair: the part permutation is restricted to the subtype,
while the block equivalences and tensor invariance are inherited from the ambient tensor. -/
noncomputable def PartitionedTensor.StructureRelabeling.compactBox
    {P : PartitionedTensor (K := K) (A := A) V}
    (r : P.StructureRelabeling) (parts : ∀ c, Finset (A c))
    (hinvariant : ∀ c a,
      a ∈ parts c ↔ r.partEquiv c a ∈ parts c) :
    (compactBox P parts).StructureRelabeling where
  partEquiv := fun c ↦ invariantFinsetSubtypePerm
    (r.partEquiv c) (parts c) (hinvariant c)
  blockEquiv := fun c b ↦ r.blockEquiv c b.1
  invariant := by
    classical
    apply PartitionedTensor.ext
    · apply Finset.ext
      intro address
      rw [PartitionedTensor.reindex_support, Finset.mem_map,
        mem_compactBox_support_iff]
      constructor
      · rintro ⟨source, hsource, hsourceAddress⟩
        have hambient : boxPartAddressVal parts source ∈ P.support :=
          (mem_compactBox_support_iff P parts source).1 hsource
        have hreindexed :
            (fun c ↦ r.partEquiv c (boxPartAddressVal parts source c)) ∈
              (P.reindex r.partEquiv r.blockEquiv).support := by
          apply Finset.mem_map.mpr
          refine ⟨boxPartAddressVal parts source, hambient, ?_⟩
          rfl
        rw [r.invariant] at hreindexed
        have hval : boxPartAddressVal parts address =
            fun c ↦ r.partEquiv c (boxPartAddressVal parts source c) := by
          funext c
          have hc := congrArg (fun a ↦ (a c).1) hsourceAddress
          simpa using hc.symm
        simpa [hval] using hreindexed
      · intro haddress
        let ambientSource : BlockAddress A :=
          fun c ↦ (r.partEquiv c).symm (boxPartAddressVal parts address c)
        have hsourceMem : ambientSource ∈ P.support := by
          have hreindexed : boxPartAddressVal parts address ∈
              (P.reindex r.partEquiv r.blockEquiv).support := by
            rw [r.invariant]
            exact haddress
          obtain ⟨source, hsource, hsourceEq⟩ := Finset.mem_map.mp hreindexed
          have heq : source = ambientSource := by
            funext c
            have hc := congrArg (fun a ↦ a c) hsourceEq
            apply (r.partEquiv c).injective
            simpa [ambientSource] using hc
          simpa [heq] using hsource
        let compactSource : BlockAddress (BoxPart parts) := fun c ↦
          ⟨ambientSource c, by
            apply (hinvariant c (ambientSource c)).mpr
            simp [ambientSource]⟩
        refine ⟨compactSource, ?_, ?_⟩
        · exact (mem_compactBox_support_iff P parts compactSource).2 hsourceMem
        · funext c
          apply Subtype.ext
          simp [compactSource, ambientSource]
    · funext address
      have hambient := congrArg
        (fun Q : PartitionedTensor (K := K) (A := A) V ↦
          Q.constituent (boxPartAddressVal parts address)) r.invariant
      have hsource :
          boxPartAddressVal parts
              ((blockAddressCongr (fun c ↦ invariantFinsetSubtypePerm
                (r.partEquiv c) (parts c) (hinvariant c))).symm address) =
            (blockAddressCongr r.partEquiv).symm
              (boxPartAddressVal parts address) := rfl
      change
        map (fun c ↦ (r.blockEquiv c (address c).1).toLinearMap)
            (P.constituent
              (boxPartAddressVal parts
                ((blockAddressCongr (fun c ↦ invariantFinsetSubtypePerm
                  (r.partEquiv c) (parts c) (hinvariant c))).symm address))) =
          P.constituent (boxPartAddressVal parts address)
      simp only [PartitionedTensor.reindex_constituent] at hambient
      cases hsource
      exact hambient

@[simp] theorem PartitionedTensor.StructureRelabeling.compactBox_partEquiv_apply_val
    {P : PartitionedTensor (K := K) (A := A) V}
    (r : P.StructureRelabeling) (parts : ∀ c, Finset (A c))
    (hinvariant : ∀ c a,
      a ∈ parts c ↔ r.partEquiv c a ∈ parts c)
    (c : Leg) (a : BoxPart parts c) :
    ((r.compactBox parts hinvariant).partEquiv c a).1 = r.partEquiv c a.1 :=
  rfl

end AlgebraicComplexity.Tensor
