/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.HoleRepair
import AlgebraicComplexity.Tensor.PartitionedCoarsening
import AlgebraicComplexity.Tensor.PartitionedPower
import AlgebraicComplexity.Tensor.TypeExtraction

/-!
# Extraction on a coarsened partition alphabet

`PartitionedTensor.coarsen` regroups block labels along arbitrary finite maps; the maps are not
required to be injective.  `Isomorphic.partitionedCoarsen` proves that this regrouping leaves the
realized tensor unchanged.  This file provides the compositional interface needed by extraction
clients: a restriction proved after passing to the quotient alphabet can be pulled back to the
original realization, and selection, exact word types, and hole repair can be instantiated
directly on that quotient alphabet.

The point of these theorems is logical rather than algorithmic.  Hashing or repair code may use
only the coarsened labels.  It never needs to choose a representative of a coarsening fiber, and
no injectivity hypothesis on the coarsening maps occurs below.
-/

namespace AlgebraicComplexity.Tensor

universe u v w x y

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Universe-explicit spelling of the positive power of a coarsened partition.  The extra
`max v w` records that a coarse block is a direct sum indexed by a fiber of the fine alphabet.
Keeping this adapter here prevents downstream quotient clients from having to supply universe
arguments by hand. -/
noncomputable abbrev PartitionedTensor.coarsenedPositivePower
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) :=
  @PartitionedTensor.positivePower.{u, max v w, x} K _ B _ _
    (CoarsenedBlockSpace (V := V) f) _ _ (P.coarsen f) n

/-- Pull a legwise predicate on quotient labels back to whole fibers of fine labels. -/
def coarseningPreimagePredicate (f : ∀ c, A c → B c)
    (keep : ∀ c, B c → Prop) : ∀ c, A c → Prop :=
  fun c a ↦ keep c (f c a)

/-- Selecting whole coarsening fibers before regrouping and selecting their quotient labels
after regrouping expose the same support. -/
theorem PartitionedTensor.coarsen_select_preimage_support
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c)
    (keep : ∀ c, B c → Prop) [∀ c b, Decidable (keep c b)] :
    ((P.select (fun c a ↦ keep c (f c a))).coarsen f).support =
      ((P.coarsen f).select keep).support := by
  classical
  ext target
  simp only [PartitionedTensor.coarsen_support, Finset.mem_image,
    PartitionedTensor.mem_select_support]
  constructor
  · rintro ⟨source, ⟨hsource, hkeep⟩, rfl⟩
    exact ⟨⟨source, hsource, rfl⟩, hkeep⟩
  · rintro ⟨⟨source, hsource, rfl⟩, hkeep⟩
    exact ⟨source, ⟨hsource, hkeep⟩, rfl⟩

/-- Whole-fiber selection commutes with coarsening at the realized-tensor level.  Constituents
outside the recorded support may differ as certificate data, so realization equality is the
correct extensional statement. -/
theorem PartitionedTensor.coarsen_select_preimage_realize
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c)
    (keep : ∀ c, B c → Prop) [∀ c b, Decidable (keep c b)] :
    ((P.select (fun c a ↦ keep c (f c a))).coarsen f).realize =
      ((P.coarsen f).select keep).realize := by
  classical
  apply PartitionedTensor.realize_eq_of_support_eq
    _ _ (P.coarsen_select_preimage_support f keep)
  intro target htarget
  have htarget' : target ∈ ((P.coarsen f).select keep).support :=
    (P.coarsen_select_preimage_support f keep) ▸ htarget
  have hkeep : ∀ c, keep c (target c) :=
    (PartitionedTensor.mem_select_support (P.coarsen f) keep target).mp htarget' |>.2
  change coarsenedConstituent
      (P.select (fun c a ↦ keep c (f c a))) f target =
    coarsenedConstituent P f target
  unfold coarsenedConstituent
  simp only [PartitionedTensor.select]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro source hsource hnotSelected
  have hnotKeep : ¬ ∀ c, keep c (f c (source c)) := by
    simpa only [Finset.mem_filter, hsource, true_and,
      coarseningPreimagePredicate] using hnotSelected
  have hne : coarsenBlockAddress f source ≠ target := by
    intro heq
    apply hnotKeep
    intro c
    rw [← coarsenBlockAddress_apply f source c, heq]
    exact hkeep c
  simp [coarsenedTerm, hne]

namespace Isomorphic

/-- Once tensor contexts have been separated into an actual indexed direct sum, each context may
use its own legwise coarsening map.  This theorem does not itself provide the context separation:
that must be established by hashing or projection-closed zeroing before context-dependent
quotients are applied. -/
theorem indexedDirectSum_partitionedCoarsen
    {I : Type y} [Fintype I]
    (P : I → PartitionedTensor (K := K) (A := A) V)
    (f : I → ∀ c, A c → B c) :
    Isomorphic (Tensor.indexedDirectSum (fun i ↦ (P i).realize))
      (Tensor.indexedDirectSum (fun i ↦ ((P i).coarsen (f i)).realize)) :=
  Isomorphic.indexedDirectSum fun i ↦ Isomorphic.partitionedCoarsen (P i) (f i)

end Isomorphic

namespace Restricts

/-- Coarsening is, in particular, an exact restriction from the original realization.  The
stronger isomorphism is `Isomorphic.partitionedCoarsen`; this direction is convenient for
composing with zeroing, hashing, type extraction, or repair performed on the coarse alphabet. -/
theorem partitionedCoarsen
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) :
    Restricts P.realize (P.coarsen f).realize :=
  (Isomorphic.partitionedCoarsen P f).restricts

/-- Pull an arbitrary downstream coarse-alphabet restriction back through the coarsening
isomorphism.  This is the generic quotient-interface bridge. -/
theorem partitionedCoarsen_trans
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c)
    {W : Leg → Type y} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    {T : Tensor3 K W}
    (h : Restricts (P.coarsen f).realize T) :
    Restricts P.realize T :=
  (partitionedCoarsen P f).trans h

/-- Legwise variable selection can be carried out after arbitrary coarsening and remains a
restriction of the original tensor. -/
theorem partitionedCoarsen_select
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c)
    (keep : ∀ c, B c → Prop) [∀ c b, Decidable (keep c b)] :
    Restricts P.realize ((P.coarsen f).select keep).realize :=
  partitionedCoarsen_trans P f (partitionedSelect (P.coarsen f) keep)

/-- Cartesian-box selection can be performed on the coarsened labels. -/
theorem partitionedCoarsen_box
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c)
    (parts : ∀ c, Finset (B c)) :
    Restricts P.realize ((P.coarsen f).box parts).realize :=
  partitionedCoarsen_trans P f (partitionedBox (P.coarsen f) parts)

/-- Tensor powers preserve the quotient-interface restriction. -/
theorem power_partitionedCoarsen
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (m : ℕ) :
    Restricts (Tensor.power P.realize m)
      (Tensor.power (P.coarsen f).realize m) :=
  (partitionedCoarsen P f).power m

/-- Select an arbitrary exact predicate on positive words of coarsened labels.  Thus exact
profile or type predicates can be formulated on the quotient alphabet itself, with no choice of
fine representatives. -/
theorem power_partitionedCoarsen_positivePowerSelect
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ)
    (keep : ∀ c, PositiveWord (B c) n → Prop)
    [∀ c word, Decidable (keep c word)] :
    Restricts (Tensor.power P.realize (n + 1))
      ((P.coarsenedPositivePower f n).select keep).realize := by
  let Q : PartitionedTensor.{u, max (max u v) w, x}
      (K := K) (A := B) (CoarsenedBlockSpace (V := V) f) := P.coarsen f
  exact (power_partitionedCoarsen P f (n + 1)).trans <|
    (Isomorphic.power_partitionedPositivePower Q n).restricts.trans
      (partitionedSelect (P.coarsenedPositivePower f n) keep)

end Restricts

/-! ## Exact multiplicity types on the quotient alphabet -/

/-- Mapping a positive word along an arbitrary finite alphabet map pushes its exact
multiplicity type forward by summing over fibers.  Injectivity of `f` is neither assumed nor
needed. -/
theorem positiveWordMap_mem_positiveTypeClass
    {I : Type w} {J : Type x} [Fintype I] [Fintype J]
    (f : I → J) (n : ℕ) (a : I → ℕ) (word : PositiveWord I n)
    (hword : word ∈ positiveTypeClass I n a) :
    positiveWordMap f n word ∈
      positiveTypeClass J n (WordType.mappedType f a) := by
  rw [mem_positiveTypeClass, positiveWordEquiv_map,
    WordType.multiplicity_comp_eq_mappedType,
    mem_positiveTypeClass.mp hword]

/-- Select one exact multiplicity type independently on each leg of a coarsened positive power. -/
noncomputable def PartitionedTensor.selectCoarsenedPositiveTypes
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) (a : ∀ c, B c → ℕ) := by
  classical
  exact (P.coarsenedPositivePower f n).select fun c word ↦
    word ∈ positiveTypeClass (B c) n (a c)

@[simp] theorem PartitionedTensor.mem_selectCoarsenedPositiveTypes_support
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) (a : ∀ c, B c → ℕ)
    (address : BlockAddress (fun c ↦ PositiveWord (B c) n)) :
    address ∈ (P.selectCoarsenedPositiveTypes f n a).support ↔
      address ∈ (P.coarsenedPositivePower f n).support ∧
        ∀ c, address c ∈ positiveTypeClass (B c) n (a c) := by
  classical
  simp [PartitionedTensor.selectCoarsenedPositiveTypes]

/-- The original tensor power restricts directly to any exact coarse multiplicity type. -/
theorem Restricts.power_selectCoarsenedPositiveTypes
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) (a : ∀ c, B c → ℕ) :
    Restricts (Tensor.power P.realize (n + 1))
      (P.selectCoarsenedPositiveTypes f n a).realize := by
  classical
  exact power_partitionedCoarsen_positivePowerSelect P f n
    (fun c word ↦ word ∈ positiveTypeClass (B c) n (a c))

/-! ## Hole repair on quotient labels -/

/-- The generic eight-way repair identity specializes directly to coarsened labels.  The
coarsening maps may identify arbitrarily many fine blocks; repair only sees finite coarse boxes
and coarse hole sets. -/
theorem Restricts.indexedDirectSum_coarsenedSplitBoxes_to_box
    {Source : (Leg → Bool) → Leg → Type y}
    [∀ mask c, AddCommMonoid (Source mask c)]
    [∀ mask c, Module K (Source mask c)]
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c)
    (target holes : ∀ c, Finset (B c))
    (input : ∀ mask, Tensor3 K (Source mask))
    (hbox : ∀ mask, Restricts (input mask)
      (((P.coarsen f).box (splitBoxParts target holes mask)).realize)) :
    Restricts (Tensor.indexedDirectSum input)
      (((P.coarsen f).box target).realize) :=
  indexedDirectSum_splitBoxes_to_box (P.coarsen f) target holes input hbox

end AlgebraicComplexity.Tensor
