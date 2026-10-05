/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainMarginalSelect
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoHoleSupplier
import AlgebraicComplexity.Tensor.GroupedCompatibilityZeroing

set_option autoImplicit false

/-!
# The retained direct sum without legwise injectivity

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoPlainRetainedSum.lean`'s
`dwz63_plainRetainedDirectSum` splits the retained subpartition with
`Tensor.Restricts.partitionedLegwiseInjective_to_indexedDirectSum`, whose premise
`IsLegwiseInjective` is `∀ c, Set.InjOn (· c)` on the **coarse** retained addresses --- all three
legs.  That premise is **false** on `[DuanWuZhou2022]`'s route, and provably so: the retained
triples deliberately share coarse `Z`-blocks (`global_value.tex:28`), and
`Examples/DuanWuZhouLevelTwoPlainZCeiling.lean`'s
`card_dwz63PlainJointIsolatedSupport_le_card_zWords` shows that a `Z`-isolated retained set is
capped strictly below any copy count at the true rate.  So `hlegwise` and `hcount` are jointly
unsatisfiable, and no downstream fine-level fact can discharge a coarse-level premise.

This module replaces it.  The separation of copies happens **one level down**, on the fine
partition, and it separates them only up to their coarse constituent --- which is all a direct sum
needs, because the summands are indexed by coarse constituents.  That is exactly the content of
`Tensor/GroupedCompatibilityZeroing.lean`, whose `HasGroupUniqueLegFibers` weakens
`HasUniqueLegFibers` from "the label determines the address" to "the label determines the coarse
group"; the audit's observation that `Tensor/CompatibilityZeroing.lean` is its `group := id`
instance is the reason nothing has to be re-proved here.

## The three legs

* **`X`** --- free.  The group of a fine address is *defined* by reading its `X`-word, coarsening
  it, and looking up the unique retained address with that coarse `X`-word
  (`dwz63PlainCoarseGroup`).  A function of `s .X` trivially satisfies
  `HasGroupUniqueLegFibers _ _ _ .X`, so the hash's `dwz63_x_injOn_plainJointRetained` is used not
  to prove group-readability but to make the lookup *correct*
  (`dwz63PlainCoarseGroup_eq_of_x`).
* **`Y`** --- `y_injectiveOn_markedXYIsolatedPowerAddresses`, the engine's certificate, in the same
  shape: distinct retained addresses have distinct coarse `Y`-words, so a fine `Y`-word determines
  the retained address too.
* **`Z`** --- the holes.  Coarse `Z`-blocks are shared, so no coarse fact can help; what separates
  is Additional Zeroing-Out Step 2 (`global_value.tex:74-89`), which deletes every small block
  compatible with more than one retained triple or useless for the one it has.  The surviving
  blocks are useful for exactly one triple (`usefulFor_of_notMem_dwz63HoleSet`), and that is
  precisely `IsGroupUniquelyCompatible` for `compatible z s := usefulFor z (group s)`.  The hole
  set enters as a **parameter**, in the shape `Examples/DuanWuZhouLevelTwoLocalizedStage.lean`'s
  `dwz63_localizedStage_of_segmentedRepair` already carries it (`holes`, `hbudget`).

## What is abstract, and why

The fine layer is carried by a partitioned tensor `fine`, a coarsening reader
`coarse : ∀ c, Afine c → PositiveWord (Fin 5) n`, and the premise that every fine address of
`fine` coarsens into the retained family.  Nothing here depends on which fine partition it is, and
the plain route has two candidates in flight --- the depth-one positive power and the segmented
localized splitting power --- so pinning one would freeze a choice this lemma does not make.  The
`Z` relations `compatibleWith` and `usefulFor` are likewise abstract, with `dwz63HoleSet`'s two
rules quoted as `hholes`; a client instantiating them at `dwz63HoleSet` gets `hholes` from
`usefulFor_of_notMem_dwz63HoleSet` verbatim.

## How it plugs in

`Examples/DuanWuZhouLevelTwoLocalizedStage.lean`'s `dwz63_localizedStage_of_segmentedRepair`
opens with `dwz63_plainRetainedDirectSum` and then maps each retained constituent to the broken
reference leaf.  Replacing that opening by `dwz63_plainGroupedStage_of_brokenLeaf` deletes
`hlegwise` and changes nothing else: the chain

`hstage ≫ dwz63_plainGroupedBrokenDirectSum ≫ Restricts.indexedDirectSum hleaf ≫
 restricts_indexedDirectSum_segmentedLocalizedHoleRepair_batched`

lands on exactly `dwz63_localizedStage_of_segmentedRepair`'s conclusion.  That composition was
checked against the committed hole-repair lemma before this module was landed; only the two new
premises appear, `hstage` (the plain power reaches the fine partition) and `hleaf` (each broken
group reaches the broken reference leaf), both of which the tensor lane already owns.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6, and `hole_lemma.tex`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v w x

/-! ## The coarse group of a fine address -/

section Group

variable {n : ℕ} {Afine : Leg → Type w}

/-- **The retained coarse address a fine address belongs to**, read off its `X`-word.

`coarse c` sends a fine leg word to its coarse leg word; the group of a fine address is the unique
retained address carrying its coarse `X`-word.  Reading a *single* leg is deliberate: the resulting
function factors through `s .X`, so `HasGroupUniqueLegFibers` on the `X` leg holds for every
ambient family with no hypothesis at all. -/
noncomputable def dwz63PlainCoarseGroup
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (coarse : ∀ c, Afine c → PositiveWord (Fin 5) n) (a₀ : retained) :
    BlockAddress Afine → retained := fun s ↦
  if h : ∃ a : retained, (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) .X =
      coarse .X (s .X) then h.choose else a₀

/-- **The lookup is correct**, given the hash's `X`-injectivity on the retained family: if some
retained address carries the coarse `X`-word of `s`, the group *is* that address. -/
theorem dwz63PlainCoarseGroup_eq_of_x
    {retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)}
    {coarse : ∀ c, Afine c → PositiveWord (Fin 5) n} {a₀ : retained}
    (hX : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .X)
      (retained : Set _))
    {s : BlockAddress Afine} {a : retained}
    (ha : (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) .X = coarse .X (s .X)) :
    dwz63PlainCoarseGroup retained coarse a₀ s = a := by
  classical
  have hex : ∃ b : retained, (b : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) .X =
      coarse .X (s .X) := ⟨a, ha⟩
  rw [dwz63PlainCoarseGroup, dif_pos hex]
  refine Subtype.ext (hX hex.choose.2 a.2 ?_)
  show (hex.choose : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) .X =
    (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) .X
  rw [hex.choose_spec, ha]

/-- **The `X` leg reads the group, with no hypothesis.**  The group is a function of `s .X`. -/
theorem dwz63PlainCoarseGroup_hasGroupUniqueLegFibers_x
    [∀ c, Fintype (Afine c)] [∀ c, DecidableEq (Afine c)]
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (coarse : ∀ c, Afine c → PositiveWord (Fin 5) n) (a₀ : retained)
    (ambient : Finset (BlockAddress Afine)) :
    HasGroupUniqueLegFibers ambient ambient
      (dwz63PlainCoarseGroup retained coarse a₀) .X := by
  refine ⟨Finset.Subset.rfl, ?_⟩
  intro s _ t _ hlabel
  simp only [dwz63PlainCoarseGroup, hlabel]

/-- **The `Y` leg reads the group**, from the engine's `Y`-injectivity certificate.

Every ambient fine address coarsens into the retained family (`hcover`); its coarse `Y`-word
therefore names a retained address, `Y`-injectivity makes that address unique, and
`dwz63PlainCoarseGroup_eq_of_x` identifies it with the group. -/
theorem dwz63PlainCoarseGroup_hasGroupUniqueLegFibers_y
    [∀ c, Fintype (Afine c)] [∀ c, DecidableEq (Afine c)]
    {retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)}
    {coarse : ∀ c, Afine c → PositiveWord (Fin 5) n} {a₀ : retained}
    {ambient : Finset (BlockAddress Afine)}
    (hX : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .X)
      (retained : Set _))
    (hY : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .Y)
      (retained : Set _))
    (hcover : ∀ s ∈ ambient, ∃ a : retained,
      ∀ c, (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) c = coarse c (s c)) :
    HasGroupUniqueLegFibers ambient ambient
      (dwz63PlainCoarseGroup retained coarse a₀) .Y := by
  refine ⟨Finset.Subset.rfl, ?_⟩
  intro s hs t ht hlabel
  obtain ⟨a, ha⟩ := hcover s hs
  obtain ⟨b, hb⟩ := hcover t ht
  have hab : a = b := by
    refine Subtype.ext (hY a.2 b.2 ?_)
    show (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) .Y =
      (b : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) .Y
    rw [ha .Y, hb .Y, hlabel]
  rw [dwz63PlainCoarseGroup_eq_of_x hX (ha .X), dwz63PlainCoarseGroup_eq_of_x hX (hb .X), hab]

end Group

/-! ## The `Z` leg: Additional Zeroing-Out Step 2 -/

section Holes

variable {n : ℕ} {Afine : Leg → Type w}
variable [∀ c, Fintype (Afine c)] [∀ c, DecidableEq (Afine c)]
variable {retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)}

/-- **The `Z` compatibility relation of Step 2**: a small block is compatible with a fine address
exactly when it is *useful* for that address's retained triple. -/
def dwz63PlainUsefulCompatible
    (group : BlockAddress Afine → retained)
    (usefulFor : Afine .Z → retained → Prop) :
    Afine .Z → BlockAddress Afine → Prop :=
  fun z s ↦ usefulFor z (group s)

/-- **The support left by Step 2 on the fine `Z` leg.** -/
noncomputable def dwz63PlainGroupedZSupport
    (ambient : Finset (BlockAddress Afine))
    (group : BlockAddress Afine → retained)
    (usefulFor : Afine .Z → retained → Prop) : Finset (BlockAddress Afine) :=
  groupCompatibilityIsolatedSupport ambient group .Z
    (dwz63PlainUsefulCompatible group usefulFor)

omit [∀ c, Fintype (Afine c)] [∀ c, DecidableEq (Afine c)] in
/-- **Every hole-free fine address survives Step 2.**

This is `usefulFor_of_notMem_dwz63HoleSet` in tensor form: if `s`'s small `Z`-block is not a hole
for `s`'s own retained triple, then it is compatible with no other retained triple, so every
ambient address it is useful for carries the same group.  `hholes` is exactly the conjunction that
lemma produces, and `hrefines` is `def:useful_g` refining compatibility. -/
theorem dwz63_mem_plainGroupedZSupport_of_notMem_holes
    {ambient : Finset (BlockAddress Afine)}
    {group : BlockAddress Afine → retained}
    {compatibleWith usefulFor : Afine .Z → retained → Prop}
    (hrefines : ∀ (z : Afine .Z) (a : retained), usefulFor z a → compatibleWith z a)
    {holes : retained → Finset (Afine .Z)}
    (hholes : ∀ (a : retained) (z : Afine .Z), z ∉ holes a →
      usefulFor z a ∧ ∀ b : retained, b ≠ a → ¬ compatibleWith z b)
    {s : BlockAddress Afine} (hs : s ∈ ambient) (hhole : s .Z ∉ holes (group s)) :
    s ∈ dwz63PlainGroupedZSupport ambient group usefulFor := by
  classical
  rw [dwz63PlainGroupedZSupport, mem_groupCompatibilityIsolatedSupport]
  refine ⟨hs, ?_⟩
  intro other _hother huseful
  obtain ⟨_, hprivate⟩ := hholes (group s) (s .Z) hhole
  by_contra hne
  exact hprivate (group other) hne
    (hrefines (s .Z) (group other) huseful)

omit [∀ c, Fintype (Afine c)] [∀ c, DecidableEq (Afine c)] in
/-- **Step 2 is sound on the hole-free ambient.**  Soundness is `[DuanWuZhou2022]`'s "useful for
the triple it belongs to", which is the first half of `usefulFor_of_notMem_dwz63HoleSet`. -/
theorem dwz63_isCompatibilitySound_plainUseful
    {ambient : Finset (BlockAddress Afine)}
    {group : BlockAddress Afine → retained}
    {compatibleWith usefulFor : Afine .Z → retained → Prop}
    {holes : retained → Finset (Afine .Z)}
    (hholes : ∀ (a : retained) (z : Afine .Z), z ∉ holes a →
      usefulFor z a ∧ ∀ b : retained, b ≠ a → ¬ compatibleWith z b)
    (hambient : ∀ s ∈ ambient, s .Z ∉ holes (group s)) :
    IsCompatibilitySound ambient .Z (dwz63PlainUsefulCompatible group usefulFor) := by
  intro s hs
  exact (hholes (group s) (s .Z) (hambient s hs)).1

end Holes

/-! ## The grouped direct sum -/

section Stage

variable {K : Type u} [CommSemiring K]
variable {n : ℕ} {Afine : Leg → Type w}
variable [∀ c, Fintype (Afine c)] [∀ c, DecidableEq (Afine c)]
variable {Vfine : ∀ c, Afine c → Type x}
variable [∀ c a, AddCommMonoid (Vfine c a)] [∀ c a, Module K (Vfine c a)]
variable {retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)}

/-- **The broken copy of one retained triple**: the fine addresses of its coarse group that
survive Step 2.  This is `constituent a` with every hole `Z`-word zeroed. -/
noncomputable def dwz63PlainBrokenGroup
    (fine : PartitionedTensor (K := K) (A := Afine) Vfine)
    (group : BlockAddress Afine → retained)
    (usefulFor : Afine .Z → retained → Prop) (a : retained) :
    PartitionedTensor (K := K) (A := Afine) Vfine :=
  fine.withSupport
    ((dwz63PlainGroupedZSupport fine.support group usefulFor).filter fun s ↦ group s = a)

/-- **The grouped retained direct sum, with no `hlegwise`.**

The replacement for `dwz63_plainRetainedDirectSum`: the fine partition restricts onto the direct
sum of the broken copies, one per retained triple, and the three premises are the hash's `X` and
`Y` certificates and the hole rules --- never legwise injectivity of the coarse retained family. -/
theorem dwz63_plainGroupedBrokenDirectSum
    (fine : PartitionedTensor (K := K) (A := Afine) Vfine)
    (coarse : ∀ c, Afine c → PositiveWord (Fin 5) n) (a₀ : retained)
    (hX : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .X)
      (retained : Set _))
    (hY : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .Y)
      (retained : Set _))
    (hcover : ∀ s ∈ fine.support, ∃ a : retained,
      ∀ c, (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) c = coarse c (s c))
    {compatibleWith usefulFor : Afine .Z → retained → Prop}
    {holes : retained → Finset (Afine .Z)}
    (hholes : ∀ (a : retained) (z : Afine .Z), z ∉ holes a →
      usefulFor z a ∧ ∀ b : retained, b ≠ a → ¬ compatibleWith z b)
    (hambient : ∀ s ∈ fine.support,
      s .Z ∉ holes (dwz63PlainCoarseGroup retained coarse a₀ s)) :
    Restricts fine.realize
      (Tensor.indexedDirectSum
        (V := PartitionedTensor.LegGrouping.GroupAmbientFamily
          (K := K) (V := Vfine) (Γ := retained))
        fun a : retained ↦
          (dwz63PlainBrokenGroup fine (dwz63PlainCoarseGroup retained coarse a₀) usefulFor
            a).realize) := by
  classical
  set group := dwz63PlainCoarseGroup retained coarse a₀ with hgroup
  have hsound : IsCompatibilitySound fine.support .Z
      (dwz63PlainUsefulCompatible group usefulFor) :=
    dwz63_isCompatibilitySound_plainUseful (compatibleWith := compatibleWith) hholes hambient
  have hzSubset : dwz63PlainGroupedZSupport fine.support group usefulFor ⊆ fine.support :=
    groupCompatibilityIsolatedSupport_subset _ _ _ _
  have hxAmbient : HasGroupUniqueLegFibers fine.support fine.support group .X :=
    dwz63PlainCoarseGroup_hasGroupUniqueLegFibers_x retained coarse a₀ fine.support
  have hyAmbient : HasGroupUniqueLegFibers fine.support fine.support group .Y :=
    dwz63PlainCoarseGroup_hasGroupUniqueLegFibers_y hX hY hcover
  have hzAmbient : HasGroupUniqueLegFibers fine.support
      (dwz63PlainGroupedZSupport fine.support group usefulFor) group .Z :=
    groupCompatibilityIsolatedSupport_hasGroupUniqueLegFibers _ _ _ _ hsound
  have hfinal : ∀ pivot,
      HasGroupUniqueLegFibers (dwz63PlainGroupedZSupport fine.support group usefulFor)
        (dwz63PlainGroupedZSupport fine.support group usefulFor) group pivot := by
    intro pivot
    cases pivot with
    | X => exact (hxAmbient.restrictToSubset hzSubset).toSelf
    | Y => exact (hyAmbient.restrictToSubset hzSubset).toSelf
    | Z => exact hzAmbient.toSelf
  let PZ : PartitionedTensor (K := K) (A := Afine) Vfine :=
    fine.withSupport (dwz63PlainGroupedZSupport fine.support group usefulFor)
  let G : PZ.LegGrouping retained :=
    PartitionedTensor.LegGrouping.ofGroupUnique PZ group a₀ hfinal
  have hzRestrict : Restricts fine.realize PZ.realize :=
    Restricts.partitionedGroupCompatibilityIsolated fine group .Z
      (dwz63PlainUsefulCompatible group usefulFor) hsound
  exact hzRestrict.trans G.restricts_groupedIndexedDirectSum

/-- **The plug**: the plain power restricts onto the direct sum of the broken leaves.

`dwz63_plainGroupedBrokenDirectSum` composed with the descent to the fine partition and with the
per-group leaf step.  This is the drop-in replacement for `dwz63_plainRetainedDirectSum` followed
by `Restricts.indexedDirectSum hleaf`, with `hlegwise` deleted; `source` is left free so the plain
power's spelling is the client's. -/
theorem dwz63_plainGroupedStage_of_brokenLeaf
    {Wsource : Leg → Type x} [∀ c, AddCommMonoid (Wsource c)] [∀ c, Module K (Wsource c)]
    {source : Tensor3 K Wsource}
    (fine : PartitionedTensor (K := K) (A := Afine) Vfine)
    (hstage : Restricts source fine.realize)
    (coarse : ∀ c, Afine c → PositiveWord (Fin 5) n) (a₀ : retained)
    (hX : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .X)
      (retained : Set _))
    (hY : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .Y)
      (retained : Set _))
    (hcover : ∀ s ∈ fine.support, ∃ a : retained,
      ∀ c, (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) c = coarse c (s c))
    {compatibleWith usefulFor : Afine .Z → retained → Prop}
    {holes : retained → Finset (Afine .Z)}
    (hholes : ∀ (a : retained) (z : Afine .Z), z ∉ holes a →
      usefulFor z a ∧ ∀ b : retained, b ≠ a → ¬ compatibleWith z b)
    (hambient : ∀ s ∈ fine.support,
      s .Z ∉ holes (dwz63PlainCoarseGroup retained coarse a₀ s))
    (broken : retained → PartitionedTensor (K := K) (A := Afine) Vfine)
    (hleaf : ∀ a : retained,
      Restricts (dwz63PlainBrokenGroup fine (dwz63PlainCoarseGroup retained coarse a₀)
        usefulFor a).realize (broken a).realize) :
    Restricts source
      (Tensor.indexedDirectSum
        (V := PartitionedTensor.LegGrouping.GroupAmbientFamily
          (K := K) (V := Vfine) (Γ := retained))
        fun a : retained ↦ (broken a).realize) :=
  (hstage.trans (dwz63_plainGroupedBrokenDirectSum fine coarse a₀ hX hY hcover
    (compatibleWith := compatibleWith) hholes hambient)).trans
    (Tensor.Restricts.indexedDirectSum hleaf)

end Stage

end AlgebraicComplexity.Examples
