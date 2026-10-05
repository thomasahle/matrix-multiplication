/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutDominationInputs
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCompetitorCount
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSeedInputs
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSeedHoleMass
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainMarginalAmbient
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoEncodingComponent

set_option autoImplicit false

/-!
# `claim:hole_frac_low`'s necessary condition, as a domination on the Step-1 cut

Layer 4 (`AlgebraicComplexity/Examples/`).  This module proves the **domination** that the
level-two hole side has owed since the design gap was found: the reference-frame hole family of
`𝒯^{(1)}` is contained in rule (i)'s seed-shared hole family, so its cardinality is bounded by
the
count that `lemma:hash_independence` controls.

The paper step is `[duan2023faster]`, section 6.1 `sec:global-algo`, claim `claim:hole_frac_low`,
`papers/sources/2210.10173/global_value.tex:249-265` (note: **not** `hole_lemma.tex`).  Its proof
opens at `:255` with the necessary condition:

>  A necessary condition of `Z_K̂` being a hole is that there exists `I' ≠ I` matchable to `K`
> such
> that (1) `Z_K̂` is compatible with `X_{I'}`; and (2) `I'` is hashed to the same slot as `K`, i.e.
> `hashx(I') = hashz(K)`.

`dwz63SeedSharedHoles` (`Examples/DuanWuZhouLevelTwoSeedHoleMass.lean:116`) is the right-hand side
of that implication --- the words some *other* ambient triple, sitting in the copy's own bucket, is
compatible with --- and `dwz63CutReferenceHoles`
(`Examples/DuanWuZhouLevelTwoStepOneCutHoles.lean`) is its left-hand side.  So the subset below
**is** the sentence at `:255`, and it is exactly the `hdom` binder of
`dwz63_exists_seed_stage_marked` (`Examples/DuanWuZhouLevelTwoHoleIntegrationStage.lean:73`), which
in turn feeds the domination premise of image 129's
`dwz63_exists_seed_holeFraction_and_copyCount`.

## Why the Step-1 cut is what makes it true

Clause (1) is the one the uncut preimage ambient cannot supply: there, a hole's witness is only
required to *carry* the word, not to be compatible with it, which is why the uncut family was
degree-determined.  Over `dwz63FineStepOneCut` the witness survives Additional Zeroing-Out Step 1
(`:52-61`), so `lemma:triple_implies_compatible` (`:63-71`) applies to it --- that is image 143's
`dwz63_stepOneCut_isCompatible`, packaged for this use as `dwz63_cutReferenceHole_isCompatible`.

## The relation is the committed one

`compat` is instantiated at the committed `dwz63SplitCompatTyped`
(`Examples/DuanWuZhouLevelTwoCompetitorCount.lean:104`) over `dwz63SplitPair s`, so the very same
relation carries `hcompetitors` and `hzIndex` through `dwz63_hcompetitorsTyped` (`:134`) and
`dwz63_hzIndexTyped` (`:151`).  `component` and `read` stay parameters, exactly as in those two
committed theorems; `hcomponent` and `hread` pin them to the geometry, and every other input of the
relation is discharged here:

* its joint-type conjunct, from `dwz63_multiplicity_dwz63Seg_of_mem_markedWords` (the marked family
  is one joint type class, `:28`);
* its `zIndex` conjunct, from the competitor sharing the copy's coarse `Z`-word
  (`dwz63_coarseZ_of_cutReferenceHole`, the "matchable to `K`" clause) through
  `dwz63_zIndex_dwz63Seg`;
* its usefulness conjunct, from `isUseful_of_segmentedAvailableWord`
  (`Examples/DuanWuZhouLevelTwoSeedInputs.lean:235`) at the owner's own frame, whose availability
  is `dwz63_segmentedAvailable_frameTransport`;
* its compatibility conjunct, from the cut, as above.

Clause (2) is `dwz63_inCommonTriple_of_zIndex_eq`.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:28, 44-72, 249-265`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor ProgressionHash CompatibleSplit

universe u v

noncomputable section

section Domination

variable {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)]
variable {n t s : ℕ} {profile : Fin 15 → ℕ}
variable {alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ}

/-- **`claim:hole_frac_low`'s necessary condition (`global_value.tex:255`), as a subset.**

Every hole of the copy `a` in `𝒯^{(1)}` is a word that some *other* marked triple, sitting in
`a`'s
own hash bucket, is compatible with.  `hX` and `hY` are not binders here: they are the hash's own
certificates, derived inside from `hmarked` and `hB`.

Proof sketch, following `:255` clause by clause.  A hole supplies a witness `other` in the cut over
a competing group; that group is modeled by a marked-`XY`-isolated triple `c'`, which is the
paper's `X_{I'}`.  `c' ≠ c` because their modeled addresses differ.  "Matchable to `K`" is
`dwz63_coarseZ_of_cutReferenceHole`: the witness carries a frame-transported available word, whose
coarse `Z`-word is `a`'s; through `dwz63_zIndex_dwz63Seg` that is the relation's `zIndex` conjunct,
and through `dwz63_zIndex_eq_of_componentWord` it is also the equality of hash `Z`-words that
clause (2) needs.  Clause (1) is `dwz63_cutReferenceHole_isCompatible`.  The remaining two
conjuncts of `dwz63SplitCompatTyped` are the marked joint type and usefulness at the owner's
frame. -/
theorem dwz63_cutReferenceHoles_subset_seedSharedHoles
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R)))
    (hmarked : dwz63MarkedWords n profile ⊆ dwz63PlainMarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (a₀ : dwz63PlainJointRetainedSupport K hinj n t (dwz63MarkedWords n profile) B seed)
    (hS : (dwz63SplitPair s).splitCount = alphaTilde)
    (hα : ∀ u k, alphaTilde u k ≠ 0 → cwSquareDegreeMap Leg.Z k = dwz63ZIndex u)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (perm : dwz63PlainJointRetainedSupport K hinj n t (dwz63MarkedWords n profile) B seed →
      Equiv.Perm (Fin (n + 1)))
    (hperm : ∀ b, positiveSupportWordBlockAddress
        ((cwSquarePartitionedTensor K dwz63Q).support) n
        (positiveWordPositionEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n (perm b) wRef)
      = (b : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (component : LegalTriple R (Fin (n + 1)) (cwSquarePartitionHashEncoding hinj).target →
      Fin (n + 1) → Fin 15)
    (hcomponent : ∀ x, component x =
      dwz63Seg K n ((cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple n x))
    (read : LegalTriple R (Fin (n + 1)) (cwSquarePartitionHashEncoding hinj).target →
      SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde →
      Fin (n + 1) → PositiveWord CWBlock 1)
    (hread : ∀ (b : dwz63PlainJointRetainedSupport K hinj n t (dwz63MarkedWords n profile) B seed)
      (x : LegalTriple R (Fin (n + 1)) (cwSquarePartitionHashEncoding hinj).target),
      (cwSquarePartitionHashEncoding hinj).modeledAddress n x =
          (b : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) →
        ∀ z, read x z = positiveWordEquiv (PositiveWord CWBlock 1) n
          (positiveWordPositionEquiv (PositiveWord CWBlock 1) n (perm b) z.1))
    (a : dwz63PlainJointRetainedSupport K hinj n t (dwz63MarkedWords n profile) B seed)
    (c : LegalTriple R (Fin (n + 1)) (cwSquarePartitionHashEncoding hinj).target)
    (hc : c ∈ LegalTriple.markedXYIsolatedTargets
      ((cwSquarePartitionHashEncoding hinj).legalTargets n (dwz63PlainMarginalWords K n t))
      ((cwSquarePartitionHashEncoding hinj).legalTargets n (dwz63MarkedWords n profile)) B seed)
    (hca : (cwSquarePartitionHashEncoding hinj).modeledAddress n c =
      (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)) :
    dwz63CutReferenceHoles K
        (dwz63PlainJointRetainedSupport K hinj n t (dwz63MarkedWords n profile) B seed)
        a₀ s alphaTilde wRef perm a ⊆
      dwz63SeedSharedHoles
        ((cwSquarePartitionHashEncoding hinj).legalTargets n (dwz63PlainMarginalWords K n t))
        (dwz63SplitCompatTyped (dwz63SplitPair s) component read profile) seed c
        (dwz63IsolatedBucket
          ((cwSquarePartitionHashEncoding hinj).legalTargets n (dwz63PlainMarginalWords K n t))
          ((cwSquarePartitionHashEncoding hinj).legalTargets n (dwz63MarkedWords n profile))
          B seed c) := by
  classical
  have hX := dwz63_x_injOn_plainJointRetained K hinj n t (dwz63MarkedWords n profile) hmarked B hB
    seed
  have hY : Set.InjOn
      (fun g : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ g Leg.Y)
      (dwz63PlainJointRetainedSupport K hinj n t (dwz63MarkedWords n profile) B seed : Set _) :=
    (cwSquarePartitionHashEncoding hinj).y_injectiveOn_markedXYIsolatedPowerAddresses n
      (dwz63PlainMarginalWords K n t) (dwz63MarkedWords n profile) hmarked B hB seed
  have hcmem : c ∈ (cwSquarePartitionHashEncoding hinj).legalTargets n
      (dwz63MarkedWords n profile) :=
    LegalTriple.markedXYIsolatedTargets_subset_marked _ _ B seed hc
  intro z hz
  obtain ⟨other, hother, hoZ, hne⟩ := (mem_dwz63CutReferenceHoles K _ a₀ s alphaTilde wRef
    perm a z).mp hz
  -- the competing group, and the marked triple modelling it: the paper's `X_{I'}` (`:255`)
  have hgmem : ((dwz63PlainCoarseGroup
      (dwz63PlainJointRetainedSupport K hinj n t (dwz63MarkedWords n profile) B seed)
      (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ other :
        BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)) ∈
      (LegalTriple.markedXYIsolatedTargets
        ((cwSquarePartitionHashEncoding hinj).legalTargets n (dwz63PlainMarginalWords K n t))
        ((cwSquarePartitionHashEncoding hinj).legalTargets n (dwz63MarkedWords n profile))
        B seed).image ((cwSquarePartitionHashEncoding hinj).modeledAddress n) :=
    (dwz63PlainCoarseGroup
      (dwz63PlainJointRetainedSupport K hinj n t (dwz63MarkedWords n profile) B seed)
      (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ other).2
  obtain ⟨c', hc', hmod'⟩ := Finset.mem_image.mp hgmem
  have hc'mem : c' ∈ (cwSquarePartitionHashEncoding hinj).legalTargets n
      (dwz63MarkedWords n profile) :=
    LegalTriple.markedXYIsolatedTargets_subset_marked _ _ B seed hc'
  -- "matchable to `K`" (`:255`): the competitor carries `a`'s coarse `Z`-word
  have hpre := ((PartitionedTensor.mem_select_support (dwz63PreimageFine K n _)
    (dwz63FineStepOneKeep _ a₀ s) other).mp hother).1
  have hret := ((mem_dwz63PreimageFine_support K n _ other).mp hpre).2
  have hgroup : (dwz63PlainCoarseGroup
      (dwz63PlainJointRetainedSupport K hinj n t (dwz63MarkedWords n profile) B seed)
      (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ other :
        BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) =
      coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) other :=
    congrArg Subtype.val (dwz63PlainCoarseGroup_eq_of_x (a₀ := a₀)
      (coarse := fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) (s := other) hX
      (a := (⟨_, hret⟩ : dwz63PlainJointRetainedSupport K hinj n t
        (dwz63MarkedWords n profile) B seed)) rfl)
  have hzword : (dwz63PlainCoarseGroup
      (dwz63PlainJointRetainedSupport K hinj n t (dwz63MarkedWords n profile) B seed)
      (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ other :
        BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) Leg.Z =
      (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) Leg.Z := by
    rw [hgroup]
    show positiveWordMap (cwSquareDegreeMap Leg.Z) n (other Leg.Z) = _
    rw [hoZ]
    exact dwz63_coarseZ_of_cutReferenceHole K _ alphaTilde hα wRef perm hperm a z
  have haddrZ : ((cwSquarePartitionHashEncoding hinj).modeledAddress n c') Leg.Z =
      ((cwSquarePartitionHashEncoding hinj).modeledAddress n c) Leg.Z := by
    rw [hmod', hca, hzword]
  -- the relation's `zIndex` conjunct
  have hzcomp : (dwz63SplitPair s).zIndex ∘ component c' =
      (dwz63SplitPair s).zIndex ∘ component c := by
    funext i
    show dwz63ZIndex (component c' i) = dwz63ZIndex (component c i)
    have h1 : dwz63ZIndex (dwz63Seg K n
        ((cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple n c') i) =
        positiveWordEquiv (Fin 5) n
          (((cwSquarePartitionHashEncoding hinj).modeledAddress n c') Leg.Z) i :=
      dwz63_zIndex_dwz63Seg K _ i
    have h2 : dwz63ZIndex (dwz63Seg K n
        ((cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple n c) i) =
        positiveWordEquiv (Fin 5) n
          (((cwSquarePartitionHashEncoding hinj).modeledAddress n c) Leg.Z) i :=
      dwz63_zIndex_dwz63Seg K _ i
    rw [hcomponent c', hcomponent c, h1, h2, haddrZ]
  -- clause (1) (`:255`): compatibility, which only the Step-1 cut supplies
  have hcompat : (dwz63SplitPair s).IsCompatible (component c') (read c z) := by
    have e3 : dwz63Seg K n
        ((cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple n c') =
        dwz63CellWordOfAddress
          ((cwSquarePartitionHashEncoding hinj).modeledAddress n c') :=
      dwz63Seg_eq_cellWordOfAddress K _
    rw [hcomponent c', e3, hmod', hread a c hca z, ← hoZ]
    exact dwz63_cutReferenceHole_isCompatible K a₀ s hX hY other hother
  -- the relation's usefulness conjunct, at the owner's own frame
  have haddrc : positiveSupportWordBlockAddress
      ((cwSquarePartitionedTensor K dwz63Q).support) n
      ((cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple n c) =
      positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n
        (positiveWordPositionEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n
          (perm a) wRef) := by
    rw [hperm a]
    exact hca
  have hcompc : component c =
      dwz63Seg K n (positiveWordPositionEquiv
        ((cwSquarePartitionedTensor K dwz63Q).support) n (perm a) wRef) := by
    have e1 : dwz63Seg K n
        ((cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple n c) =
        dwz63CellWordOfAddress
          (positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n
            ((cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple n c)) :=
      dwz63Seg_eq_cellWordOfAddress K _
    have e2 : dwz63Seg K n (positiveWordPositionEquiv
        ((cwSquarePartitionedTensor K dwz63Q).support) n (perm a) wRef) =
        dwz63CellWordOfAddress
          (positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n
            (positiveWordPositionEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n
              (perm a) wRef)) :=
      dwz63Seg_eq_cellWordOfAddress K _
    rw [hcomponent c, e1, e2, haddrc]
  have huseful : (dwz63SplitPair s).IsUseful (component c) (read c z) := by
    rw [hcompc, hread a c hca z]
    exact isUseful_of_segmentedAvailableWord (dwz63SplitPair s)
      (dwz63Seg K n (positiveWordPositionEquiv
        ((cwSquarePartitionedTensor K dwz63Q).support) n (perm a) wRef)) alphaTilde hS
      ⟨positiveWordPositionEquiv (PositiveWord CWBlock 1) n (perm a) z.1,
        dwz63_segmentedAvailable_frameTransport K alphaTilde wRef (perm a) z⟩
  -- the relation's joint-type conjunct: the marked family is one type class (`:28`)
  have htype : WordType.multiplicity (component c') = profile := by
    rw [hcomponent c']
    exact dwz63_multiplicity_dwz63Seg_of_mem_markedWords K profile _
      ((cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple_mem_of_mem n
        (dwz63MarkedWords n profile) hc'mem)
  have hcc' : c' ≠ c := by
    intro hEq
    exact hne (Subtype.ext (by rw [← hmod', hEq, hca]))
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, c', ?_, ?_⟩
  · refine mem_dwz63FineCompetitors.mpr ⟨⟨hcc', ?_⟩, htype, hzcomp, huseful, hcompat⟩
    exact (cwSquarePartitionHashEncoding hinj).legalTargets_mono n hmarked hc'mem
  · -- clause (2) (`:255`): the competitor lands in the copy's own bucket
    refine dwz63_inCommonTriple_of_zIndex_eq _ _ B seed hc hc' ?_
    refine dwz63_zIndex_eq_of_componentWord (cwSquarePartitionHashEncoding hinj) n
      (dwz63MarkedWords n profile) hc'mem hcmem ?_
    funext i
    have e1 := congrFun (PartitionHashEncoding.positiveWordEquiv_supportWordAddress n
      ((cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple n c') Leg.Z) i
    have e2 := congrFun (PartitionHashEncoding.positiveWordEquiv_supportWordAddress n
      ((cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple n c) Leg.Z) i
    exact (e1.symm.trans
      (congrFun (congrArg (positiveWordEquiv (Fin 5) n) haddrZ) i)).trans e2


/-- **The domination, in the shape the stage's `hdom` binder consumes.**

`dwz63_exists_seed_stage_marked` (`Examples/DuanWuZhouLevelTwoHoleIntegrationStage.lean:73`) binds
the hole family's cardinality against rule (i)'s shared-hole count plus the rule-(ii) allowance
`useless`; this is that inequality for the hole family of `𝒯^{(1)}`, and it is
`[duan2023faster]`'s `claim:hole_frac_low` (`global_value.tex:249-265`) reduced to the counting
statement `lemma:hash_independence` controls.  The allowance is not used: the localized rule (ii)
removes nothing (`card_dwz63UselessZWords_eq_zero`,
`Examples/DuanWuZhouLevelTwoSeedInputs.lean:265`), so the bound holds already at `useless = 0`.

Proof sketch: `Finset.card_le_card` on the subset above, then `Nat.le_add_right`. -/
theorem dwz63_card_cutReferenceHoles_le_seedSharedHoles
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R)))
    (hmarked : dwz63MarkedWords n profile ⊆ dwz63PlainMarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (a₀ : dwz63PlainJointRetainedSupport K hinj n t (dwz63MarkedWords n profile) B seed)
    (hS : (dwz63SplitPair s).splitCount = alphaTilde)
    (hα : ∀ u k, alphaTilde u k ≠ 0 → cwSquareDegreeMap Leg.Z k = dwz63ZIndex u)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (perm : dwz63PlainJointRetainedSupport K hinj n t (dwz63MarkedWords n profile) B seed →
      Equiv.Perm (Fin (n + 1)))
    (hperm : ∀ b, positiveSupportWordBlockAddress
        ((cwSquarePartitionedTensor K dwz63Q).support) n
        (positiveWordPositionEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n (perm b) wRef)
      = (b : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (component : LegalTriple R (Fin (n + 1)) (cwSquarePartitionHashEncoding hinj).target →
      Fin (n + 1) → Fin 15)
    (hcomponent : ∀ x, component x =
      dwz63Seg K n ((cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple n x))
    (read : LegalTriple R (Fin (n + 1)) (cwSquarePartitionHashEncoding hinj).target →
      SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde →
      Fin (n + 1) → PositiveWord CWBlock 1)
    (hread : ∀ (b : dwz63PlainJointRetainedSupport K hinj n t (dwz63MarkedWords n profile) B seed)
      (x : LegalTriple R (Fin (n + 1)) (cwSquarePartitionHashEncoding hinj).target),
      (cwSquarePartitionHashEncoding hinj).modeledAddress n x =
          (b : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) →
        ∀ z, read x z = positiveWordEquiv (PositiveWord CWBlock 1) n
          (positiveWordPositionEquiv (PositiveWord CWBlock 1) n (perm b) z.1))
    (a : dwz63PlainJointRetainedSupport K hinj n t (dwz63MarkedWords n profile) B seed)
    (c : LegalTriple R (Fin (n + 1)) (cwSquarePartitionHashEncoding hinj).target)
    (hc : c ∈ LegalTriple.markedXYIsolatedTargets
      ((cwSquarePartitionHashEncoding hinj).legalTargets n (dwz63PlainMarginalWords K n t))
      ((cwSquarePartitionHashEncoding hinj).legalTargets n (dwz63MarkedWords n profile)) B seed)
    (hca : (cwSquarePartitionHashEncoding hinj).modeledAddress n c =
      (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (useless : LegalTriple R (Fin (n + 1)) (cwSquarePartitionHashEncoding hinj).target → ℕ) :
    (dwz63CutReferenceHoles K
        (dwz63PlainJointRetainedSupport K hinj n t (dwz63MarkedWords n profile) B seed)
        a₀ s alphaTilde wRef perm a).card ≤
      (dwz63SeedSharedHoles
        ((cwSquarePartitionHashEncoding hinj).legalTargets n (dwz63PlainMarginalWords K n t))
        (dwz63SplitCompatTyped (dwz63SplitPair s) component read profile) seed c
        (dwz63IsolatedBucket
          ((cwSquarePartitionHashEncoding hinj).legalTargets n (dwz63PlainMarginalWords K n t))
          ((cwSquarePartitionHashEncoding hinj).legalTargets n (dwz63MarkedWords n profile))
          B seed c)).card + useless c :=
  le_trans
    (Finset.card_le_card
      (dwz63_cutReferenceHoles_subset_seedSharedHoles K hinj hmarked B hB seed a₀ hS hα wRef
        perm hperm component hcomponent read hread a c hc hca))
    (Nat.le_add_right _ _)

end Domination

end

end AlgebraicComplexity.Examples
