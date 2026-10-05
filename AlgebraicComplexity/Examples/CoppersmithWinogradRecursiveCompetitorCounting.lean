/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveHashing
import AlgebraicComplexity.Combinatorics.RecursiveSplitMarginalCounting

/-!
# Ambient X-competitor counts for recursive CW hashing

The affine hashing theorem for a recursive constituent needs an upper bound on the number of
ambient marginal-type triples sharing one marked `X` word.  This file connects that concrete
family to the exact combinatorial count in `RecursiveSplitMarginalCounting`.

The bridge is intentionally one-sided.  Every *actual* recursive quotient address determines a
canonical ordered left-child shape word, and this map is injective.  Hence an actual `X`-fiber
injects into the abstract marginal-word `X`-fiber.  Surjectivity is neither assumed nor needed;
in particular this theorem does not smuggle in the later obligation that every prescribed fine
recursive box be nonempty and intact.

Combining the injection with

`N_X * #(abstract X-fiber) = N_triple`

gives the exact finite degree estimate used to choose the hashing modulus.  Entropy estimates for
`N_X` and `N_triple` are downstream asymptotic bookkeeping.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-! ## A canonical child-shape word on the coarse quotient -/

/-- On every supported recursive quotient address, the two labelled child coordinates add to
the fixed parent coordinate. -/
theorem cwRecursiveCoarsenedAlphaMarginalTerm_left_add_right
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (address : CWRecursiveCoarseAddress depth n)
    (haddress : address ∈
      (cwRecursiveCoarsenedAlphaMarginalTerm
        K q term hmultiplicity sigma alpha).support)
    (physicalLeg : Leg) (sample : Fin (n + 1)) :
    (address physicalLeg (Fin.castAdd (n + 1) sample) : ℕ) +
        (address physicalLeg (Fin.natAdd (n + 1) sample) : ℕ) =
      term.index.count physicalLeg := by
  classical
  change address ∈
    ((cwRecursiveAlphaMarginalSelectedTerm
      K q term hmultiplicity sigma alpha).coarsen
        (cwRecursiveChildCoarsening depth n)).support at haddress
  rw [PartitionedTensor.coarsen_support, Finset.mem_image] at haddress
  obtain ⟨fine, hfine, hcoarse⟩ := haddress
  have hparent : fine ∈
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support :=
    (mem_cwRecursiveAlphaMarginalSelectedTerm_support
      K q term hmultiplicity sigma alpha fine).mp hfine |>.1
  let partAt : Fin (n + 1) → (PUnit : Type) := fun _ ↦ PUnit.unit
  let model := cwRecursiveChildCompatibilityModel depth n partAt
  have hadd := recursiveChildCompatibilityModel_coarse_add_eq_parent
    (fun _c ↦ cwChunkSplitWord (depth + 1)) partAt fine term.index.count
    (cwRecursive_parentWeight_of_mem_selected_support
      K q term hmultiplicity fine hparent) physicalLeg sample
  have hleft :
      (address physicalLeg (Fin.castAdd (n + 1) sample) : ℕ) =
        (model.coarse fine (Fin.castAdd (n + 1) sample)).get physicalLeg := by
    rw [← hcoarse]
    exact congrArg Fin.val <| congrFun
      (cwRecursiveLabelledChildWord_eq_model_get depth n partAt fine physicalLeg)
      (Fin.castAdd (n + 1) sample)
  have hright :
      (address physicalLeg (Fin.natAdd (n + 1) sample) : ℕ) =
        (model.coarse fine (Fin.natAdd (n + 1) sample)).get physicalLeg := by
    rw [← hcoarse]
    exact congrArg Fin.val <| congrFun
      (cwRecursiveLabelledChildWord_eq_model_get depth n partAt fine physicalLeg)
      (Fin.natAdd (n + 1) sample)
  rw [hleft, hright]
  simpa only [model, cwRecursiveChildCompatibilityModel] using hadd

/-- The ordered logical left child attached directly to a supported coarse quotient address.

The bounds use the retained right occurrence, while the fixed total follows from the tight CW
support equation.  Thus the definition does not choose a fine representative. -/
def cwRecursiveLogicalLeftShapeWordOfCoarse
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (address : CWRecursiveCoarseAddress depth n)
    (haddress : address ∈
      (cwRecursiveCoarsenedAlphaMarginalTerm
        K q term hmultiplicity sigma alpha).support) :
    Fin (n + 1) → RecursiveChildShape
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) :=
  fun sample ↦ RecursiveChildShape.ofCoordinates
    (fun logicalLeg ↦
      (address (sigma logicalLeg) (Fin.castAdd (n + 1) sample) : ℕ))
    (fun logicalLeg ↦ by
      have hadd := cwRecursiveCoarsenedAlphaMarginalTerm_left_add_right
        K q term hmultiplicity sigma alpha address haddress (sigma logicalLeg) sample
      change (address (sigma logicalLeg)
          (Fin.castAdd (n + 1) sample) : ℕ) ≤
        cwRecursiveLogicalParent term sigma logicalLeg
      simpa [cwRecursiveLogicalParent] using Nat.le.intro hadd)
    (by
      have hsum := cwRecursiveCoarsenedAlphaMarginalTerm_coarse_sum
        K q term hmultiplicity sigma alpha address haddress
          (Fin.castAdd (n + 1) sample)
      have hperm :
          (∑ c : Leg,
            (address (sigma c) (Fin.castAdd (n + 1) sample) : ℕ)) =
          ∑ c : Leg,
            (address c (Fin.castAdd (n + 1) sample) : ℕ) :=
        Equiv.sum_comp sigma fun c : Leg ↦
          (address c (Fin.castAdd (n + 1) sample) : ℕ)
      calc
        (address (sigma .X) (Fin.castAdd (n + 1) sample) : ℕ) +
            (address (sigma .Y) (Fin.castAdd (n + 1) sample) : ℕ) +
            (address (sigma .Z) (Fin.castAdd (n + 1) sample) : ℕ) =
          ∑ c : Leg,
            (address (sigma c) (Fin.castAdd (n + 1) sample) : ℕ) := by
              simp [Tensor.sum_leg]
        _ = ∑ c : Leg,
            (address c (Fin.castAdd (n + 1) sample) : ℕ) := hperm
        _ = coarseTotal depth := by
          simpa [Tensor.sum_leg] using hsum)

@[simp] theorem coordinate_cwRecursiveLogicalLeftShapeWordOfCoarse
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (address : CWRecursiveCoarseAddress depth n)
    (haddress : address ∈
      (cwRecursiveCoarsenedAlphaMarginalTerm
        K q term hmultiplicity sigma alpha).support)
    (logicalLeg : Leg) (sample : Fin (n + 1)) :
    ExactRecursiveSplitType.coordinate logicalLeg
        (cwRecursiveLogicalLeftShapeWordOfCoarse
          K q term hmultiplicity sigma alpha address haddress sample) =
      address (sigma logicalLeg) (Fin.castAdd (n + 1) sample) := by
  apply Fin.ext
  simp [cwRecursiveLogicalLeftShapeWordOfCoarse,
    ExactRecursiveSplitType.coordinate]

/-- The retained right occurrence is exactly the coordinatewise complement of the canonical
left child shape. -/
theorem coordinate_complement_cwRecursiveLogicalLeftShapeWordOfCoarse
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (address : CWRecursiveCoarseAddress depth n)
    (haddress : address ∈
      (cwRecursiveCoarsenedAlphaMarginalTerm
        K q term hmultiplicity sigma alpha).support)
    (logicalLeg : Leg) (sample : Fin (n + 1)) :
    ExactRecursiveSplitType.coordinate logicalLeg
        ((RecursiveChildShape.complementPerm
          (cwRecursiveLogicalParent_total term sigma))
          (cwRecursiveLogicalLeftShapeWordOfCoarse
            K q term hmultiplicity sigma alpha address haddress sample)) =
      address (sigma logicalLeg) (Fin.natAdd (n + 1) sample) := by
  apply Fin.ext
  have hadd := cwRecursiveCoarsenedAlphaMarginalTerm_left_add_right
    K q term hmultiplicity sigma alpha address haddress (sigma logicalLeg) sample
  have hleft :
      (cwRecursiveLogicalLeftShapeWordOfCoarse
        K q term hmultiplicity sigma alpha address haddress sample).get logicalLeg =
        (address (sigma logicalLeg) (Fin.castAdd (n + 1) sample) : ℕ) :=
    congrArg Fin.val
    (coordinate_cwRecursiveLogicalLeftShapeWordOfCoarse
      K q term hmultiplicity sigma alpha address haddress logicalLeg sample)
  simp only [ExactRecursiveSplitType.coordinate_val,
    RecursiveChildShape.complementPerm_apply,
    RecursiveChildShape.complement_get]
  change cwRecursiveLogicalParent term sigma logicalLeg -
      (cwRecursiveLogicalLeftShapeWordOfCoarse
        K q term hmultiplicity sigma alpha address haddress sample).get logicalLeg = _
  rw [hleft]
  change term.index.count (sigma logicalLeg) -
      (address (sigma logicalLeg) (Fin.castAdd (n + 1) sample) : ℕ) = _
  omega

/-- A supported coarse quotient address is completely determined by its ordered left shape
word.  The right half is recovered by complementation, including self-complementary shapes. -/
theorem cwRecursiveLogicalLeftShapeWordOfCoarse_injectiveOn
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    Set.InjOn
      (fun source : {address : CWRecursiveCoarseAddress depth n //
          address ∈ (cwRecursiveCoarsenedAlphaMarginalTerm
            K q term hmultiplicity sigma alpha).support} ↦
        cwRecursiveLogicalLeftShapeWordOfCoarse
          K q term hmultiplicity sigma alpha source.1 source.2)
      Set.univ := by
  intro left _ right _ heq
  apply Subtype.ext
  funext physicalLeg occurrence
  let logicalLeg := sigma.symm physicalLeg
  have hphysical : sigma logicalLeg = physicalLeg := sigma.apply_symm_apply physicalLeg
  refine Fin.addCases ?_ ?_ occurrence <;> intro sample
  · have hcoordinate := congrArg
      (fun word ↦ ExactRecursiveSplitType.coordinate logicalLeg (word sample)) heq
    rw [← hphysical]
    simpa only [coordinate_cwRecursiveLogicalLeftShapeWordOfCoarse] using hcoordinate
  · have hcomplement := congrArg
      (fun word ↦ ExactRecursiveSplitType.coordinate logicalLeg
        ((RecursiveChildShape.complementPerm
          (cwRecursiveLogicalParent_total term sigma)) (word sample))) heq
    rw [← hphysical]
    simpa only [coordinate_complement_cwRecursiveLogicalLeftShapeWordOfCoarse] using hcomplement

/-- The canonical coarse left-shape word has the three prescribed ambient marginals. -/
theorem cwRecursiveLogicalLeftShapeWordOfCoarse_mem_marginalWords
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (source : {address : CWRecursiveCoarseAddress depth n //
      address ∈ (cwRecursiveCoarsenedAlphaMarginalTerm
        K q term hmultiplicity sigma alpha).support}) :
    cwRecursiveLogicalLeftShapeWordOfCoarse
        K q term hmultiplicity sigma alpha source.1 source.2 ∈
      alpha.marginalWords := by
  classical
  rw [ExactRecursiveSplitType.mem_marginalWords]
  intro logicalLeg
  have hsource : source.1 ∈
      ((cwRecursiveAlphaMarginalSelectedTerm
        K q term hmultiplicity sigma alpha).coarsen
          (cwRecursiveChildCoarsening depth n)).support := source.2
  rw [PartitionedTensor.coarsen_support, Finset.mem_image] at hsource
  obtain ⟨fine, hfine, hcoarse⟩ := hsource
  have hmarginal :=
    (mem_cwRecursiveAlphaMarginalSelectedTerm_support
      K q term hmultiplicity sigma alpha fine).mp hfine |>.2 (sigma logicalLeg)
  calc
    WordType.multiplicity
        (ExactRecursiveSplitType.coordinateWord logicalLeg
          (cwRecursiveLogicalLeftShapeWordOfCoarse
            K q term hmultiplicity sigma alpha source.1 source.2)) =
      WordType.multiplicity
        (cwRecursiveLogicalLeftCoordinateWord sigma source.1 logicalLeg) := by
          congr 1
          funext sample
          exact coordinate_cwRecursiveLogicalLeftShapeWordOfCoarse
            K q term hmultiplicity sigma alpha source.1 source.2 logicalLeg sample
    _ = WordType.multiplicity
        (cwRecursiveLeftChildWord depth n (fine (sigma logicalLeg))) := by
      congr 1
      funext sample
      rw [← hcoarse]
      simp only [cwRecursiveLogicalLeftCoordinateWord, coarsenBlockAddress_apply,
        cwRecursiveChildCoarsening, cwRecursiveLabelledChildWord_left]
    _ = alpha.marginalCount logicalLeg := by
      simpa [sigma.symm_apply_apply] using hmarginal

/-! ## Legal targets and the abstract marginal fiber -/

namespace CWCoarseFieldEncoding

variable {R : Type v} [Field R]

/-- The injective legal-triple representation is an equivalence onto the finite ambient target
family. -/
noncomputable def recursiveAmbientTargetEquiv
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    {address : CWRecursiveCoarseAddress depth n //
        address ∈ (cwRecursiveCoarsenedAlphaMarginalTerm
          K q term hmultiplicity sigma alpha).support} ≃
      {triple : ProgressionHash.LegalTriple R (Fin ((n + 1) + (n + 1))) encoding.target //
        triple ∈ encoding.recursiveAmbientTargets
          K q term hmultiplicity sigma alpha} := by
  classical
  let f := fun source : {address : CWRecursiveCoarseAddress depth n //
      address ∈ (cwRecursiveCoarsenedAlphaMarginalTerm
        K q term hmultiplicity sigma alpha).support} ↦
    (⟨encoding.recursiveOrientedLegalTriple
        K q term hmultiplicity sigma alpha source,
      Finset.mem_image.mpr ⟨source, Finset.mem_univ _, rfl⟩⟩ :
      {triple : ProgressionHash.LegalTriple R (Fin ((n + 1) + (n + 1))) encoding.target //
        triple ∈ encoding.recursiveAmbientTargets
          K q term hmultiplicity sigma alpha})
  apply Equiv.ofBijective f
  constructor
  · intro left right heq
    exact encoding.recursiveOrientedLegalTriple_injective
      K q term hmultiplicity sigma alpha (congrArg Subtype.val heq)
  · intro target
    have htarget := target.2
    unfold recursiveAmbientTargets at htarget
    rw [Finset.mem_image] at htarget
    obtain ⟨source, _hsource, hsource⟩ := htarget
    refine ⟨source, ?_⟩
    apply Subtype.ext
    exact hsource

/-- Source address underlying an ambient legal target. -/
noncomputable def recursiveAmbientSourceOfTarget
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (target : {triple : ProgressionHash.LegalTriple R
      (Fin ((n + 1) + (n + 1))) encoding.target //
        triple ∈ encoding.recursiveAmbientTargets
          K q term hmultiplicity sigma alpha}) :=
  (encoding.recursiveAmbientTargetEquiv
    K q term hmultiplicity sigma alpha).symm target

@[simp] theorem recursiveOrientedLegalTriple_recursiveAmbientSourceOfTarget
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (target : {triple : ProgressionHash.LegalTriple R
      (Fin ((n + 1) + (n + 1))) encoding.target //
        triple ∈ encoding.recursiveAmbientTargets
          K q term hmultiplicity sigma alpha}) :
    encoding.recursiveOrientedLegalTriple K q term hmultiplicity sigma alpha
        (encoding.recursiveAmbientSourceOfTarget
          K q term hmultiplicity sigma alpha target) = target.1 := by
  exact congrArg Subtype.val
    ((encoding.recursiveAmbientTargetEquiv
      K q term hmultiplicity sigma alpha).apply_symm_apply target)

/-- Every concrete ambient `X`-fiber injects into the abstract recursive marginal-word fiber.

The target of the injection uses the ordered-left `X` coordinate word of the chosen source.
The concrete hash index contains both labelled children; equality of those indices in particular
gives equality on the left half. -/
theorem card_recursiveAmbient_xFiber_le_marginalWordFiber
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (source : {address : CWRecursiveCoarseAddress depth n //
      address ∈ (cwRecursiveCoarsenedAlphaMarginalTerm
        K q term hmultiplicity sigma alpha).support}) :
    (ProgressionHash.LegalTriple.xFiber
      (encoding.recursiveAmbientTargets K q term hmultiplicity sigma alpha)
      (encoding.recursiveOrientedLegalTriple
        K q term hmultiplicity sigma alpha source)).card ≤
      (alpha.marginalWordFiber .X
        (ExactRecursiveSplitType.coordinateWord .X
          (cwRecursiveLogicalLeftShapeWordOfCoarse
            K q term hmultiplicity sigma alpha source.1 source.2))).card := by
  classical
  let ambient := encoding.recursiveAmbientTargets
    K q term hmultiplicity sigma alpha
  let chosen := encoding.recursiveOrientedLegalTriple
    K q term hmultiplicity sigma alpha source
  let fiber := ProgressionHash.LegalTriple.xFiber ambient chosen
  let sourceOf := fun other : {triple : ProgressionHash.LegalTriple R
      (Fin ((n + 1) + (n + 1))) encoding.target // triple ∈ ambient} ↦
    encoding.recursiveAmbientSourceOfTarget
      K q term hmultiplicity sigma alpha other
  let shapeOf := fun other : {triple : ProgressionHash.LegalTriple R
      (Fin ((n + 1) + (n + 1))) encoding.target // triple ∈ fiber} ↦
    let hambient : other.1 ∈ ambient :=
      (Finset.mem_filter.mp other.2).1
    let coarse := sourceOf ⟨other.1, hambient⟩
    cwRecursiveLogicalLeftShapeWordOfCoarse
      K q term hmultiplicity sigma alpha coarse.1 coarse.2
  have hbound : fiber.attach.card ≤
      (alpha.marginalWordFiber .X
        (ExactRecursiveSplitType.coordinateWord .X
          (cwRecursiveLogicalLeftShapeWordOfCoarse
            K q term hmultiplicity sigma alpha source.1 source.2))).card := by
    apply Finset.card_le_card_of_injOn shapeOf
    · intro other _hother
      have hother : other.1 ∈ ambient ∧ other.1.xIndex = chosen.xIndex :=
        Finset.mem_filter.mp other.2
      let coarse := sourceOf ⟨other.1, hother.1⟩
      have hfin : shapeOf other ∈
          alpha.marginalWordFiber .X
            (ExactRecursiveSplitType.coordinateWord .X
              (cwRecursiveLogicalLeftShapeWordOfCoarse
                K q term hmultiplicity sigma alpha source.1 source.2)) := by
        rw [ExactRecursiveSplitType.mem_marginalWordFiber]
        refine ⟨cwRecursiveLogicalLeftShapeWordOfCoarse_mem_marginalWords
          K q term hmultiplicity sigma alpha coarse, ?_⟩
        funext sample
        apply encoding.encode_injective
        change encoding.encode
            (coarse.1 (sigma .X) (Fin.castAdd (n + 1) sample)) =
          encoding.encode
            (source.1 (sigma .X) (Fin.castAdd (n + 1) sample))
        have hrecover :=
          encoding.recursiveOrientedLegalTriple_recursiveAmbientSourceOfTarget
            K q term hmultiplicity sigma alpha ⟨other.1, hother.1⟩
        have hxRecover := congrFun
          (congrArg ProgressionHash.LegalTriple.xIndex hrecover)
          (Fin.castAdd (n + 1) sample)
        have hx := congrFun hother.2 (Fin.castAdd (n + 1) sample)
        calc
          encoding.encode
              (coarse.1 (sigma .X) (Fin.castAdd (n + 1) sample)) =
            other.1.xIndex (Fin.castAdd (n + 1) sample) := by
              simpa [coarse, sourceOf, recursiveOrientedLegalTriple] using hxRecover
          _ = chosen.xIndex (Fin.castAdd (n + 1) sample) := hx
          _ = encoding.encode
              (source.1 (sigma .X) (Fin.castAdd (n + 1) sample)) := by
                rfl
      exact hfin
    · intro left _hleft right _hright heq
      have hleft : left.1 ∈ ambient := (Finset.mem_filter.mp left.2).1
      have hright : right.1 ∈ ambient := (Finset.mem_filter.mp right.2).1
      let leftSource := sourceOf ⟨left.1, hleft⟩
      let rightSource := sourceOf ⟨right.1, hright⟩
      have hshape :
          cwRecursiveLogicalLeftShapeWordOfCoarse
              K q term hmultiplicity sigma alpha leftSource.1 leftSource.2 =
            cwRecursiveLogicalLeftShapeWordOfCoarse
              K q term hmultiplicity sigma alpha rightSource.1 rightSource.2 := by
        simpa [shapeOf, sourceOf, leftSource, rightSource] using heq
      have hsource := cwRecursiveLogicalLeftShapeWordOfCoarse_injectiveOn
        K q term hmultiplicity sigma alpha (Set.mem_univ leftSource)
          (Set.mem_univ rightSource) hshape
      apply Subtype.ext
      calc
        left.1 = encoding.recursiveOrientedLegalTriple
            K q term hmultiplicity sigma alpha leftSource := by
          simpa [leftSource, sourceOf] using
            (encoding.recursiveOrientedLegalTriple_recursiveAmbientSourceOfTarget
              K q term hmultiplicity sigma alpha ⟨left.1, hleft⟩).symm
        _ = encoding.recursiveOrientedLegalTriple
            K q term hmultiplicity sigma alpha rightSource := congrArg _ hsource
        _ = right.1 := by
          simpa [rightSource, sourceOf] using
            encoding.recursiveOrientedLegalTriple_recursiveAmbientSourceOfTarget
              K q term hmultiplicity sigma alpha ⟨right.1, hright⟩
  simpa [fiber] using hbound

/-- Division-free paper form of the ambient degree bound.

Multiplying the actual competitor fiber by `N_X` is at most the abstract `N_triple` count. -/
theorem card_coordinateType_mul_card_recursiveAmbient_xFiber_le
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (source : {address : CWRecursiveCoarseAddress depth n //
      address ∈ (cwRecursiveCoarsenedAlphaMarginalTerm
        K q term hmultiplicity sigma alpha).support}) :
    (WordType.typeClass (n + 1) (alpha.marginalCount .X)).card *
        (ProgressionHash.LegalTriple.xFiber
          (encoding.recursiveAmbientTargets K q term hmultiplicity sigma alpha)
          (encoding.recursiveOrientedLegalTriple
            K q term hmultiplicity sigma alpha source)).card ≤
      alpha.marginalWords.card := by
  have htarget : ExactRecursiveSplitType.coordinateWord .X
      (cwRecursiveLogicalLeftShapeWordOfCoarse
        K q term hmultiplicity sigma alpha source.1 source.2) ∈
      WordType.typeClass (n + 1) (alpha.marginalCount .X) := by
    rw [WordType.mem_typeClass]
    exact (ExactRecursiveSplitType.mem_marginalWords alpha _).mp
      (cwRecursiveLogicalLeftShapeWordOfCoarse_mem_marginalWords
        K q term hmultiplicity sigma alpha source) .X
  calc
    (WordType.typeClass (n + 1) (alpha.marginalCount .X)).card *
        (ProgressionHash.LegalTriple.xFiber
          (encoding.recursiveAmbientTargets K q term hmultiplicity sigma alpha)
          (encoding.recursiveOrientedLegalTriple
            K q term hmultiplicity sigma alpha source)).card ≤
      (WordType.typeClass (n + 1) (alpha.marginalCount .X)).card *
        (alpha.marginalWordFiber .X
          (ExactRecursiveSplitType.coordinateWord .X
            (cwRecursiveLogicalLeftShapeWordOfCoarse
              K q term hmultiplicity sigma alpha source.1 source.2))).card :=
        Nat.mul_le_mul_left _
          (encoding.card_recursiveAmbient_xFiber_le_marginalWordFiber
            K q term hmultiplicity sigma alpha source)
    _ = alpha.marginalWords.card :=
      alpha.card_coordinateType_mul_card_marginalWordFiber .X _ htarget

end CWCoarseFieldEncoding

end AlgebraicComplexity.Examples
