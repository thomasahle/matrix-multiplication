/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.IndexedDirectSum

/-!
# Finite outer-constituent extraction stages

An `OuterConstituentStage` records an exact restriction to an indexed direct sum of whole,
not-yet-evaluated constituents.  It is the lightweight intermediate object used between
recursive hashing stages: no matrix-multiplication leaf, polynomial degeneration, asymptotic
rate, or numerical certificate occurs in this module.

Keeping this finite interface separate lets semantic composition clients verify their proofs
without importing the substantially heavier asymptotic laser-volume development.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x y

section FiniteStage

variable (K : Type u) [CommSemiring K]
variable {Source : Leg → Type v}
variable [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]

/-- A finite restriction to an indexed direct sum of whole, not-yet-evaluated constituents.

Unlike `WholeConstituentLaserVolumeStage`, the constituents here need not already be matrix
multiplication tensors.  This is the correct intermediate object for recursive extraction: the
entire retained constituent remains available to the next exact finite stage. -/
structure OuterConstituentStage
    (source : Tensor3 K Source) (outerCopies : ℕ) where
  I : Type w
  [fintypeI : Fintype I]
  card_I : Fintype.card I = outerCopies
  W : I → Leg → Type x
  [addCommMonoidW : ∀ i c, AddCommMonoid (W i c)]
  [moduleW : ∀ i c, Module K (W i c)]
  constituent : ∀ i, Tensor3 K (W i)
  source_restricts : Restricts source (Tensor.indexedDirectSum constituent)

namespace OuterConstituentStage

/-- Package an exact restriction to a naturally indexed family of whole constituents. -/
noncomputable def ofIndexedConstituents
    {source : Tensor3 K Source} {outerCopies : ℕ}
    {I : Type w} [Fintype I]
    {W : I → Leg → Type x}
    [∀ i c, AddCommMonoid (W i c)] [∀ i c, Module K (W i c)]
    {constituent : ∀ i, Tensor3 K (W i)}
    (hcard : Fintype.card I = outerCopies)
    (hsource : Restricts source (Tensor.indexedDirectSum constituent)) :
    OuterConstituentStage K source outerCopies where
  I := I
  card_I := hcard
  W := W
  constituent := constituent
  source_restricts := hsource

/-- Precompose an outer constituent stage with an exact restriction, preserving its complete
indexed output family and copy count. -/
noncomputable def precompose
    {source : Tensor3 K Source} {outerCopies : ℕ}
    {NewSource : Leg → Type y}
    [∀ c, AddCommMonoid (NewSource c)] [∀ c, Module K (NewSource c)]
    {newSource : Tensor3 K NewSource}
    (hsource : Restricts newSource source)
    (outer : OuterConstituentStage.{u, v, w, x} K source outerCopies) :
    OuterConstituentStage K newSource outerCopies := by
  letI := outer.addCommMonoidW
  letI := outer.moduleW
  exact
    { I := outer.I
      fintypeI := outer.fintypeI
      card_I := outer.card_I
      W := outer.W
      addCommMonoidW := outer.addCommMonoidW
      moduleW := outer.moduleW
      constituent := outer.constituent
      source_restricts := hsource.trans outer.source_restricts }

end OuterConstituentStage

end FiniteStage

end AlgebraicComplexity
