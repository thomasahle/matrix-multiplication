/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ProductUniformOnParts
import AlgebraicComplexity.MatrixMultiplication.SegmentedSplitRestriction

/-!
# Segmented available blocks and the segmented shuffling group

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  `RestrictedSplittingShuffle.lean:187` pins
**one global pooled** type on the available small `Z`-blocks and shuffles them by
`Equiv.Perm (Fin (n+1))` (`:194`).  `[DuanWuZhou2022]`'s `hole_lemma.tex:40` pins a type **per
component**, and its group is `Sym[n_1] x ... x Sym[n_m]` (`hole_lemma.tex:72-74`), whose Claim 1
turns on the destination "staying within the region" (`:95-101`).  This module lays down those two
objects beside the committed ones, which are milestone machinery and are not edited here.

## The two facts that make the joint hole set work

**The committed union bound already accepts a joint hole set.**
`Combinatorics/ShufflingGroup.lean:191`'s `exists_shuffles_avoiding` is group-agnostic and takes an
**arbitrary** `holes : ι → Finset A` over the whole part set, its own docstring recording that "the
bound does not depend on how the holes of different copies are related; only their sizes enter".
Instantiated at the segmented part set and the product group it is `[DuanWuZhou2022]`'s union bound
over `∏_t Avail_t` verbatim, with holes that need **not** be a product.  That is
`exists_segmented_shuffles_avoiding` below, and it is one line.

**Claim 3 reduces to two purely combinatorial equivalences.**
`segmentedShuffleUniformity_of_equiv` shows that the segmented Claim-3 analogue follows from
`HoleRepair.UniformOnParts.pi` — the `m`-fold product of the committed single-type uniformity
`WordShuffle.uniformOnTypedWords` (`ShufflingGroup.lean:377`) — as soon as one exhibits

* `SegmentPerm seg ≃ ∀ t, Equiv.Perm (Fin |seg⁻¹ t|)`, and
* `SegmentedAvailableWord seg α ≃ ∀ t, WordShuffle.TypedWord I |seg⁻¹ t| (α t)`.

Neither mentions a tensor, a distribution or a hole; both are re-indexings of a word by its
segments.  So the remaining content of the segmented Hole Lemma is *combinatorial book-keeping*,
not new mathematics — and `[DuanWuZhou2022]`'s own count `∏_t ∏_{k'} (α̃_t(k') n_t)!`
(`hole_lemma.tex:111-120`) is exactly the product of the per-segment counts this factorization
produces.

## What is deliberately a hypothesis

`SegmentedShuffleUniformity` is a *parameter* of every statement here.  Whether the product group
acting with **independent** per-component shuffles is the group `[DuanWuZhou2022]`'s
`∑_t η_t ≥ Nℓ + 1` union bound needs is the open question of the Z-side adjudication, and this
module does not prejudge it.  What it does establish is that *if* it is, the discharge is the two
equivalences above and nothing else.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w

section Segmented

variable {I : Type w} [Fintype I] [DecidableEq I] {n m : ℕ}

/-- **Available small blocks with a per-segment type** — `hole_lemma.tex:40`.  Compare the
committed pooled form `AvailableWord` (`RestrictedSplittingShuffle.lean:187`), which constrains
only the sum of these types (`sum_segmentMultiplicity`). -/
def SegmentedAvailableWord (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ) :=
  {word : PositiveWord I n //
    ∀ t, segmentMultiplicity seg (positiveWordEquiv I n word) t = α t}

noncomputable instance segmentedAvailableWordDecidablePred
    (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ) :
    DecidablePred fun word : PositiveWord I n ↦
      ∀ t, segmentMultiplicity seg (positiveWordEquiv I n word) t = α t :=
  fun _ ↦ Classical.dec _

noncomputable instance segmentedAvailableWordFintype
    (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ) :
    Fintype (SegmentedAvailableWord seg α) :=
  Subtype.fintype _

noncomputable instance segmentedAvailableWordDecidableEq
    (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ) :
    DecidableEq (SegmentedAvailableWord seg α) :=
  fun _ _ ↦ Classical.dec _

/-- **The segmented shuffling group** `Sym[n_1] x ... x Sym[n_m]` of `hole_lemma.tex:72-74`. -/
def SegmentPerm (seg : Fin (n + 1) → Fin m) := ∀ t : Fin m, Equiv.Perm {i // seg i = t}

noncomputable instance segmentPermFintype (seg : Fin (n + 1) → Fin m) :
    Fintype (SegmentPerm seg) := by
  classical
  exact Pi.instFintype

noncomputable instance segmentPermDecidableEq (seg : Fin (n + 1) → Fin m) :
    DecidableEq (SegmentPerm seg) := fun _ _ ↦ Classical.dec _

instance segmentPermOne (seg : Fin (n + 1) → Fin m) : Nonempty (SegmentPerm seg) :=
  ⟨fun _ ↦ Equiv.refl _⟩

/-- A segmented shuffle, read as a permutation of all positions. -/
def segmentPermToPerm (seg : Fin (n + 1) → Fin m) (φ : SegmentPerm seg) :
    Equiv.Perm (Fin (n + 1)) :=
  (Equiv.sigmaFiberEquiv seg).symm.trans
    ((Equiv.sigmaCongrRight φ).trans (Equiv.sigmaFiberEquiv seg))

/-- **Segmented shuffles stay within their segment** — `hole_lemma.tex:95-101`'s "stays within the
region", which is exactly what fails for the committed full symmetric group. -/
theorem seg_segmentPermToPerm (seg : Fin (n + 1) → Fin m) (φ : SegmentPerm seg)
    (i : Fin (n + 1)) : seg (segmentPermToPerm seg φ i) = seg i :=
  (φ (seg i) ⟨i, rfl⟩).2

/-! ## The Claim-3 analogue, carried as a hypothesis -/

/-- **The segmented Claim 3**, as a parameter.  See the module docstring: this module does not
prejudge whether the product group with independent per-component shuffles is the group
`[DuanWuZhou2022]`'s union bound needs. -/
abbrev SegmentedShuffleUniformity (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ) :=
  HoleRepair.UniformOnParts (SegmentPerm seg) (SegmentedAvailableWord seg α)

/-- **Claim 3 reduces to two re-indexings.**

Given an identification of the segmented shuffle group with a product of symmetric groups, and of
the segmented available words with the corresponding product of singly-typed words, the segmented
uniformity is the `m`-fold product `HoleRepair.UniformOnParts.pi` of the committed single-type
uniformity, transported by `HoleRepair.UniformOnParts.congrEquiv`.

Neither equivalence mentions tensors, distributions or holes. -/
noncomputable def segmentedShuffleUniformity_of_equiv
    {seg : Fin (n + 1) → Fin m} {α : Fin m → I → ℕ}
    (eg : SegmentPerm seg ≃ ∀ t : Fin m, Equiv.Perm (Fin (Fintype.card {i // seg i = t})))
    (ea : SegmentedAvailableWord seg α ≃
      ∀ t : Fin m, WordShuffle.TypedWord I (Fintype.card {i // seg i = t}) (α t)) :
    SegmentedShuffleUniformity seg α :=
  HoleRepair.UniformOnParts.congrEquiv
    (HoleRepair.UniformOnParts.pi fun t : Fin m ↦
      WordShuffle.uniformOnTypedWords (α t) (Fintype.card {i // seg i = t})) eg ea

/-! ## The union bound with a joint hole set -/

/-- **`[DuanWuZhou2022]`'s Hole-Lemma union bound over the segmented available blocks, with a
JOINT hole set.**

`holes` is an arbitrary `Finset` of segmented available words per copy --- **not** a product of
per-component hole sets.  This is `def:broken_standard_form_tensor` (`hole_lemma.tex:48`), where a
hole is one global sequence spanning all components.  Nothing new is proved: the committed
`exists_shuffles_avoiding` is already group-agnostic and already hole-shape-agnostic, and this is
its instantiation at the segmented part set and the segmented group. -/
theorem exists_segmented_shuffles_avoiding
    {seg : Fin (n + 1) → Fin m} {α : Fin m → I → ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (uniformity : SegmentedShuffleUniformity seg α)
    (holes : ι → Finset (SegmentedAvailableWord seg α))
    (hsmall : Fintype.card (SegmentedAvailableWord seg α) * ∏ t, (holes t).card <
      Fintype.card (SegmentedAvailableWord seg α) ^ Fintype.card ι) :
    ∃ shuffle : ι → SegmentPerm seg,
      ∀ a : SegmentedAvailableWord seg α, ∃ t : ι,
        uniformity.relabel (shuffle t) a ∉ holes t :=
  exists_shuffles_avoiding uniformity holes hsmall

end Segmented

end AlgebraicComplexity
