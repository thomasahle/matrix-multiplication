/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SegmentedLocalizedDivision
import AlgebraicComplexity.MatrixMultiplication.TauValueDirectSum

set_option autoImplicit false

/-!
# Iterating the regional division of a localized segmented leaf

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).
`MatrixMultiplication/SegmentedLocalizedDivision.lean` splits a localized segmented leaf into
**two** consecutive regions.  `[duan2023faster]`'s section 6.3 leaf has fifteen, so the binary
form has to be iterated.  This module does that iteration once and for all, for an arbitrary
finite list of consecutive regions.

## Why the iterated external product is never named

`HasTauWeight.external` (`MatrixMultiplication/TauValueDirectSum.lean`) and
`Tensor.Isomorphic.symSix_external` are **binary**, and the factors of the section 6.3 product
live in fifteen *different* block-space types --- `PositivePowerBlockSpace K V (size t)`, one per
region.  An `n`-ary external product would therefore have to be a dependent recursive
construction, and every statement about it would then carry that construction.

The way out is to iterate the weight law *alongside* the division, so that no iterated tensor is
ever written down: the theorem below takes one `HasTauWeight` fact per region and concludes one
`HasTauWeight` fact about the parent leaf, with the product of the regional weights.  The
intermediate external products appear only inside the induction.

## The shape of the regional data

A region is a `SegmentRegionSpec`: `size + 1` positions, a per-segment type on the restricted leg,
and the weight its factor carries.  The regions are given as a nonempty list --- a head and a tail
--- because `positiveWordAppend` concatenates two *nonempty* words, so an empty region cannot be
peeled.  In the section 6.3 instance every region is nonempty because every entry of `dwz63Alpha`
is strictly positive.

`SegmentedRegionalWeights` is the hypothesis, defined by recursion on that list.  It bundles, for
each peel, the two regional coarse targets (existentially --- the client chooses them), the
statement that the parent target is their concatenation, and the head region's weight.  Bundling
them recursively is what lets the segmentation of each region be *named*: it is the parent
segmentation restricted by `segmentationLeft` / `segmentationRight`, iterated, and there is no
uniform way to write that as a family indexed by the region number without a junk value in
`Fin M`.

The parent's prescribed type is the pointwise sum of the regional types, which is `claim:degen`'s
hypothesis; on a single restricted leg `SegmentedSplitRestriction.ofLeg_sum` discharges it.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `hole_lemma.tex` and `global_value.tex` section 6.3.

Exact source lines: `papers/sources/2210.10173/global_value.tex:332-378` (§6.3),
`papers/sources/2210.10173/component_value.tex:18-24` (`claim:degen`),
`papers/sources/2210.10173/hole_lemma.tex:1-168` (whole file).
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x

/-! ## Region specifications -/

/-- **One consecutive region of a localized segmented leaf.**  It holds `size + 1` positions, it
prescribes `type` as the per-segment empirical type on the restricted leg, and its factor carries
the `tau`-weight `value`. -/
structure SegmentRegionSpec (A : Leg → Type w) (c₀ : Leg) (M : ℕ) where
  /-- The region holds `size + 1` positions.  Positive because `positiveWordAppend` concatenates
  nonempty words. -/
  size : ℕ
  /-- The per-segment empirical type prescribed on the restricted leg `c₀`. -/
  type : Fin M → A c₀ → ℕ
  /-- The `tau`-weight the region's factor carries. -/
  value : ℝ

namespace SegmentRegionSpec

variable {A : Leg → Type w} {c₀ : Leg} {M : ℕ}

/-- The additional-letter parameter of the concatenation of a head region and a tail of further
regions: `size + 1` positions each, laid end to end. -/
def total : SegmentRegionSpec A c₀ M → List (SegmentRegionSpec A c₀ M) → ℕ
  | s, [] => s.size
  | s, t :: rest => s.size + total t rest + 1

@[simp] theorem total_nil (s : SegmentRegionSpec A c₀ M) : total s [] = s.size := rfl

@[simp] theorem total_cons (s t : SegmentRegionSpec A c₀ M)
    (rest : List (SegmentRegionSpec A c₀ M)) :
    total s (t :: rest) = s.size + total t rest + 1 := rfl

/-- The parent's per-segment type is the pointwise sum of the regional types.  This is
`[duan2023faster]`'s `claim:degen` hypothesis, additively. -/
def parentType : SegmentRegionSpec A c₀ M → List (SegmentRegionSpec A c₀ M) →
    (Fin M → A c₀ → ℕ)
  | s, [] => s.type
  | s, t :: rest => s.type + parentType t rest

@[simp] theorem parentType_nil (s : SegmentRegionSpec A c₀ M) : parentType s [] = s.type := rfl

@[simp] theorem parentType_cons (s t : SegmentRegionSpec A c₀ M)
    (rest : List (SegmentRegionSpec A c₀ M)) :
    parentType s (t :: rest) = s.type + parentType t rest := rfl

/-- The parent's weight is the product of the regional weights. -/
def totalValue : SegmentRegionSpec A c₀ M → List (SegmentRegionSpec A c₀ M) → ℝ
  | s, [] => s.value
  | s, t :: rest => s.value * totalValue t rest

@[simp] theorem totalValue_nil (s : SegmentRegionSpec A c₀ M) : totalValue s [] = s.value := rfl

@[simp] theorem totalValue_cons (s t : SegmentRegionSpec A c₀ M)
    (rest : List (SegmentRegionSpec A c₀ M)) :
    totalValue s (t :: rest) = s.value * totalValue t rest := rfl

/-- A product of nonnegative regional weights is nonnegative.  `HasTauWeight.external` needs
this at every peel. -/
theorem totalValue_nonneg :
    ∀ (s : SegmentRegionSpec A c₀ M) (rest : List (SegmentRegionSpec A c₀ M)),
      0 ≤ s.value → (∀ u ∈ rest, 0 ≤ u.value) → 0 ≤ totalValue s rest
  | _, [], hs, _ => hs
  | s, t :: rest, hs, hrest => by
      rw [totalValue_cons]
      exact mul_nonneg hs
        (totalValue_nonneg t rest (hrest t (List.mem_cons_self ..))
          fun u hu ↦ hrest u (List.mem_cons_of_mem t hu))

end SegmentRegionSpec

/-! ## The regional weight hypothesis -/

section Regional

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {M : ℕ}

/-- **The regional weight hypothesis.**

Defined by recursion on the list of remaining regions.  At each peel it supplies the two regional
coarse targets, the statement that the parent target is their concatenation, and a `tau`-weight
for the head region's factor --- at the segmentation the peel induces on that region.  The last
region is the base case: there the parent leaf *is* the regional leaf. -/
def SegmentedRegionalWeights (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (c₀ : Leg) (τ : ℝ) :
    (s : SegmentRegionSpec A c₀ M) → (rest : List (SegmentRegionSpec A c₀ M)) →
      (Fin (SegmentRegionSpec.total s rest + 1) → Fin M) →
      BlockAddress (fun c ↦ PositiveWord (B c) (SegmentRegionSpec.total s rest)) → Prop
  | s, [], seg, target =>
      HasTauWeight K
        (P.segmentedLocalizedSplittingPower f s.size M seg
          (SegmentedSplitRestriction.ofLeg c₀ s.type) target).realize τ s.value
  | s, t :: rest, seg, target =>
      ∃ (targetHead : BlockAddress (fun c ↦ PositiveWord (B c) s.size))
        (targetTail : BlockAddress
          (fun c ↦ PositiveWord (B c) (SegmentRegionSpec.total t rest))),
        (∀ c, target c = positiveWordAppend (targetHead c)
          (SegmentRegionSpec.total t rest) (targetTail c)) ∧
        HasTauWeight K
          (P.segmentedLocalizedSplittingPower f s.size M
            (segmentationLeft s.size (SegmentRegionSpec.total t rest) seg)
            (SegmentedSplitRestriction.ofLeg c₀ s.type) targetHead).realize τ s.value ∧
        SegmentedRegionalWeights P f c₀ τ t rest
          (segmentationRight s.size (SegmentRegionSpec.total t rest) seg) targetTail

omit [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
/-- **The iterated regional division, as a weight law.**

`[duan2023faster]`'s `claim:degen` iterated over an arbitrary finite list of consecutive regions,
composed with the weight law at every peel.  One `HasTauWeight` per region in, one `HasTauWeight`
for the whole leaf out, with the product of the regional weights.  No iterated external product is
named: it is built and consumed inside the induction. -/
theorem hasTauWeight_segmentedLocalizedSplittingPower_regional
    (P : PartitionedTensor (K := K) (A := A) V) (f : ∀ c, A c → B c) (c₀ : Leg) {τ : ℝ} :
    ∀ (s : SegmentRegionSpec A c₀ M) (rest : List (SegmentRegionSpec A c₀ M))
      (seg : Fin (SegmentRegionSpec.total s rest + 1) → Fin M)
      (target : BlockAddress (fun c ↦ PositiveWord (B c) (SegmentRegionSpec.total s rest))),
      0 ≤ s.value → (∀ u ∈ rest, 0 ≤ u.value) →
      SegmentedRegionalWeights P f c₀ τ s rest seg target →
      HasTauWeight K
        (P.segmentedLocalizedSplittingPower f (SegmentRegionSpec.total s rest) M seg
          (SegmentedSplitRestriction.ofLeg c₀ (SegmentRegionSpec.parentType s rest))
          target).realize τ (SegmentRegionSpec.totalValue s rest)
  | _, [], _, _, _, _, h => h
  | s, t :: rest, seg, target, hs, hrest, h => by
      obtain ⟨targetHead, targetTail, htarget, hhead, htail⟩ := h
      have hrestHead : 0 ≤ t.value := hrest t (List.mem_cons_self ..)
      have hrestTail : ∀ u ∈ rest, 0 ≤ u.value := fun u hu ↦ hrest u
        (List.mem_cons_of_mem t hu)
      have htailWeight := hasTauWeight_segmentedLocalizedSplittingPower_regional P f c₀ t rest
        (segmentationRight s.size (SegmentRegionSpec.total t rest) seg) targetTail
        hrestHead hrestTail htail
      have hprod := hhead.external htailWeight hs
        (SegmentRegionSpec.totalValue_nonneg t rest hrestHead hrestTail)
      refine hprod.of_restricts ?_
      exact Tensor.Restricts.segmentedLocalizedSplittingPower_binaryDivision P f seg
        (SegmentedSplitRestriction.ofLeg c₀ (SegmentRegionSpec.parentType s (t :: rest)))
        (SegmentedSplitRestriction.ofLeg c₀ s.type)
        (SegmentedSplitRestriction.ofLeg c₀ (SegmentRegionSpec.parentType t rest))
        (SegmentedSplitRestriction.ofLeg_sum c₀ (SegmentRegionSpec.parentType s (t :: rest))
          s.type (SegmentRegionSpec.parentType t rest) (fun _ ↦ rfl))
        target targetHead targetTail htarget

end Regional

end AlgebraicComplexity
