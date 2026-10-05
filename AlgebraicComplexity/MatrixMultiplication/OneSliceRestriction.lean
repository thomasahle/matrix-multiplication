/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.OneSliceProduct

/-!
# Explicit restrictions to one-slice matrix-multiplication tensors

An ordinary proof of `Restricts T ⟨1,d,1⟩` hides the three linear maps behind an existential.
That is insufficient when several constituents share a source leg: their maps on the shared leg
must be literally the same map before the constituent restrictions can be assembled globally.

`OneSliceRestriction T d` retains the actual leg maps.  The binary product constructor uses the
explicit lightweight one-slice matrix product map, and the accompanying `Z`-map theorem makes
the crucial coherence visible: on the one-slice family, the product map on `Z` is independent of
the two middle dimensions.  This is reusable semantic infrastructure; it contains no C-tensor,
CW-support, type-counting, or asymptotic assumptions.  Retyping into canonical C-tensor spaces is
kept in the optional downstream module `OneSliceCTensor` so clients do not pay that import cost.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

variable {K : Type u} [CommSemiring K]

/-- An exact restriction to `⟨1,d,1⟩` with its three witnessing maps exposed.

Keeping `legMap` as data, rather than storing only `Restricts`, is what permits a later C-tensor
client to prove that every constituent uses one common map on its shared `Z` block. -/
structure OneSliceRestriction
    {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
    (T : Tensor3 K V) (d : ℕ) where
  /-- The three concrete source-to-matrix-space maps. -/
  legMap : ∀ c, V c →ₗ[K] MMSpace K 1 d 1 c
  /-- Applying those maps gives the stated one-slice matrix tensor exactly. -/
  map_eq : Tensor.map legMap T = matrixMultiplication (K := K) 1 d 1

namespace OneSliceRestriction

variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
variable {T : Tensor3 K V} {S : Tensor3 K W}
variable {d e : ℕ}

/-- Identity certificate for the canonical one-slice matrix tensor.  Besides being useful in
compositions, this is a tiny semantic inhabitant showing that the map-level interface is not
merely propositionally satisfiable. -/
def self (d : ℕ) :
    OneSliceRestriction (matrixMultiplication (K := K) 1 d 1) d where
  legMap := fun _c ↦ LinearMap.id
  map_eq := by simp

/-- Transport a certificate across an equality of its middle dimension. -/
def castDimension {d' : ℕ} (C : OneSliceRestriction T d) (h : d = d') :
    OneSliceRestriction T d' := by
  subst d'
  exact C

/-- Product of two explicit one-slice restrictions.

The target dimensions multiply because the explicit map in `OneSliceProduct` carries
`⟨1,d,1⟩ ⊠ ⟨1,e,1⟩` onto `⟨1,d e,1⟩`.  Unlike the proposition-level product law, this constructor
retains the resulting leg maps. -/
noncomputable def external
    (left : OneSliceRestriction T d) (right : OneSliceRestriction S e) :
    OneSliceRestriction (Tensor.external T S) (d * e) where
  legMap := OneSliceProduct.legMapAfter d e left.legMap right.legMap
  map_eq := by
    rw [OneSliceProduct.map_external_after, left.map_eq, right.map_eq,
      OneSliceProduct.map_external_matrixMultiplication]

/-- The exposed `Z` map of a product certificate. -/
@[simp] theorem external_legMap_Z
    (left : OneSliceRestriction T d) (right : OneSliceRestriction S e) :
    (left.external right).legMap .Z =
      OneSliceProduct.coordinateProductMapAfter
        (OneSliceProduct.indexProductEquiv d e .Z)
        (left.legMap .Z) (right.legMap .Z) :=
  rfl

/-- Product `Z` maps depend only on the two input `Z` maps, not on their middle dimensions.

This is the coherence property needed when different words have the same shared source `Z`
block but different arrangements of one-dimensional and `q`-dimensional letters. -/
theorem external_legMap_Z_congr
    {d' e' : ℕ}
    (left : OneSliceRestriction T d) (left' : OneSliceRestriction T d')
    (right : OneSliceRestriction S e) (right' : OneSliceRestriction S e')
    (hleft : left.legMap .Z = left'.legMap .Z)
    (hright : right.legMap .Z = right'.legMap .Z) :
    (left.external right).legMap .Z = (left'.external right').legMap .Z := by
  change
    OneSliceProduct.coordinateProductMapAfter
        (OneSliceProduct.indexProductEquiv 1 1 .Z)
        (left.legMap .Z) (right.legMap .Z) =
      OneSliceProduct.coordinateProductMapAfter
        (OneSliceProduct.indexProductEquiv 1 1 .Z)
        (left'.legMap .Z) (right'.legMap .Z)
  rw [hleft, hright]

/-- Tiny two-factor client: the explicit product of two identity certificates maps the external
product tensor to `⟨1,d e,1⟩`. -/
theorem self_external_map_eq (d e : ℕ) :
    Tensor.map ((self (K := K) d).external (self (K := K) e)).legMap
        (Tensor.external
          (matrixMultiplication (K := K) 1 d 1)
          (matrixMultiplication (K := K) 1 e 1)) =
      matrixMultiplication (K := K) 1 (d * e) 1 :=
  ((self (K := K) d).external (self (K := K) e)).map_eq

end OneSliceRestriction

end AlgebraicComplexity
