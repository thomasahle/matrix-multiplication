/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SymSixDistribution

set_option autoImplicit false

/-!
# Finite assembly of two cyclic uniform extractions

This module formalizes the Total-Weight manuscript's cyclic product assembly corollary
`cor:cyclic-product-assembly` in `better_bound/paper.tex:2034-2057`, immediately after
`lem:mixed-cyclic-assembly`.  Each input has already been extracted as uniform copies of a cyclic
child.  Their external product retains every Cartesian pair of copies and returns the cyclic
product of the two children.

This theorem only assembles completed local extractions.  It supplies no hashing, input-profile
selection, damaged-fiber model, repair estimate, or child-interface identification.
-/

namespace AlgebraicComplexity.Tensor

universe u v w x y a b

variable {K : Type u} [CommSemiring K]
variable {VA : Leg → Type v} [∀ c, AddCommMonoid (VA c)] [∀ c, Module K (VA c)]
variable {VB : Leg → Type w} [∀ c, AddCommMonoid (VB c)] [∀ c, Module K (VB c)]
variable {WA : Leg → Type x} [∀ c, AddCommMonoid (WA c)] [∀ c, Module K (WA c)]
variable {WB : Leg → Type y} [∀ c, AddCommMonoid (WB c)] [∀ c, Module K (WB c)]
variable {I : Type a} [Fintype I] {J : Type b} [Fintype J]

/-- Combine two cyclic uniform extractions, retaining one output for every Cartesian pair of
input-copy indices.

Proof sketch: shuffle `symThree` of the external source into the external product of the two
cyclic sources, apply the restrictions factorwise, distribute the two indexed direct sums, and
undo the same shuffle independently on every child summand. -/
theorem Restricts.symThree_external_indexedDirectSum
    {RA : Tensor3 K VA} {RB : Tensor3 K VB}
    {IA : Tensor3 K WA} {IB : Tensor3 K WB}
    (hA : Restricts (symThree K RA)
      (Tensor.indexedDirectSum (fun _ : I ↦ symThree K IA)))
    (hB : Restricts (symThree K RB)
      (Tensor.indexedDirectSum (fun _ : J ↦ symThree K IB))) :
    Restricts (symThree K (Tensor.external RA RB))
      (Tensor.indexedDirectSum (fun _ : I × J ↦
        symThree K (Tensor.external IA IB))) := by
  refine (Isomorphic.symThree_external RA RB).restricts.trans ?_
  refine (hA.external hB).trans ?_
  refine (Isomorphic.external_indexedDirectSum
    (fun _ : I ↦ symThree K IA)
    (fun _ : J ↦ symThree K IB)).restricts.trans ?_
  exact Restricts.indexedDirectSum fun _ ↦
    (Isomorphic.symThree_external IA IB).symm.restricts

end AlgebraicComplexity.Tensor
