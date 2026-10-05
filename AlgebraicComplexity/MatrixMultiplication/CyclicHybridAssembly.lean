/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SymSixUniformLeaf

set_option autoImplicit false

/-!
# Finite assembly of ordinary and cyclic uniform extractions

This is the Total-Weight manuscript's own mixed cyclic assembly lemma
`lem:mixed-cyclic-assembly` in `better_bound/paper.tex`, final-assembly section. Its
distribution-after-local-extraction principle is analogous to the final six-orientation step
in [DuanWuZhou2022], Section 6, `papers/sources/2210.10173/global_value.tex:104-121`;
that paper does not state this mixed ordinary/cyclic lemma.

One factor supplies ordinary copies of an arbitrary child tensor, and another supplies cyclic
copies of another arbitrary child tensor. The theorem derives the restriction of their combined
cyclic source, keeping every Cartesian summand. There are `|I|^3 * |J|` copies, not `|I| * |J|`
or `(|I| * |J|)^3`. Local hashing, input-profile selection, and repair must already be proved
for the two factors; no restriction of the assembled source is a hypothesis.
-/

namespace AlgebraicComplexity.Tensor

universe u v w x y a b

variable {K : Type u} [CommSemiring K]
variable {VA : Leg → Type v} [∀ c, AddCommMonoid (VA c)] [∀ c, Module K (VA c)]
variable {VB : Leg → Type w} [∀ c, AddCommMonoid (VB c)] [∀ c, Module K (VB c)]
variable {WA : Leg → Type x} [∀ c, AddCommMonoid (WA c)] [∀ c, Module K (WA c)]
variable {WB : Leg → Type y} [∀ c, AddCommMonoid (WB c)] [∀ c, Module K (WB c)]
variable {I : Type a} [Fintype I] {J : Type b} [Fintype J]

/-- Combine an ordinary uniform extraction with a cyclic uniform extraction. The output child
tensor is preserved literally up to the canonical external-product isomorphism.

Proof sketch: cyclically tensor the first restriction and distribute its three uniform sums.
Reassociate the combined source, apply the two factorwise restrictions, distribute their sums,
and reassociate every resulting child product. -/
theorem Restricts.symThree_hybrid_indexedDirectSum
    {RA : Tensor3 K VA} {RB : Tensor3 K VB}
    {IA : Tensor3 K WA} {IB : Tensor3 K WB}
    (hA : Restricts RA (Tensor.indexedDirectSum (fun _ : I ↦ IA)))
    (hB : Restricts (symThree K RB)
      (Tensor.indexedDirectSum (fun _ : J ↦ symThree K IB))) :
    Restricts (symThree K (Tensor.external RA RB))
      (Tensor.indexedDirectSum (fun _ : ((I × I) × I) × J ↦
        symThree K (Tensor.external IA IB))) := by
  have hA3 : Restricts (symThree K RA)
      (Tensor.indexedDirectSum (fun _ : (I × I) × I ↦ symThree K IA)) :=
    hA.symThree_congr.trans
      (Isomorphic.symThree_indexedDirectSum_uniform (ι := I) IA).restricts
  refine (Isomorphic.symThree_external RA RB).restricts.trans ?_
  refine (hA3.external hB).trans ?_
  refine (Isomorphic.external_indexedDirectSum
    (fun _ : (I × I) × I ↦ symThree K IA)
    (fun _ : J ↦ symThree K IB)).restricts.trans ?_
  exact Restricts.indexedDirectSum fun _ ↦
    (Isomorphic.symThree_external IA IB).symm.restricts

end AlgebraicComplexity.Tensor
