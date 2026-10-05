/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ShufflingGroup

/-!
# The `m`-fold product of shuffling families

Layer 1 (`AlgebraicComplexity/Combinatorics/`).  `Combinatorics/ShufflingGroup.lean` proves the
binary product law `HoleRepair.UniformOnParts.prod` (`:129`) and says in its own docstring that
`[DuanWuZhou2022]`'s shuffling group `Sym[n_1] x ... x Sym[n_m]` is obtained "by iterating this
binary construction".  A segmented restricted-splitting power needs the `m`-fold form directly,
indexed by the segments rather than built by association.

`UniformOnParts.pi` is that form.  It is proved the same way as the binary case and not by
iterating it: the fibre of a target under the pointwise action is literally
`Fintype.piFinset` of the factor fibres, so `Fintype.card_piFinset` turns its cardinality into a
product of factor cardinalities, and target-independence follows factor by factor from
`UniformOnParts.uniform_point`.

This is the group side of the segmentation programme.  It is stated for an arbitrary index type,
so a client may take the segments of a word, the components of a standard-form tensor, or anything
else; nothing here mentions words, tensors or a distribution.

`Combinatorics/ShufflingGroup.lean:191`'s `exists_shuffles_avoiding` is already group-agnostic and
already takes an **arbitrary** hole family `holes : ι → Finset A` over the whole part set `A`, with
its docstring recording that "the bound does not depend on how the holes of different copies are
related; only their sizes enter".  So once `A` is the *segmented* part set and `G` is the product
group supplied here, the union bound of the Hole Lemma applies verbatim to a **joint**, that is
non-rectangular, hole set.
-/

namespace AlgebraicComplexity

open scoped BigOperators

universe u v w

namespace HoleRepair.UniformOnParts

variable {ι : Type w} [Fintype ι] [DecidableEq ι]
variable {G : ι → Type u} {A : ι → Type v}
variable [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)]
variable [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- The fibre of a pointwise target under the pointwise action is the product of the factor
fibres. -/
theorem filter_piCongrRight_eq_piFinset
    (family : ∀ i, UniformOnParts (G i) (A i)) (a c : ∀ i, A i) :
    (Finset.univ.filter fun g : ∀ i, G i ↦
        (Equiv.piCongrRight fun i ↦ (family i).relabel (g i)) a = c) =
      Fintype.piFinset fun i ↦
        Finset.univ.filter fun gi : G i ↦ (family i).relabel gi (a i) = c i := by
  classical
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
    Equiv.piCongrRight_apply, funext_iff]
  exact Iff.rfl

/-- **The `m`-fold product of shuffling families.**

`[DuanWuZhou2022]`'s group `Sym[n_1] x ... x Sym[n_m]` acting factorwise, in the indexed form a
segmentation produces.  The binary `UniformOnParts.prod` is the case `ι = Fin 2`. -/
noncomputable def pi (family : ∀ i, UniformOnParts (G i) (A i)) :
    UniformOnParts (∀ i, G i) (∀ i, A i) := by
  classical
  refine ofTargetIndependentFiber
    (fun g ↦ Equiv.piCongrRight fun i ↦ (family i).relabel (g i)) ?_
  intro a b b'
  rw [filter_piCongrRight_eq_piFinset family a b,
    filter_piCongrRight_eq_piFinset family a b',
    Fintype.card_piFinset, Fintype.card_piFinset]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have hApos : 0 < Fintype.card (A i) := Fintype.card_pos_iff.2 ⟨a i⟩
  have h₁ := (family i).uniform_point (a i) (b i)
  have h₂ := (family i).uniform_point (a i) (b' i)
  exact Nat.eq_of_mul_eq_mul_left hApos (h₁.trans h₂.symm)

@[simp] theorem pi_relabel (family : ∀ i, UniformOnParts (G i) (A i)) (g : ∀ i, G i) :
    (pi family).relabel g = Equiv.piCongrRight fun i ↦ (family i).relabel (g i) := rfl


/-! ## Transport along equivalences -/

variable {G' : Type u} {A' : Type v} [Fintype G'] [DecidableEq G'] [Fintype A'] [DecidableEq A']
variable {G'' : Type u} {A'' : Type v} [Fintype G''] [DecidableEq G''] [Fintype A''] [DecidableEq A'']

/-- **A uniform family transports along equivalences of the group and of the part set.**

This is the glue a segmented client needs: the Claim-3 analogue for segmented available words is
`pi` above, read through the re-indexing that identifies segmented available words with the product
of the per-segment typed words, and that identification is an equivalence. -/
noncomputable def congrEquiv (family : UniformOnParts G'' A'')
    (eg : G' ≃ G'') (ea : A' ≃ A'') : UniformOnParts G' A' := by
  classical
  refine ofTargetIndependentFiber
    (fun g ↦ (ea.trans ((family.relabel (eg g)).trans ea.symm))) ?_
  intro a b b'
  have hfib : ∀ c : A',
      (Finset.univ.filter fun g : G' ↦
          (ea.trans ((family.relabel (eg g)).trans ea.symm)) a = c).card =
        (Finset.univ.filter fun h : G'' ↦ family.relabel h (ea a) = ea c).card := by
    intro c
    refine Finset.card_nbij' (fun g ↦ eg g) (fun h ↦ eg.symm h) ?_ ?_ ?_ ?_
    · intro g hg
      rw [Finset.mem_coe, Finset.mem_filter] at hg
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hg2 : ea.symm (family.relabel (eg g) (ea a)) = c := hg.2
      rw [← hg2, ea.apply_symm_apply]
    · intro h hh
      rw [Finset.mem_coe, Finset.mem_filter] at hh
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      show ea.symm (family.relabel (eg (eg.symm h)) (ea a)) = c
      rw [eg.apply_symm_apply, hh.2, ea.symm_apply_apply]
    · intro g _
      simp
    · intro h _
      simp
  rw [hfib b, hfib b']
  have hApos : 0 < Fintype.card A'' := Fintype.card_pos_iff.2 ⟨ea a⟩
  have h₁ := family.uniform_point (ea a) (ea b)
  have h₂ := family.uniform_point (ea a) (ea b')
  exact Nat.eq_of_mul_eq_mul_left hApos (h₁.trans h₂.symm)

end HoleRepair.UniformOnParts

end AlgebraicComplexity
