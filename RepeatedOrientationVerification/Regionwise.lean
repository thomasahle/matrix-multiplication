import Mathlib

set_option linter.style.header false

/-!
# Abstract repeated-orientation theorem

This file formalizes the precise algebraic principle used by the proposed repeated-orientation
extension. It does not assume that orientations are distinct.

The remaining mathematical task is to instantiate `RegionwiseSystem` with the actual recursive
tensor degeneration and extraction relation from the matrix-multiplication proof.
-/

namespace RepeatedOrientationVerification

universe u v

/--
An abstract extraction system in which independent labelled regions tensor together and every
orientation preserves the extraction relation.
-/
structure RegionwiseSystem (Tensor : Type u) (Orientation : Type v) [CommMonoid Tensor] where
  rel : Tensor → Tensor → Prop
  one : rel 1 1
  tensor : ∀ {a b c d : Tensor}, rel a b → rel c d → rel (a * c) (b * d)
  orient : Orientation → Tensor → Tensor
  orient_rel : ∀ (σ : Orientation) {a b : Tensor}, rel a b → rel (orient σ a) (orient σ b)

namespace RegionwiseSystem

variable {Tensor : Type u} {Orientation : Type v} [CommMonoid Tensor]

/-- Independent regionwise extractions tensor over an arbitrary finite set of labels. -/
theorem finset_tensor
    (S : RegionwiseSystem Tensor Orientation)
    {ι : Type*} (s : Finset ι) (source target : ι → Tensor)
    (h : ∀ i ∈ s, S.rel (source i) (target i)) :
    S.rel (∏ i ∈ s, source i) (∏ i ∈ s, target i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using S.one
  | @insert x s hx ih =>
      rw [Finset.prod_insert hx, Finset.prod_insert hx]
      exact S.tensor
        (h x (Finset.mem_insert_self x s))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/--
Arbitrary orientations may be assigned to labelled regions. The function `σ` need not be
injective, so this theorem explicitly permits repeated orientations.
-/
theorem arbitrary_orientations
    (S : RegionwiseSystem Tensor Orientation)
    {ι : Type*} [Fintype ι]
    (σ : ι → Orientation) (source target : ι → Tensor)
    (h : ∀ i, S.rel (source i) (target i)) :
    S.rel
      (∏ i, S.orient (σ i) (source i))
      (∏ i, S.orient (σ i) (target i)) := by
  classical
  apply S.finset_tensor Finset.univ
  intro i _
  exact S.orient_rel (σ i) (h i)

/-- A single orientation may be repeated on all six labelled regions. -/
theorem six_repeated_orientation
    (S : RegionwiseSystem Tensor Orientation)
    (σ : Orientation) (source target : Fin 6 → Tensor)
    (h : ∀ i, S.rel (source i) (target i)) :
    S.rel
      (∏ i, S.orient σ (source i))
      (∏ i, S.orient σ (target i)) := by
  simpa using S.arbitrary_orientations (fun _ : Fin 6 => σ) source target h

#print axioms RegionwiseSystem.finset_tensor
#print axioms RegionwiseSystem.arbitrary_orientations
#print axioms RegionwiseSystem.six_repeated_orientation

end RegionwiseSystem
end RepeatedOrientationVerification
