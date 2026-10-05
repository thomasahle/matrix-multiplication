/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.IteratedProduct

set_option autoImplicit false

/-!
# Constant positive-word products are tensor powers

Type extraction naturally represents a nonempty product by a recursively parenthesized
`PositiveWord`.  Asymptotic and paper-facing statements instead use the canonical
`Tensor.power`.  This file proves the coherence theorem between those representations when every
letter selects the same tensor.

The bridge is used in the exceptional `(1,1,2)` construction of
[CoppersmithWinograd1990, pp. 270--272]: after a complete residual group has been retyped
factorwise, its constant positive-word tensor is the canonical power consumed by the established
X/Y-isolation and shared-Z C-tensor pipeline.  The theorem itself is tensor-generic and contains
no Coppersmith--Winograd data.

## Reference

- [CoppersmithWinograd1990] Don Coppersmith and Shmuel Winograd, *Matrix Multiplication via
  Arithmetic Progressions*; see the transcription in `papers/notes/MMult1987.tex:226-285`.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]

namespace Isomorphic

/-- A positive-word tensor whose module and tensor families are constant is canonically
isomorphic to the corresponding positive tensor power.

In human-readable terms, a word of parameter `n` contains `n + 1` letters, so selecting the same
tensor at every letter gives exactly its `(n + 1)`st power; only the parenthesization and canonical
tensor-power coordinates differ.

Proof sketch: first induct on the recursive word to identify the selected product with
`iteratedExternal A T n`.  Then use `power_positive_iteratedExternal` in the reverse direction to
replace that left-associated product by `Tensor.power T (n + 1)`. -/
theorem positiveWordTensor_const_power
    {I : Type w} [Fintype I]
    (A : LegModuleFamily.{u, v} K) (T : Tensor3 K A.Space)
    (n : ℕ) (word : PositiveWord I n) :
    Isomorphic
      (positiveWordTensor (fun _ : I ↦ A) (fun _ : I ↦ T) n word)
      (Tensor.power T (n + 1)) := by
  have hiterated :
      ∀ (m : ℕ) (q : PositiveWord I m),
        Isomorphic
          (positiveWordTensor (fun _ : I ↦ A) (fun _ : I ↦ T) m q)
          (iteratedExternal A T m) := by
    intro m
    induction m with
    | zero =>
        intro q
        exact Isomorphic.refl T
    | succ m ih =>
        intro q
        rcases q with ⟨headWord, last⟩
        change Isomorphic
          (AlgebraicComplexity.Tensor.external
            (positiveWordTensor (fun _ : I ↦ A) (fun _ : I ↦ T) m headWord) T)
          (AlgebraicComplexity.Tensor.external (iteratedExternal A T m) T)
        exact Isomorphic.external (ih headWord) (Isomorphic.refl T)
  exact (hiterated n word).trans
    (power_positive_iteratedExternal A T n).symm

end Isomorphic

end AlgebraicComplexity.Tensor
