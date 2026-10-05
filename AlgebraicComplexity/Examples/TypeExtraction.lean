/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.TypeExtraction

/-!
# Tiny regression test for multinomial type extraction

The mixed type in the square of `⟨2,1,1⟩ ⊕ ⟨3,1,1⟩` contains the two words `01` and `10`.
Both words are `⟨6,1,1⟩`, so the type-extraction theorem must produce exactly two independent
copies.  This small example detects reversed restriction arrows, lost cross terms, and incorrect
word-product ordering.
-/

namespace AlgebraicComplexity.Examples.TypeExtraction

open AlgebraicComplexity Tensor
open scoped BigOperators Matrix

abbrev TinyIndex := Fin 2

def tinyM : TinyIndex → ℕ := ![2, 3]
def tinyOne : TinyIndex → ℕ := ![1, 1]
def tinyMixedType : TinyIndex → ℕ := ![1, 1]

theorem tinyMixedType_mem :
    tinyMixedType ∈ WordType.types TinyIndex 2 := by
  rw [WordType.mem_types]
  decide

theorem tinyMixedType_card :
    Fintype.card (Tensor.positiveTypeClass TinyIndex 1 tinyMixedType) = 2 := by
  rw [fintypeCard_positiveTypeClass_eq_multinomial 1 tinyMixedType tinyMixedType_mem]
  decide

theorem tinyM_product : (∏ i, tinyM i ^ tinyMixedType i) = 6 := by
  decide

theorem tinyOne_product : (∏ i, tinyOne i ^ tinyMixedType i) = 1 := by
  decide

universe u

variable (K : Type u) [CommSemiring K]

/-- The mixed type of the two-fold product gives two independent copies of `⟨6,1,1⟩`. -/
theorem tiny_mixed_type_extraction :
    Restricts
      (Tensor.iteratedExternal
        (Tensor.indexedDirectSumFamily
          (matrixMultiplicationFamily (K := K) tinyM tinyOne tinyOne))
        (Tensor.indexedDirectSum
          (matrixMultiplicationTensorFamily (K := K) tinyM tinyOne tinyOne)) 1)
      (Tensor.indexedDirectSum
        (fun _q : Tensor.positiveTypeClass TinyIndex 1 tinyMixedType ↦
          matrixMultiplication (K := K)
            (∏ i, tinyM i ^ tinyMixedType i)
            (∏ i, tinyOne i ^ tinyMixedType i)
            (∏ i, tinyOne i ^ tinyMixedType i))) :=
  Tensor.Restricts.iteratedExternal_matrixMultiplicationDirectSum_type
    (K := K) tinyM tinyOne tinyOne 1 tinyMixedType

end AlgebraicComplexity.Examples.TypeExtraction
