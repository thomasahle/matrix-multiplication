/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.TypeExtraction
import AlgebraicComplexity.Tensor.PartitionedPower

/-!
# Matrix-multiplication constituents in partitioned tensor powers

This module connects two reusable interfaces: typed constituents of a partitioned tensor and
word products of rectangular matrix-multiplication tensors.  A client that gives an exact
restriction certificate for every base constituent automatically gets the corresponding
restriction for every supported constituent word in every positive partitioned power.

The result is deliberately independent of Coppersmith--Winograd tensors and of hashing.  A
hashing client can first extract a legwise-independent family of word constituents and then use
the theorem here componentwise.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

namespace Tensor.Restricts

/-- Iterating exact constituent restrictions along a supported address word produces the
external product of the corresponding matrix-multiplication tensors, canonically reindexed as
one rectangular matrix-multiplication tensor. -/
theorem positiveSupportWordTensor_matrixMultiplication
    (P : PartitionedTensor (K := K) (A := A) V)
    (m n p : P.support → ℕ)
    (hconstituent : ∀ s : P.support,
      Restricts (P.constituent s.1)
        (matrixMultiplication (K := K) (m s) (n s) (p s)))
    (r : ℕ) (q : PositiveWord P.support r) :
    Restricts (P.positiveSupportWordTensor r q)
      (matrixMultiplication (K := K)
        (positiveWordProduct m r q)
        (positiveWordProduct n r q)
        (positiveWordProduct p r q)) := by
  induction r with
  | zero =>
      exact hconstituent q
  | succ r ih =>
      exact
        ((ih q.1).external (hconstituent q.2)).trans
          (Tensor.Isomorphic.matrixMultiplication_external
            (K := K)
            (positiveWordProduct m r q.1)
            (positiveWordProduct n r q.1)
            (positiveWordProduct p r q.1)
            (m q.2) (n q.2) (p q.2)).restricts

/-- Constituent-level form of
`positiveSupportWordTensor_matrixMultiplication`, stated directly for the canonical partitioned
positive power. -/
theorem positivePower_constituent_matrixMultiplication
    (P : PartitionedTensor (K := K) (A := A) V)
    (m n p : P.support → ℕ)
    (hconstituent : ∀ s : P.support,
      Restricts (P.constituent s.1)
        (matrixMultiplication (K := K) (m s) (n s) (p s)))
    (r : ℕ) (q : PositiveWord P.support r) :
    Restricts
      ((P.positivePower r).constituent
        (positiveSupportWordBlockAddress P.support r q))
      (matrixMultiplication (K := K)
        (positiveWordProduct m r q)
        (positiveWordProduct n r q)
        (positiveWordProduct p r q)) := by
  rw [P.positivePower_constituent_positiveSupportWordBlockAddress r q]
  exact positiveSupportWordTensor_matrixMultiplication
    P m n p hconstituent r q

end Tensor.Restricts

namespace Tensor.PolynomialDegenerates

/-- Iterating polynomial constituent degenerations along a supported address word produces a
polynomial degeneration to the external product of the corresponding matrix-multiplication
tensors, canonically reindexed as one rectangular matrix-multiplication tensor.

This is the degeneration-parametric companion of
`Tensor.Restricts.positiveSupportWordTensor_matrixMultiplication`.  Keeping the two statements
parallel is intentional: a client may choose exact restriction, zeroing followed by restriction,
or a genuinely polynomial constituent certificate without changing the typed-word/counting API.
-/
theorem positiveSupportWordTensor_matrixMultiplication
    (P : PartitionedTensor (K := K) (A := A) V)
    (m n p : P.support → ℕ)
    (hconstituent : ∀ s : P.support,
      PolynomialDegenerates (P.constituent s.1)
        (matrixMultiplication (K := K) (m s) (n s) (p s)))
    (r : ℕ) (q : PositiveWord P.support r) :
    PolynomialDegenerates (P.positiveSupportWordTensor r q)
      (matrixMultiplication (K := K)
        (positiveWordProduct m r q)
        (positiveWordProduct n r q)
        (positiveWordProduct p r q)) := by
  induction r with
  | zero =>
      exact hconstituent ⟨q.1, q.2⟩
  | succ r ih =>
      exact
        ((ih q.1).external (hconstituent q.2)).trans
          (PolynomialDegenerates.of_restricts
            (Tensor.Isomorphic.matrixMultiplication_external
              (K := K)
              (positiveWordProduct m r q.1)
              (positiveWordProduct n r q.1)
              (positiveWordProduct p r q.1)
              (m q.2) (n q.2) (p q.2)).restricts)

/-- Constituent-level form of
`positiveSupportWordTensor_matrixMultiplication`, stated directly for the canonical partitioned
positive power. -/
theorem positivePower_constituent_matrixMultiplication
    (P : PartitionedTensor (K := K) (A := A) V)
    (m n p : P.support → ℕ)
    (hconstituent : ∀ s : P.support,
      PolynomialDegenerates (P.constituent s.1)
        (matrixMultiplication (K := K) (m s) (n s) (p s)))
    (r : ℕ) (q : PositiveWord P.support r) :
    PolynomialDegenerates
      ((P.positivePower r).constituent
        (positiveSupportWordBlockAddress P.support r q))
      (matrixMultiplication (K := K)
        (positiveWordProduct m r q)
        (positiveWordProduct n r q)
        (positiveWordProduct p r q)) := by
  rw [P.positivePower_constituent_positiveSupportWordBlockAddress r q]
  exact positiveSupportWordTensor_matrixMultiplication
    P m n p hconstituent r q

end Tensor.PolynomialDegenerates

end AlgebraicComplexity
