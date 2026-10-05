/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.BorderRank
import AlgebraicComplexity.Tensor.BorderRankTransport

/-!
# Transposition laws for matrix-multiplication certificates

`AlgebraicComplexity/MatrixMultiplication.lean` and
`AlgebraicComplexity/MatrixMultiplication/BorderRank.lean` transport rank and border-rank
certificates for `⟨m,n,p⟩` along the *cyclic* symmetry `⟨m,n,p⟩ ↦ ⟨p,m,n⟩`.  The cyclic rotations
reach only three of the six dimension orders.  This module adds the missing generator, the
transposition `⟨m,n,p⟩ ↦ ⟨n,m,p⟩`, at all three certificate levels, and derives the remaining two
odd orders by composition.

The transposition is what a rectangular pipeline needs whenever it must normalize *which* of the
three dimensions is the small one: Coppersmith's 1982 construction (SIAM J. Comput. 11, p. 469)
reverses two legs of its basic tensor, and Huang--Pan's `ω(1, r, 1)` / `ω(1, 1, r)` bookkeeping
(J. Complexity 14 (1998), §8) moves the exponent `r` between the middle and an outer dimension.

## Principal results

* `Tensor.RankLE.matrixMultiplication_swapYZ`,
  `Tensor.BorderRankLE.matrixMultiplication_swapYZ`,
  `Tensor.BorderRankLEAt.matrixMultiplication_swapYZ`: a certificate for `⟨m,n,p⟩` gives one of
  the same size for `⟨n,m,p⟩`, with the leading degree preserved in the degree-aware case;
* `Tensor.BorderRankLEAt.matrixMultiplication_cycle`: the degree-aware form of the cyclic law,
  which `MatrixMultiplication/BorderRank.lean` states only for `BorderRankLE`;
* `matrixMultiplication_reverse` (`⟨m,n,p⟩ ↦ ⟨p,n,m⟩`, the certificate form of
  `(A·B)ᵀ = Bᵀ·Aᵀ`) and `matrixMultiplication_swapXZ` (`⟨m,n,p⟩ ↦ ⟨m,p,n⟩`) at each of the three
  levels: composing the transposition with a rotation reaches the remaining orders, so a
  certificate can be delivered in whichever of the six dimension orders a client wants.

## Layer placement and strategy

Layer 3, a leaf downstream of `MatrixMultiplication/BorderRank.lean` and of
`Tensor/BorderRankTransport.lean`, whose `permute_xzy` laws supply the tensor-level content.  Each
proof mirrors its cyclic sibling exactly: reindex the certificate along the leg transposition
`xzy`, then retype the permuted legs by reversing every matrix-coordinate pair.  That composite is
the canonical isomorphism `mmSwapYZEquiv` of `AlgebraicComplexity/MatrixMultiplication.lean`,
whose verified action on the defining sum is `mmSwapYZEquiv_matrixMultiplication`.

## References

* D. Coppersmith, *Rapid multiplication of rectangular matrices*, SIAM J. Comput. 11 (1982),
  p. 469.
* X. Huang and V. Y. Pan, *Fast rectangular matrix multiplication and applications*,
  J. Complexity 14 (1998), §8.
-/

namespace AlgebraicComplexity

open Tensor

universe u

variable {K : Type u} [CommSemiring K]

/-- The retyped leg transposition applied to a matrix-multiplication tensor transposes its first
two dimensions.  This is `mmSwapYZEquiv_matrixMultiplication` with the ambient equivalence
unfolded into the `Tensor.map`-after-`Tensor.permute` form in which certificate transport laws
consume it. -/
private theorem map_mmSwapYZLegEquiv_permute (m n p : ℕ) :
    Tensor.map (fun c ↦ (mmSwapYZLegEquiv (K := K) m n p c).toLinearMap)
        (Tensor.permute xzy (matrixMultiplication (K := K) m n p)) =
      matrixMultiplication (K := K) n m p := by
  have heq :
      Tensor.map (fun c ↦ (mmSwapYZLegEquiv (K := K) m n p c).toLinearMap)
          (Tensor.permute xzy (matrixMultiplication (K := K) m n p)) =
        mmSwapYZEquiv (K := K) m n p (matrixMultiplication (K := K) m n p) := rfl
  rw [heq, mmSwapYZEquiv_matrixMultiplication]

namespace Tensor.RankLE

/-- **Transposing the first two matrix dimensions preserves every rank certificate**: a rank-`r`
algorithm for `m × n` by `n × p` products gives a rank-`r` algorithm for `n × m` by `m × p`
products. -/
theorem matrixMultiplication_swapYZ {m n p r : ℕ}
    (h : RankLE r (matrixMultiplication (K := K) m n p)) :
    RankLE r (matrixMultiplication (K := K) n m p) := by
  have h' := (h.permute xzy).map
    (fun c ↦ (mmSwapYZLegEquiv (K := K) m n p c).toLinearMap)
  rwa [map_mmSwapYZLegEquiv_permute] at h'

/-- Reversing the dimension triple, `⟨m,n,p⟩ ↦ ⟨p,n,m⟩`: the certificate-level form of the
transpose-product rule `(A·B)ᵀ = Bᵀ·Aᵀ`. -/
theorem matrixMultiplication_reverse {m n p r : ℕ}
    (h : RankLE r (matrixMultiplication (K := K) m n p)) :
    RankLE r (matrixMultiplication (K := K) p n m) :=
  h.matrixMultiplication_swapYZ.matrixMultiplication_cycle

/-- The remaining odd order, `⟨m,n,p⟩ ↦ ⟨m,p,n⟩`. -/
theorem matrixMultiplication_swapXZ {m n p r : ℕ}
    (h : RankLE r (matrixMultiplication (K := K) m n p)) :
    RankLE r (matrixMultiplication (K := K) m p n) :=
  h.matrixMultiplication_cycle.matrixMultiplication_swapYZ

end Tensor.RankLE

namespace Tensor.BorderRankLEAt

/-- **Transposing the first two matrix dimensions preserves every degree-aware border-rank
certificate**, with both the size and the leading degree unchanged. -/
theorem matrixMultiplication_swapYZ {m n p r d : ℕ}
    (h : BorderRankLEAt r d (matrixMultiplication (K := K) m n p)) :
    BorderRankLEAt r d (matrixMultiplication (K := K) n m p) := by
  have h' := h.permute_xzy.map
    (fun c ↦ (mmSwapYZLegEquiv (K := K) m n p c).toLinearMap)
  rwa [map_mmSwapYZLegEquiv_permute] at h'

/-- Cyclically rotating the three roles of a matrix-multiplication tensor preserves every
degree-aware border-rank certificate: a size-`r`, degree-`d` certificate for `⟨m,n,p⟩` gives one
for `⟨p,m,n⟩`.  This is the degree-retaining refinement of
`Tensor.BorderRankLE.matrixMultiplication_cycle`. -/
theorem matrixMultiplication_cycle {m n p r d : ℕ}
    (h : BorderRankLEAt r d (matrixMultiplication (K := K) m n p)) :
    BorderRankLEAt r d (matrixMultiplication (K := K) p m n) := by
  have h' := h.permute_cycle.map
    (fun c ↦ (mmCycleLegEquiv (K := K) m n p c).toLinearMap)
  have heq :
      Tensor.map (fun c ↦ (mmCycleLegEquiv (K := K) m n p c).toLinearMap)
          (Tensor.permute cycle (matrixMultiplication (K := K) m n p)) =
        mmCycleEquiv (K := K) m n p
          (matrixMultiplication (K := K) m n p) := rfl
  rw [heq, mmCycleEquiv_matrixMultiplication] at h'
  exact h'

/-- Reversing the dimension triple at a displayed leading degree, `⟨m,n,p⟩ ↦ ⟨p,n,m⟩`. -/
theorem matrixMultiplication_reverse {m n p r d : ℕ}
    (h : BorderRankLEAt r d (matrixMultiplication (K := K) m n p)) :
    BorderRankLEAt r d (matrixMultiplication (K := K) p n m) :=
  h.matrixMultiplication_swapYZ.matrixMultiplication_cycle

/-- The remaining odd order at a displayed leading degree, `⟨m,n,p⟩ ↦ ⟨m,p,n⟩`. -/
theorem matrixMultiplication_swapXZ {m n p r d : ℕ}
    (h : BorderRankLEAt r d (matrixMultiplication (K := K) m n p)) :
    BorderRankLEAt r d (matrixMultiplication (K := K) m p n) :=
  h.matrixMultiplication_cycle.matrixMultiplication_swapYZ

end Tensor.BorderRankLEAt

namespace Tensor.BorderRankLE

/-- **Transposing the first two matrix dimensions preserves every border-rank certificate**: a
size-`r` approximate algorithm for `m × n` by `n × p` products gives one for `n × m` by `m × p`
products. -/
theorem matrixMultiplication_swapYZ {m n p r : ℕ}
    (h : BorderRankLE r (matrixMultiplication (K := K) m n p)) :
    BorderRankLE r (matrixMultiplication (K := K) n m p) := by
  have h' := h.permute_xzy.map
    (fun c ↦ (mmSwapYZLegEquiv (K := K) m n p c).toLinearMap)
  rwa [map_mmSwapYZLegEquiv_permute] at h'

/-- Reversing the dimension triple at border rank, `⟨m,n,p⟩ ↦ ⟨p,n,m⟩`. -/
theorem matrixMultiplication_reverse {m n p r : ℕ}
    (h : BorderRankLE r (matrixMultiplication (K := K) m n p)) :
    BorderRankLE r (matrixMultiplication (K := K) p n m) :=
  h.matrixMultiplication_swapYZ.matrixMultiplication_cycle

/-- The remaining odd order at border rank, `⟨m,n,p⟩ ↦ ⟨m,p,n⟩`. -/
theorem matrixMultiplication_swapXZ {m n p r : ℕ}
    (h : BorderRankLE r (matrixMultiplication (K := K) m n p)) :
    BorderRankLE r (matrixMultiplication (K := K) m p n) :=
  h.matrixMultiplication_cycle.matrixMultiplication_swapYZ

end Tensor.BorderRankLE

end AlgebraicComplexity
