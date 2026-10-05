import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeaf
import AlgebraicComplexity.Probability.ReindexBasic

/-!
# Reindexing rational typed leaves

Entropy calculations are often easiest on a Cartesian source alphabet, whereas the tensor-facing
hashing theorem is indexed by the subtype of addresses in an actual partition support.  These
alphabets are normally equivalent but not definitionally equal.  This file transports positive
integral profiles and rational typed leaves across an arbitrary source equivalence.

Reindexing changes no semantic data: the normalized law is relabelled by the equivalence, each
coordinate marginal is unchanged, and every exact dimension product is preserved.  Keeping this
operation generic prevents tensor clients from reproducing dependent-subtype transport proofs.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w

namespace PositiveIntegralProfile

variable {I : Type u} {J : Type v} [Fintype I] [Nonempty I]
variable [Fintype J] [Nonempty J]

/-- Relabel a positive integral profile along an equivalence of finite alphabets. -/
noncomputable def reindex (profile : PositiveIntegralProfile I) (e : I ≃ J) :
    PositiveIntegralProfile J where
  alphabet := Finset.univ
  complete := by simp
  count j := profile.count (e.symm j)
  count_pos j := profile.count_pos (e.symm j)

/-- Reindexing preserves the exact integral mass.

Proof sketch: the new count sum is the old count sum composed with `e.symm`; finite sums are
invariant under an equivalence. -/
@[simp] theorem mass_reindex (profile : PositiveIntegralProfile I) (e : I ≃ J) :
    (profile.reindex e).mass = profile.mass := by
  unfold reindex mass WordType.profileMass
  exact e.symm.sum_comp profile.count

/-- Normalization commutes with reindexing an integral profile. -/
theorem probability_reindex (profile : PositiveIntegralProfile I) (e : I ≃ J) :
    (profile.reindex e).probability = profile.probability.reindex e := by
  apply ProbabilityVector.ext
  funext j
  rw [probability_weight, ProbabilityVector.reindex_weight, probability_weight,
    mass_reindex]
  rfl

end PositiveIntegralProfile

namespace RationalTypedLeaf

variable {I : Type u} {J : Type v} [Fintype I] [Nonempty I]
variable [Fintype J] [Nonempty J]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

/-- Transport a rational typed leaf to an equivalent finite source alphabet. -/
noncomputable def reindex (leaf : RationalTypedLeaf I A) (e : I ≃ J) :
    RationalTypedLeaf J A where
  profile := leaf.profile.reindex e
  coordinate c j := leaf.coordinate c (e.symm j)
  dimension j c := leaf.dimension (e.symm j) c
  dimension_pos j c := leaf.dimension_pos (e.symm j) c

/-- The distribution of a reindexed leaf is the reindexed original distribution. -/
theorem distribution_reindex (leaf : RationalTypedLeaf I A) (e : I ≃ J) :
    (leaf.reindex e).distribution = leaf.distribution.reindex e := by
  exact leaf.profile.probability_reindex e

/-- A coordinate marginal is invariant under source reindexing.

Proof sketch: pushing the relabelled law through the coordinate composed with `e.symm` cancels the
source equivalence. -/
theorem marginal_reindex (leaf : RationalTypedLeaf I A) (e : I ≃ J) (c : Leg) :
    (leaf.reindex e).marginal c = leaf.marginal c := by
  unfold marginal
  rw [distribution_reindex, ProbabilityVector.pushforward_reindex]
  congr 1
  funext i
  change leaf.coordinate c (e.symm (e i)) = leaf.coordinate c i
  simp

/-- Marginal entropy is invariant under source reindexing. -/
@[simp] theorem marginalEntropyBits_reindex
    (leaf : RationalTypedLeaf I A) (e : I ≃ J) (c : Leg) :
    (leaf.reindex e).marginalEntropyBits c = leaf.marginalEntropyBits c := by
  unfold marginalEntropyBits
  rw [marginal_reindex]

/-- Maximum entropy in the three-coordinate fiber is invariant under source relabelling.

Proof sketch: pull a competing law back along the inverse equivalence.  Its three old-coordinate
marginals agree with the old reference law because the transported coordinates commute with
reindexing.  Apply old maximality and use entropy invariance under source equivalence. -/
theorem IsMaximumEntropyBits.reindex
    {leaf : RationalTypedLeaf I A}
    (hmaximum : leaf.IsMaximumEntropyBits leaf.distribution) (e : I ≃ J) :
    (leaf.reindex e).IsMaximumEntropyBits (leaf.reindex e).distribution := by
  intro competitor hcompetitor
  have holdMarginals : leaf.SameMarginals leaf.distribution
      (competitor.reindex e.symm) := by
    intro c
    calc
      leaf.distribution.pushforward (leaf.coordinate c) =
          (leaf.reindex e).distribution.pushforward
            ((leaf.reindex e).coordinate c) := by
        exact (leaf.marginal_reindex e c).symm
      _ = competitor.pushforward ((leaf.reindex e).coordinate c) :=
        hcompetitor c
      _ = (competitor.reindex e.symm).pushforward (leaf.coordinate c) := by
        rw [ProbabilityVector.pushforward_reindex]
        congr 1
  have hentropy := hmaximum (competitor.reindex e.symm) holdMarginals
  rw [ProbabilityVector.entropyBits_reindex] at hentropy
  calc
    competitor.entropyBits ≤ leaf.distribution.entropyBits := hentropy
    _ = (leaf.reindex e).distribution.entropyBits := by
      rw [distribution_reindex, ProbabilityVector.entropyBits_reindex]

/-- Exact matrix-dimension products are invariant under source reindexing.

Proof sketch: after replacing each stored alphabet by `univ`, the new product is the old product
composed with `e.symm`, and finite products are invariant under an equivalence. -/
@[simp] theorem dimensionProduct_reindex
    (leaf : RationalTypedLeaf I A) (e : I ≃ J) (c : Leg) :
    (leaf.reindex e).dimensionProduct c = leaf.dimensionProduct c := by
  classical
  unfold dimensionProduct reindex PositiveIntegralProfile.reindex
  rw [leaf.profile.alphabet_eq_univ]
  exact e.symm.prod_comp
    (fun i ↦ leaf.dimension i c ^ leaf.profile.count i)

end RationalTypedLeaf

end AlgebraicComplexity
