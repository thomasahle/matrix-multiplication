import AlgebraicComplexity.Analysis.MaximumEntropyProduct
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafProduct

/-!
# Cyclic products of rational typed leaves

Tensor value arguments multiply a typed tensor by its two cyclic leg orientations before
extracting blocks.  This file supplies the corresponding paper-independent operation on rational
typed leaves.  The new letter alphabet is a triple of source letters; its integral profile is the
independent product profile, each visible coordinate contains one interface of each orientation,
and each matrix dimension is the product of the three rotated primitive dimensions.

The principal theorem proves that maximum entropy tensorizes through this construction.  Thus a
client such as the exceptional Coppersmith--Winograd `112` constituent can work on its primitive
four-letter law and obtain the 64-letter symmetric maximum-entropy theorem without enumerating
the product support.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v

/-- Left-associated triple alphabet used by the three-orientation product. -/
abbrev CyclicTriple (I : Type u) := (I × I) × I

/-- Visible compound alphabet on one leg of a cyclic typed-leaf product. -/
abbrev CyclicTypedLeafCoordinate (A : Leg → Type v) (c : Leg) :=
  (A c × A (cycle.symm c)) × A (cycle c)

namespace PositiveIntegralProfile

variable {I : Type u} [Fintype I] [Nonempty I]

/-- Independent product profile on three copies of a positive integral profile. -/
def cyclicProduct (profile : PositiveIntegralProfile I) :
    PositiveIntegralProfile (CyclicTriple I) where
  alphabet := Finset.univ
  complete := by simp
  count source :=
    profile.count source.1.1 * profile.count source.1.2 * profile.count source.2
  count_pos source := mul_pos (mul_pos
    (profile.count_pos source.1.1) (profile.count_pos source.1.2))
      (profile.count_pos source.2)

/-- The independent triple profile has the cube of the primitive mass.

Proof sketch: expand the sum over the product alphabet and distribute each independent factor.
Every one-letter sum is the primitive profile mass. -/
@[simp] theorem mass_cyclicProduct (profile : PositiveIntegralProfile I) :
    profile.cyclicProduct.mass = profile.mass ^ 3 := by
  classical
  unfold cyclicProduct mass WordType.profileMass
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  calc
    (∑ i, ∑ j, ∑ k, profile.count i * profile.count j * profile.count k) =
        ∑ i, ∑ j, (profile.count i * profile.count j) *
          (∑ k, profile.count k) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.mul_sum]
    _ = ∑ i, profile.count i * (∑ j, profile.count j) *
          (∑ k, profile.count k) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_mul]
      congr 1
      rw [← Finset.mul_sum]
    _ = (∑ i, profile.count i) * (∑ j, profile.count j) *
          (∑ k, profile.count k) := by
      rw [← Finset.sum_mul]
      congr 1
      rw [← Finset.sum_mul]
    _ = (∑ i, profile.count i) ^ 3 := by ring

end PositiveIntegralProfile

namespace RationalTypedLeaf

variable {I : Type u} [Fintype I] [Nonempty I] [DecidableEq I]
variable {A : Leg → Type v} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

/-- Product of a rational typed leaf with its two cyclic orientations. -/
def cyclicProduct (leaf : RationalTypedLeaf I A) :
    RationalTypedLeaf (CyclicTriple I) (CyclicTypedLeafCoordinate A) where
  profile := leaf.profile.cyclicProduct
  coordinate c source :=
    ((leaf.coordinate c source.1.1,
      leaf.coordinate (cycle.symm c) source.1.2),
      leaf.coordinate (cycle c) source.2)
  dimension source c :=
    leaf.dimension source.1.1 c *
      leaf.dimension source.1.2 (cycle.symm c) *
      leaf.dimension source.2 (cycle c)
  dimension_pos source c := mul_pos (mul_pos
    (leaf.dimension_pos source.1.1 c)
    (leaf.dimension_pos source.1.2 (cycle.symm c)))
    (leaf.dimension_pos source.2 (cycle c))

/-! The named cyclic operation is the iterated generic product.  Keeping this theorem explicit
means downstream clients can switch between the readable cyclic notation and the compositional
`product`/`permute` API without reproving any counting facts. -/

theorem cyclicProduct_eq_product (leaf : RationalTypedLeaf I A) :
    leaf.cyclicProduct =
      (leaf.product (leaf.permute cycle)).product (leaf.permute cycle.symm) := by
  rfl

/-- Exact dimension product of a cyclic typed leaf.

Each primitive dimension product occurs once in each orientation.  The other two independent
source coordinates contribute the square of the primitive profile mass to every exponent. -/
theorem cyclicProduct_dimensionProduct (leaf : RationalTypedLeaf I A) (c : Leg) :
    leaf.cyclicProduct.dimensionProduct c =
      (leaf.dimensionProduct c *
        leaf.dimensionProduct (cycle.symm c) *
        leaf.dimensionProduct (cycle c)) ^ (leaf.profile.mass ^ 2) := by
  classical
  rw [cyclicProduct_eq_product, product_dimensionProduct,
    product_dimensionProduct]
  simp only [permute_dimensionProduct, permute_profile, product_profile,
    PositiveIntegralProfile.mass_product, Equiv.symm_symm_apply]
  rw [mul_pow]
  simp only [pow_mul]
  ring

/-- The normalized cyclic product profile is the independent product of three primitive laws.

Proof sketch: at a triple, both sides have numerator `aᵢ aⱼ aₖ`; the profile-mass theorem
identifies the denominator with the cube of the primitive mass. -/
theorem cyclicProduct_distribution (leaf : RationalTypedLeaf I A) :
    leaf.cyclicProduct.distribution =
      (leaf.distribution.product leaf.distribution).product leaf.distribution := by
  rw [cyclicProduct_eq_product, product_distribution, product_distribution,
    permute_distribution, permute_distribution]

/-- The cyclic product coordinate is the nested generic product coordinate of the three rotated
primitive coordinate systems. -/
theorem cyclicProduct_coordinate_eq_productCoordinate (leaf : RationalTypedLeaf I A) :
    leaf.cyclicProduct.coordinate =
      WordType.productCoordinate
        (WordType.productCoordinate leaf.coordinate
          (fun c ↦ leaf.coordinate (cycle.symm c)))
        (fun c ↦ leaf.coordinate (cycle c)) := by
  rfl

/-- Maximum entropy in the primitive three-marginal fiber is preserved by cyclic product.

Proof sketch: cyclically reordering the three constraints preserves the primitive maximum.  Apply
the generic independent-product maximum-entropy theorem twice.  Finally identify the product law
with the normalized cyclic integral profile. -/
theorem IsMaximumEntropyBits.cyclicProduct
    {leaf : RationalTypedLeaf I A}
    (hmaximum : leaf.IsMaximumEntropyBits leaf.distribution) :
    leaf.cyclicProduct.IsMaximumEntropyBits leaf.cyclicProduct.distribution := by
  have hbase := hmaximum.isMaximumEntropyInMappedFiber
  have hcycleLeaf := hmaximum.permute cycle
  have hcycleInvLeaf := hmaximum.permute cycle.symm
  have hcycle := hcycleLeaf.isMaximumEntropyInMappedFiber
  have hcycleInv := hcycleInvLeaf.isMaximumEntropyInMappedFiber
  have hproduct := WordType.IsMaximumEntropyInMappedFiber.product
    leaf.coordinate (fun c ↦ leaf.coordinate (cycle.symm c))
    leaf.distribution leaf.distribution hbase hcycle
  have htriple := WordType.IsMaximumEntropyInMappedFiber.product
    (WordType.productCoordinate leaf.coordinate
      (fun c ↦ leaf.coordinate (cycle.symm c)))
    (fun c ↦ leaf.coordinate (cycle c))
    (leaf.distribution.product leaf.distribution) leaf.distribution hproduct hcycleInv
  intro competitor hcompetitor
  have hfiber : ∀ c,
      competitor.pushforward (leaf.cyclicProduct.coordinate c) =
        ((leaf.distribution.product leaf.distribution).product
          leaf.distribution).pushforward (leaf.cyclicProduct.coordinate c) := by
    intro c
    rw [← leaf.cyclicProduct_distribution]
    exact (hcompetitor c).symm
  have hentropy := htriple competitor (by
    rw [← cyclicProduct_coordinate_eq_productCoordinate]
    exact hfiber)
  rw [← leaf.cyclicProduct_distribution] at hentropy
  unfold ProbabilityVector.entropyBits
  exact (div_le_div_iff_of_pos_right (Real.log_pos (by norm_num))).2 hentropy

end RationalTypedLeaf

end AlgebraicComplexity
