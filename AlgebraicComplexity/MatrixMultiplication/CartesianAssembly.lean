import AlgebraicComplexity.MatrixMultiplication.DiagonalAssembly
import AlgebraicComplexity.Tensor.IndexedProduct

/-!
# Cartesian assembly of heterogeneous extracted families

Independent recursive constituent stages generally retain different numbers of copies. Tensoring
their indexed direct sums therefore produces the Cartesian product of the stage index sets, not a
diagonal subfamily. This file supplies the dependent-index counterpart of `DiagonalAssembly`:
the output type may vary with the stage, and the resulting copy count is the product of all stage
copy counts.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x

/-- Output choices aligned with a nonempty word of heterogeneous stages. -/
def PositiveStageOutput {Stage : Type w} (Output : Stage → Type x) :
    (r : ℕ) → PositiveWord Stage r → Type x
  | 0, stage => Output stage
  | r + 1, stages => PositiveStageOutput Output r stages.1 × Output stages.2

namespace PositiveStageOutput

variable {Stage : Type w} (Output : Stage → Type x)

/-- Finite heterogeneous stage outputs give a finite Cartesian output type. -/
@[instance_reducible] noncomputable def fintype
    (instances : ∀ stage, Fintype (Output stage)) :
    (r : ℕ) → (stages : PositiveWord Stage r) →
      Fintype (PositiveStageOutput Output r stages)
  | 0, stage => instances stage
  | r + 1, stages =>
      @instFintypeProd
        (PositiveStageOutput Output r stages.1) (Output stages.2)
        (fintype instances r stages.1) (instances stages.2)

@[instance_reducible] noncomputable instance instFintype
    [∀ stage, Fintype (Output stage)]
    (r : ℕ) (stages : PositiveWord Stage r) :
    Fintype (PositiveStageOutput Output r stages) :=
  fintype Output (fun stage ↦ inferInstanceAs (Fintype (Output stage))) r stages

/-- The Cartesian output cardinality is the product of the stage output cardinalities. -/
theorem card [∀ stage, Fintype (Output stage)] :
    ∀ (r : ℕ) (stages : PositiveWord Stage r),
      Fintype.card (PositiveStageOutput Output r stages) =
        positiveWordProduct (fun stage ↦ Fintype.card (Output stage)) r stages
  | 0, stage => rfl
  | r + 1, stages => by
      rcases stages with ⟨init, last⟩
      change
        Fintype.card (PositiveStageOutput Output r init × Output last) =
          positiveWordProduct (fun stage ↦ Fintype.card (Output stage)) r init *
            Fintype.card (Output last)
      rw [Fintype.card_prod, card r init]

end PositiveStageOutput

section TensorAssembly

variable (K : Type u) [CommSemiring K]
variable {Stage : Type w} (Output : Stage → Type x)
variable [∀ stage, Fintype (Output stage)]
variable (W : ∀ stage, Output stage → Leg → Type (max u v))
variable [addW : ∀ stage output c, AddCommMonoid (W stage output c)]
variable [moduleW : ∀ stage output c, Module K (W stage output c)]

/-- Package one stage's output-indexed direct sum. -/
@[reducible] noncomputable def cartesianStageFamily (stage : Stage) :
    LegModuleFamily.{u, max v x} K :=
  indexedDirectSumFamily
    (fun output ↦ LegModuleFamily.of (K := K) (W stage output))

/-- Leg spaces of one Cartesian output, formed recursively in stage order. -/
@[reducible] noncomputable def cartesianComponentFamily :
    (r : ℕ) → (stages : PositiveWord Stage r) →
      PositiveStageOutput Output r stages → LegModuleFamily.{u, v} K
  | 0, stage, output =>
      @LegModuleFamily.of.{u, v} K _ (W stage output)
        (addW stage output) (moduleW stage output)
  | r + 1, stages, output =>
      (cartesianComponentFamily r stages.1 output.1).external
        (@LegModuleFamily.of.{u, v} K _ (W stages.2 output.2)
          (addW stages.2 output.2) (moduleW stages.2 output.2))

/-- Tensor belonging to one Cartesian output choice. -/
noncomputable def cartesianComponentTensor
    (S : ∀ stage output, Tensor3 K (W stage output)) :
    (r : ℕ) → (stages : PositiveWord Stage r) →
      (output : PositiveStageOutput Output r stages) →
        Tensor3 K
          (cartesianComponentFamily (K := K) Output (W := W) r stages output).Space
  | 0, stage, output => S stage output
  | r + 1, stages, output =>
      Tensor.external
        (cartesianComponentTensor S r stages.1 output.1)
        (S stages.2 output.2)

namespace Tensor.Restricts

/-- The external product of two finite matrix-multiplication families is the full Cartesian
family of pairwise products.

This is the binary adapter used after aggregate hashing: each selected factor family may have
dependent leg spaces and nonuniform rectangular dimensions.  No diagonal projection is taken;
every pair of selected outputs survives, and its three dimensions are multiplied exactly. -/
theorem external_indexedDirectSum_matrixMultiplication
    {ι : Type w} [Fintype ι] {κ : Type x} [Fintype κ]
    {V₁ : ι → Leg → Type (max u v)}
    [∀ i c, AddCommMonoid (V₁ i c)] [∀ i c, Module K (V₁ i c)]
    {V₂ : κ → Leg → Type (max u v)}
    [∀ j c, AddCommMonoid (V₂ j c)] [∀ j c, Module K (V₂ j c)]
    (T₁ : ∀ i, Tensor3 K (V₁ i)) (T₂ : ∀ j, Tensor3 K (V₂ j))
    (m₁ n₁ p₁ : ι → ℕ) (m₂ n₂ p₂ : κ → ℕ)
    (h₁ : ∀ i, Restricts (T₁ i)
      (matrixMultiplication (K := K) (m₁ i) (n₁ i) (p₁ i)))
    (h₂ : ∀ j, Restricts (T₂ j)
      (matrixMultiplication (K := K) (m₂ j) (n₂ j) (p₂ j))) :
    Restricts
      (Tensor.external (Tensor.indexedDirectSum T₁) (Tensor.indexedDirectSum T₂))
      (matrixMultiplicationDirectSum K
        (fun q : ι × κ ↦ m₁ q.1 * m₂ q.2)
        (fun q : ι × κ ↦ n₁ q.1 * n₂ q.2)
        (fun q : ι × κ ↦ p₁ q.1 * p₂ q.2)) := by
  exact
    (Tensor.Isomorphic.external_indexedDirectSum T₁ T₂).restricts.trans
      (Restricts.indexedDirectSum fun q ↦
        ((h₁ q.1).external (h₂ q.2)).trans
          (Tensor.Isomorphic.matrixMultiplication_external
            (K := K)
            (m₁ q.1) (n₁ q.1) (p₁ q.1)
            (m₂ q.2) (n₂ q.2) (p₂ q.2)).restricts)

/-- A heterogeneous product of indexed direct sums restricts to the indexed direct sum over the
full Cartesian product of the stage output sets. -/
theorem positiveWord_dependentIndexedDirectSum
    (S : ∀ stage output, Tensor3 K (W stage output)) :
    ∀ (r : ℕ) (stages : PositiveWord Stage r),
      Restricts
        (positiveWordTensor
          (cartesianStageFamily (K := K) Output (W := W))
          (fun stage ↦ Tensor.indexedDirectSum (S stage)) r stages)
        (Tensor.indexedDirectSum
          (cartesianComponentTensor (K := K) Output (W := W) S r stages))
  | 0, stage => Restricts.refl _
  | r + 1, stages => by
      rcases stages with ⟨init, last⟩
      let PairOutput := PositiveStageOutput Output r init × Output last
      letI : Fintype (PositiveStageOutput Output (r + 1) (init, last)) :=
        @instFintypeProd (PositiveStageOutput Output r init) (Output last)
          (PositiveStageOutput.instFintype Output r init) inferInstance
      let pairTensor := fun output : PairOutput ↦
        Tensor.external
          (cartesianComponentTensor (K := K) Output (W := W) S r init output.1)
          (S last output.2)
      have hpair : Restricts
          (Tensor.external
            (positiveWordTensor
              (cartesianStageFamily (K := K) Output (W := W))
              (fun stage ↦ Tensor.indexedDirectSum (S stage)) r init)
            (Tensor.indexedDirectSum (S last)))
          (Tensor.indexedDirectSum pairTensor) :=
        ((positiveWord_dependentIndexedDirectSum S r init).external
          (Restricts.refl (Tensor.indexedDirectSum (S last)))).trans
          (Tensor.Isomorphic.external_indexedDirectSum
            (cartesianComponentTensor (K := K) Output (W := W) S r init)
            (S last)).restricts
      have hreindex : Restricts (Tensor.indexedDirectSum pairTensor)
          (Tensor.indexedDirectSum
            (cartesianComponentTensor (K := K) Output (W := W) S
              (r + 1) (init, last))) := by
        apply Restricts.indexedDirectSum_equiv (Equiv.refl PairOutput)
        intro output
        exact Restricts.refl _
      exact hpair.trans hreindex

/-- Product of a natural-valued statistic along one heterogeneous Cartesian output. -/
def positiveOutputProduct (f : ∀ stage, Output stage → ℕ) :
    ∀ (r : ℕ) (stages : PositiveWord Stage r),
      PositiveStageOutput Output r stages → ℕ
  | 0, stage, output => f stage output
  | r + 1, stages, output =>
      positiveOutputProduct f r stages.1 output.1 * f stages.2 output.2

omit [∀ stage, Fintype (Output stage)] in
/-- Every Cartesian component is a rectangular matrix-multiplication tensor whose dimensions
are the products of the corresponding stage dimensions. -/
theorem cartesianComponentTensor_matrixMultiplication
    (S : ∀ stage output, Tensor3 K (W stage output))
    (m n p : ∀ stage, Output stage → ℕ)
    (hleaf : ∀ stage output,
      Restricts (S stage output)
        (matrixMultiplication (K := K)
          (m stage output) (n stage output) (p stage output))) :
    ∀ (r : ℕ) (stages : PositiveWord Stage r)
      (output : PositiveStageOutput Output r stages),
      Restricts
        (cartesianComponentTensor (K := K) Output (W := W) S r stages output)
        (matrixMultiplication (K := K)
          (positiveOutputProduct Output m r stages output)
          (positiveOutputProduct Output n r stages output)
          (positiveOutputProduct Output p r stages output))
  | 0, stage, output => by
      exact hleaf stage output
  | r + 1, stages, output => by
      exact
        ((cartesianComponentTensor_matrixMultiplication S m n p hleaf
            r stages.1 output.1).external (hleaf stages.2 output.2)).trans
          (Tensor.Isomorphic.matrixMultiplication_external
            (K := K)
            (positiveOutputProduct Output m r stages.1 output.1)
            (positiveOutputProduct Output n r stages.1 output.1)
            (positiveOutputProduct Output p r stages.1 output.1)
            (m stages.2 output.2) (n stages.2 output.2)
            (p stages.2 output.2)).restricts

/-- Cartesian assembly followed by all heterogeneous rectangular leaf restrictions. -/
theorem positiveWord_dependentIndexedDirectSum_matrixMultiplication
    (S : ∀ stage output, Tensor3 K (W stage output))
    (m n p : ∀ stage, Output stage → ℕ)
    (hleaf : ∀ stage output,
      Restricts (S stage output)
        (matrixMultiplication (K := K)
          (m stage output) (n stage output) (p stage output)))
    (r : ℕ) (stages : PositiveWord Stage r) :
    Restricts
      (positiveWordTensor
        (cartesianStageFamily (K := K) Output (W := W))
        (fun stage ↦ Tensor.indexedDirectSum (S stage)) r stages)
      (matrixMultiplicationDirectSum K
        (positiveOutputProduct Output m r stages)
        (positiveOutputProduct Output n r stages)
        (positiveOutputProduct Output p r stages)) :=
  (positiveWord_dependentIndexedDirectSum
      (K := K) Output (W := W) S r stages).trans
    (Restricts.indexedDirectSum fun output ↦
      cartesianComponentTensor_matrixMultiplication
        (K := K) Output (W := W) S m n p hleaf r stages output)

variable {V₀ : Leg → Type v}
variable [∀ c, AddCommMonoid (V₀ c)] [∀ c, Module K (V₀ c)]

/-- Stagewise restrictions of powers of one source assemble into the heterogeneous product of
their indexed output families. -/
theorem power_positiveWord_dependentIndexedDirectSum
    (T : Tensor3 K V₀) (exponent : Stage → ℕ)
    (S : ∀ stage output, Tensor3 K (W stage output))
    (hstage : ∀ stage,
      Restricts (Tensor.power T (exponent stage))
        (Tensor.indexedDirectSum (S stage))) :
    ∀ (r : ℕ) (stages : PositiveWord Stage r),
      Restricts
        (Tensor.power T (positiveWordSum exponent r stages))
        (positiveWordTensor
          (cartesianStageFamily (K := K) Output (W := W))
          (fun stage ↦ Tensor.indexedDirectSum (S stage)) r stages)
  | 0, stage => hstage stage
  | r + 1, stages => by
      change Restricts
        (Tensor.power T
          (positiveWordSum exponent r stages.1 + exponent stages.2))
        (Tensor.external
          (positiveWordTensor
            (cartesianStageFamily (K := K) Output (W := W))
            (fun stage ↦ Tensor.indexedDirectSum (S stage)) r stages.1)
          (Tensor.indexedDirectSum (S stages.2)))
      exact
        (isomorphic_external_power T
          (positiveWordSum exponent r stages.1) (exponent stages.2)).symm.restricts.trans
          ((power_positiveWord_dependentIndexedDirectSum T exponent S hstage
            r stages.1).external (hstage stages.2))

/-- Complete Cartesian assembly from heterogeneous stage extractions out of powers of one
common source tensor. -/
theorem power_positiveWord_dependentIndexedDirectSum_matrixMultiplication
    (T : Tensor3 K V₀) (exponent : Stage → ℕ)
    (S : ∀ stage output, Tensor3 K (W stage output))
    (hstage : ∀ stage,
      Restricts (Tensor.power T (exponent stage))
        (Tensor.indexedDirectSum (S stage)))
    (m n p : ∀ stage, Output stage → ℕ)
    (hleaf : ∀ stage output,
      Restricts (S stage output)
        (matrixMultiplication (K := K)
          (m stage output) (n stage output) (p stage output)))
    (r : ℕ) (stages : PositiveWord Stage r) :
    Restricts
      (Tensor.power T (positiveWordSum exponent r stages))
      (matrixMultiplicationDirectSum K
        (positiveOutputProduct Output m r stages)
        (positiveOutputProduct Output n r stages)
        (positiveOutputProduct Output p r stages)) :=
  (power_positiveWord_dependentIndexedDirectSum
      (K := K) Output (W := W) T exponent S hstage r stages).trans
    (positiveWord_dependentIndexedDirectSum_matrixMultiplication
      (K := K) Output (W := W) S m n p hleaf r stages)

end Tensor.Restricts

namespace Tensor.PolynomialDegenerates

/-- Polynomial-degeneration form of heterogeneous Cartesian matrix-multiplication assembly. -/
theorem positiveWord_dependentIndexedDirectSum_matrixMultiplication
    (S : ∀ stage output, Tensor3 K (W stage output))
    (m n p : ∀ stage, Output stage → ℕ)
    (hleaf : ∀ stage output,
      Restricts (S stage output)
        (matrixMultiplication (K := K)
          (m stage output) (n stage output) (p stage output)))
    (r : ℕ) (stages : PositiveWord Stage r) :
    PolynomialDegenerates
      (positiveWordTensor
        (cartesianStageFamily (K := K) Output (W := W))
        (fun stage ↦ Tensor.indexedDirectSum (S stage)) r stages)
      (matrixMultiplicationDirectSum K
        (Tensor.Restricts.positiveOutputProduct Output m r stages)
        (Tensor.Restricts.positiveOutputProduct Output n r stages)
        (Tensor.Restricts.positiveOutputProduct Output p r stages)) :=
  PolynomialDegenerates.of_restricts
    (Tensor.Restricts.positiveWord_dependentIndexedDirectSum_matrixMultiplication
      (K := K) Output (W := W) S m n p hleaf r stages)

variable {V₀ : Leg → Type v}
variable [∀ c, AddCommMonoid (V₀ c)] [∀ c, Module K (V₀ c)]

/-- Polynomial-degeneration form of complete heterogeneous Cartesian assembly from powers of
one common source tensor. -/
theorem power_positiveWord_dependentIndexedDirectSum_matrixMultiplication
    (T : Tensor3 K V₀) (exponent : Stage → ℕ)
    (S : ∀ stage output, Tensor3 K (W stage output))
    (hstage : ∀ stage,
      Restricts (Tensor.power T (exponent stage))
        (Tensor.indexedDirectSum (S stage)))
    (m n p : ∀ stage, Output stage → ℕ)
    (hleaf : ∀ stage output,
      Restricts (S stage output)
        (matrixMultiplication (K := K)
          (m stage output) (n stage output) (p stage output)))
    (r : ℕ) (stages : PositiveWord Stage r) :
    PolynomialDegenerates
      (Tensor.power T (positiveWordSum exponent r stages))
      (matrixMultiplicationDirectSum K
        (Tensor.Restricts.positiveOutputProduct Output m r stages)
        (Tensor.Restricts.positiveOutputProduct Output n r stages)
        (Tensor.Restricts.positiveOutputProduct Output p r stages)) :=
  PolynomialDegenerates.of_restricts
    (Tensor.Restricts.power_positiveWord_dependentIndexedDirectSum_matrixMultiplication
      (K := K) Output (W := W) T exponent S hstage m n p hleaf r stages)

end Tensor.PolynomialDegenerates

end TensorAssembly

end AlgebraicComplexity
