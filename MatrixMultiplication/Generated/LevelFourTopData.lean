import MatrixMultiplication.Generated.LevelFourTopSemantic0
import MatrixMultiplication.Generated.LevelFourTopSemantic1
import MatrixMultiplication.Generated.LevelFourTopSemantic2
import MatrixMultiplication.Generated.LevelFourTopSemantic3
import MatrixMultiplication.Generated.LevelFourTopSemantic4
import MatrixMultiplication.Generated.LevelFourTopSemantic5

/-!
# Generated exact top-mass certificate

Source SHA-256: `7a255f50ab903cb7f3da56d93ceccfff3acf39061463115655d7f3f63e746481`.

The arrays are emitted from the archived `2^32`-denominator certificate.  Generated checking
modules use Lean's kernel with `decide`; no floating-point values are imported.
The six root checks are separate modules so Lake can check them independently and retain only
small proof batches in memory.
-/

namespace MatrixMultiplication.LevelFourRemainingReconstruction.Generated.Top

open AlgebraicComplexity.LevelFourReconstruction.PositiveLevelThreeData

set_option maxRecDepth 100000
set_option Elab.async false

private abbrev r0 : Fin regionCount := ⟨0, by norm_num [regionCount]⟩
private abbrev r1 : Fin regionCount := ⟨1, by norm_num [regionCount]⟩
private abbrev r2 : Fin regionCount := ⟨2, by norm_num [regionCount]⟩
private abbrev r3 : Fin regionCount := ⟨3, by norm_num [regionCount]⟩
private abbrev r4 : Fin regionCount := ⟨4, by norm_num [regionCount]⟩
private abbrev r5 : Fin regionCount := ⟨5, by norm_num [regionCount]⟩

private theorem zeroTotal :
    (∑ root : Fin regionCount, certificate.zeroRowTotal root) = 5906007 := by
  refine (sum_regions_six fun root => certificate.zeroRowTotal root).trans ?_
  have h0 : certificate.zeroRowTotal ⟨0, by decide⟩ = 1686 := zeroRowTotal_0
  have h1 : certificate.zeroRowTotal ⟨1, by decide⟩ = 5900058 := zeroRowTotal_1
  have h2 : certificate.zeroRowTotal ⟨2, by decide⟩ = 375 := zeroRowTotal_2
  have h3 : certificate.zeroRowTotal ⟨3, by decide⟩ = 368 := zeroRowTotal_3
  have h4 : certificate.zeroRowTotal ⟨4, by decide⟩ = 2469 := zeroRowTotal_4
  have h5 : certificate.zeroRowTotal ⟨5, by decide⟩ = 1051 := zeroRowTotal_5
  omega

private theorem branchTotal :
    (∑ root : Fin regionCount, ∑ region,
      certificate.branchRowTotal root region) = 4289061289 := by
  refine (sum_regions_six fun root => ∑ region,
    certificate.branchRowTotal root region).trans ?_
  have h0 : (∑ region, certificate.branchRowTotal ⟨0, by decide⟩ region) =
      2277285 := branchRootTotal_0
  have h1 : (∑ region, certificate.branchRowTotal ⟨1, by decide⟩ region) =
      4281758036 := branchRootTotal_1
  have h2 : (∑ region, certificate.branchRowTotal ⟨2, by decide⟩ region) =
      95321 := branchRootTotal_2
  have h3 : (∑ region, certificate.branchRowTotal ⟨3, by decide⟩ region) =
      94631 := branchRootTotal_3
  have h4 : (∑ region, certificate.branchRowTotal ⟨4, by decide⟩ region) =
      3434892 := branchRootTotal_4
  have h5 : (∑ region, certificate.branchRowTotal ⟨5, by decide⟩ region) =
      1401124 := branchRootTotal_5
  omega

/-- Kernel-checked global `2^32` normalization, assembled from independent root checks. -/
private theorem certificate_totalNumerator :
    certificate.totalNumerator = AlgebraicComplexity.dyadicDenominator bits := by
  calc
    certificate.totalNumerator =
        (∑ root, certificate.zeroRowTotal root) +
          ∑ root, ∑ region, certificate.branchRowTotal root region :=
      TopMassArrays.totalNumerator_eq_rowTotals certificate
    _ = 5906007 + 4289061289 := congrArg₂ Nat.add zeroTotal branchTotal
    _ = AlgebraicComplexity.dyadicDenominator bits := by
      norm_num [AlgebraicComplexity.dyadicDenominator, bits]

/-- Kernel-checked global normalization of the joint top mass. -/
theorem certificate_isValid : certificate.IsValid :=
  certificate_totalNumerator

/-- Exact rational top distribution. -/
noncomputable def probability := certificate.toRational

theorem probability_isProbability : probability.IsProbability :=
  TopMassArrays.toRational_isProbability certificate_isValid

end MatrixMultiplication.LevelFourRemainingReconstruction.Generated.Top
