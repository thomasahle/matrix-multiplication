import MatrixMultiplication.SignedDyadicLogCanonicalDefs
import MatrixMultiplication.SignedDyadicLogForm
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FieldSimp

/-!
# Canonical signed dyadic logarithm forms

The logarithms of `0` and `1` vanish under Lean's real-log convention.  Generated certificate
exporters naturally omit those terms, while the purely syntactic normalizer in
`SignedDyadicLogForm` retains them.  `SignedDyadicLogCanonicalDefs` supplies the executable
canonicalizers used at that adapter boundary.  This module proves that they preserve the
represented real value: first combine equal logarithm arguments, then remove the trivial
arguments.

Certificate exporters also commonly replace `log₂ (2^k * m)` by `k + log₂ m`.  The
power-normalization API near the end of this module proves that this second, executable
canonicalization preserves the represented real value.
-/

namespace MatrixMultiplication.SignedDyadicLogForm.Form

open MatrixMultiplication.SignedDyadicLogForm

noncomputable section

/-! ## Structurally recursive merge normalization

`List.merge` is efficient when evaluated normally, but its well-founded recursor can leave
`Eq.rec` terms that block kernel reduction inside `decide`.  The following merge consumes an
explicit fuel argument instead.  Its public wrapper supplies the sum of the input lengths, so it
performs the same complete merge while remaining structurally recursive. -/

theorem termsValue_mergeRuns (bits : ℕ) (left right : List Term) :
    termsValue bits (mergeRuns left right) =
      termsValue bits left + termsValue bits right := by
  unfold mergeRuns termsValue
  have hperm :=
    (List.merge_perm_append termLE (xs := left) (ys := right)).map (termValue bits)
  rw [hperm.sum_eq, List.map_append, List.sum_append]

/-- Sum of the logarithmic values stored in a binary-counter run family. -/
def runsValue (bits : ℕ) : List (Option (List Term)) → ℝ
  | [] => 0
  | none :: runs => runsValue bits runs
  | some run :: runs => termsValue bits run + runsValue bits runs

theorem runsValue_insertRun (bits : ℕ) (run : List Term)
    (runs : List (Option (List Term))) :
    runsValue bits (insertRun run runs) =
      termsValue bits run + runsValue bits runs := by
  induction runs generalizing run with
  | nil => simp [runsValue]
  | cons stored runs ih =>
      cases stored with
      | none => simp [runsValue]
      | some stored =>
          simp only [runsValue]
          rw [ih, termsValue_mergeRuns]
          ring

theorem runsValue_buildRuns (bits : ℕ) (terms : List Term) :
    runsValue bits (buildRuns terms) = termsValue bits terms := by
  have haux (runs : List (Option (List Term))) :
      runsValue bits
          (terms.foldl (fun runs term ↦ insertRun [term] runs) runs) =
        termsValue bits terms + runsValue bits runs := by
    induction terms generalizing runs with
    | nil => simp [termsValue]
    | cons term terms ih =>
        simp only [List.foldl_cons]
        rw [ih, runsValue_insertRun]
        simp [termsValue]
        ring
  rw [buildRuns, haux]
  simp [runsValue]

theorem termsValue_collapseRuns (bits : ℕ)
    (runs : List (Option (List Term))) :
    termsValue bits (collapseRuns runs) = runsValue bits runs := by
  induction runs with
  | nil => simp [collapseRuns, runsValue, termsValue]
  | cons run runs ih =>
      cases run with
      | none => simpa [collapseRuns, runsValue] using ih
      | some run =>
          simp only [collapseRuns, runsValue, termsValue_mergeRuns, ih]

theorem termsValue_bottomUpSort (bits : ℕ) (terms : List Term) :
    termsValue bits (bottomUpSort terms) = termsValue bits terms := by
  rw [bottomUpSort, termsValue_collapseRuns, runsValue_buildRuns]

theorem termsValue_fastNormalizeTerms (bits : ℕ) (terms : List Term) :
    termsValue bits (fastNormalizeTerms terms) = termsValue bits terms := by
  rw [fastNormalizeTerms, termsValue_normalizeTerms, termsValue_bottomUpSort]

theorem eval_fastNormalize (bits : ℕ) (form : Form) :
    eval bits (fastNormalize form) = eval bits form := by
  simp [eval, termsValue_fastNormalizeTerms]

theorem termsValue_filter_nontrivial (bits : ℕ) (terms : List Term) :
    termsValue bits (terms.filter fun term ↦ 1 < term.argument) =
      termsValue bits terms := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      rcases term with ⟨argument, coefficient⟩
      by_cases hnontrivial : 1 < argument
      · have hadd := congrArg
          (fun value ↦ termValue bits ⟨argument, coefficient⟩ + value) ih
        simpa [hnontrivial, termsValue] using hadd
      · have hcases : argument = 0 ∨ argument = 1 :=
          Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_not_gt hnontrivial)
        have hterm : termValue bits ⟨argument, coefficient⟩ = 0 := by
          rcases hcases with rfl | rfl <;> simp [termValue, log2Nat]
        calc
          termsValue bits
              ((⟨argument, coefficient⟩ :: terms).filter
                fun term ↦ 1 < term.argument) =
              termsValue bits (terms.filter fun term ↦ 1 < term.argument) := by
                simp [hnontrivial]
          _ = termsValue bits terms := ih
          _ = termsValue bits (⟨argument, coefficient⟩ :: terms) := by
                simp [termsValue, hterm]

theorem eval_dropTrivialLogs (bits : ℕ) (form : Form) :
    eval bits (dropTrivialLogs form) = eval bits form := by
  simp [eval, dropTrivialLogs, termsValue_filter_nontrivial]

theorem eval_canonical (bits : ℕ) (form : Form) :
    eval bits (canonical form) = eval bits form := by
  rw [canonical, eval_dropTrivialLogs, eval_normalize]

theorem eval_fastCanonical (bits : ℕ) (form : Form) :
    eval bits (fastCanonical form) = eval bits form := by
  rw [fastCanonical, eval_dropTrivialLogs, eval_fastNormalize]

/-- Explicit-fuel merging preserves the sum of represented logarithm terms.

Proof sketch: induct on the fuel.  Each recursive branch emits one head term and applies the
induction hypothesis to the two residual runs; the zero-fuel fallback is plain append. -/
theorem termsValue_mergeRunsWithFuel (bits fuel : ℕ) (left right : List Term) :
    termsValue bits (mergeRunsWithFuel fuel left right) =
      termsValue bits left + termsValue bits right := by
  induction fuel generalizing left right with
  | zero => simp [mergeRunsWithFuel, termsValue]
  | succ fuel ih =>
      cases left with
      | nil => simp [mergeRunsWithFuel, termsValue]
      | cons leftHead leftTail =>
          cases right with
          | nil => simp [mergeRunsWithFuel, termsValue]
          | cons rightHead rightTail =>
              simp only [mergeRunsWithFuel]
              by_cases hle : leftHead.argument ≤ rightHead.argument
              · rw [if_pos hle]
                change termValue bits leftHead +
                    termsValue bits (mergeRunsWithFuel fuel leftTail
                      (rightHead :: rightTail)) =
                  (termValue bits leftHead + termsValue bits leftTail) +
                    (termValue bits rightHead + termsValue bits rightTail)
                rw [ih]
                simp only [termsValue, List.map_cons, List.sum_cons]
                ring
              · rw [if_neg hle]
                change termValue bits rightHead +
                    termsValue bits (mergeRunsWithFuel fuel
                      (leftHead :: leftTail) rightTail) =
                  (termValue bits leftHead + termsValue bits leftTail) +
                    (termValue bits rightHead + termsValue bits rightTail)
                rw [ih]
                simp only [termsValue, List.map_cons, List.sum_cons]
                ring

/-- Structural merging preserves the sum of represented logarithm terms. -/
theorem termsValue_structuralMergeRuns (bits : ℕ) (left right : List Term) :
    termsValue bits (structuralMergeRuns left right) =
      termsValue bits left + termsValue bits right := by
  exact termsValue_mergeRunsWithFuel bits (left.length + right.length) left right

/-- Inserting a sorted run into the binary-counter bins adds exactly that run's value. -/
theorem runsValue_structuralInsertRun (bits : ℕ) (run : List Term)
    (runs : List (Option (List Term))) :
    runsValue bits (structuralInsertRun run runs) =
      termsValue bits run + runsValue bits runs := by
  induction runs generalizing run with
  | nil => simp [runsValue]
  | cons stored runs ih =>
      cases stored with
      | none => simp [runsValue]
      | some stored =>
          simp only [runsValue]
          rw [ih, termsValue_structuralMergeRuns]
          ring

/-- Building the binary-counter bins preserves the value of the original term list. -/
theorem runsValue_structuralBuildRuns (bits : ℕ) (terms : List Term) :
    runsValue bits (structuralBuildRuns terms) = termsValue bits terms := by
  have haux (runs : List (Option (List Term))) :
      runsValue bits
          (terms.foldl (fun runs term ↦ structuralInsertRun [term] runs) runs) =
        termsValue bits terms + runsValue bits runs := by
    induction terms generalizing runs with
    | nil => simp [termsValue]
    | cons term terms ih =>
        simp only [List.foldl_cons]
        rw [ih, runsValue_structuralInsertRun]
        simp [termsValue]
        ring
  rw [structuralBuildRuns, haux]
  simp [runsValue]

/-- Collapsing the occupied binary-counter bins preserves their total value. -/
theorem termsValue_structuralCollapseRuns (bits : ℕ)
    (runs : List (Option (List Term))) :
    termsValue bits (structuralCollapseRuns runs) = runsValue bits runs := by
  induction runs with
  | nil => simp [structuralCollapseRuns, runsValue, termsValue]
  | cons run runs ih =>
      cases run with
      | none => simpa [structuralCollapseRuns, runsValue] using ih
      | some run =>
          simp only [structuralCollapseRuns, runsValue, termsValue_structuralMergeRuns, ih]

/-- Structural bottom-up sorting only reorders terms, so it preserves their value. -/
theorem termsValue_structuralBottomUpSort (bits : ℕ) (terms : List Term) :
    termsValue bits (structuralBottomUpSort terms) = termsValue bits terms := by
  rw [structuralBottomUpSort, termsValue_structuralCollapseRuns,
    runsValue_structuralBuildRuns]

/-- Structural sorting followed by coefficient collection preserves the represented value. -/
theorem termsValue_structuralFastNormalizeTerms (bits : ℕ) (terms : List Term) :
    termsValue bits (structuralFastNormalizeTerms terms) = termsValue bits terms := by
  rw [structuralFastNormalizeTerms, termsValue_normalizeTerms,
    termsValue_structuralBottomUpSort]

/-- Structural merge normalization preserves exact evaluation. -/
theorem eval_structuralFastNormalize (bits : ℕ) (form : Form) :
    eval bits (structuralFastNormalize form) = eval bits form := by
  simp [eval, termsValue_structuralFastNormalizeTerms]

/-- Structural merge canonicalization preserves exact evaluation. -/
theorem eval_structuralFastCanonical (bits : ℕ) (form : Form) :
    eval bits (structuralFastCanonical form) = eval bits form := by
  rw [structuralFastCanonical, eval_dropTrivialLogs, eval_structuralFastNormalize]

/-! ## Removing powers of two from logarithm arguments -/

/-- Every bounded split reconstructs its input exactly. -/
theorem splitTwosWithFuel_spec (fuel argument : ℕ) :
    2 ^ (splitTwosWithFuel fuel argument).1 *
        (splitTwosWithFuel fuel argument).2 = argument := by
  induction fuel generalizing argument with
  | zero => simp
  | succ fuel ih =>
      by_cases heven : argument ≠ 0 ∧ argument % 2 = 0
      · simp only [splitTwosWithFuel, heven.2, and_true]
        rw [if_pos heven.1]
        rw [pow_succ', Nat.mul_assoc, ih]
        have hmod := Nat.mod_add_div argument 2
        omega
      · simp [splitTwosWithFuel, heven]

/-- The concrete fast splitter reconstructs its argument. -/
theorem splitTwos_spec (argument : ℕ) :
    2 ^ (splitTwos argument).1 * (splitTwos argument).2 = argument := by
  exact splitTwosWithFuel_spec (Nat.log2 argument + 1) argument

/-- Splitting powers of two preserves the represented base-two logarithm. -/
theorem log2Nat_splitTwos (argument : ℕ) :
    log2Nat argument =
      (splitTwos argument).1 + log2Nat (splitTwos argument).2 := by
  by_cases hzero : argument = 0
  · subst argument
    simp [splitTwos, splitTwosWithFuel, log2Nat]
  · let exponent := (splitTwos argument).1
    let remaining := (splitTwos argument).2
    have hremaining : remaining ≠ 0 := by
      intro h
      have hspec := splitTwos_spec argument
      change 2 ^ exponent * remaining = argument at hspec
      rw [h] at hspec
      simp at hspec
      exact hzero hspec.symm
    have hpow : ((2 : ℝ) ^ exponent) ≠ 0 := by positivity
    have hremainingReal : (remaining : ℝ) ≠ 0 := by
      exact_mod_cast hremaining
    have hfactor : (argument : ℝ) = (2 : ℝ) ^ exponent * remaining := by
      have hspec := splitTwos_spec argument
      change 2 ^ exponent * remaining = argument at hspec
      exact_mod_cast hspec.symm
    change Real.log (argument : ℝ) / Real.log 2 =
      (exponent : ℝ) + Real.log (remaining : ℝ) / Real.log 2
    rw [hfactor]
    rw [Real.log_mul hpow hremainingReal, Real.log_pow]
    have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    field_simp

theorem termValue_splitPowerTerm (bits : ℕ) (term : Term) :
    termValue bits term =
      (term.coefficient * ((splitTwos term.argument).1 : ℤ) : ℤ) /
          (2 : ℝ) ^ bits +
        termValue bits (splitPowerTerm term) := by
  rw [termValue, termValue, splitPowerTerm, log2Nat_splitTwos]
  simp only
  push_cast
  ring

theorem termsValue_splitPowerTerms (bits : ℕ) (terms : List Term) :
    termsValue bits terms =
      ((terms.map fun term =>
          term.coefficient * ((splitTwos term.argument).1 : ℤ)).sum : ℝ) /
          (2 : ℝ) ^ bits +
        termsValue bits (terms.map splitPowerTerm) := by
  induction terms with
  | nil => simp [termsValue]
  | cons term terms ih =>
      change termValue bits term + termsValue bits terms = _
      rw [termValue_splitPowerTerm, ih]
      simp only [termsValue, List.map_cons, List.sum_cons]
      push_cast
      ring

/-- Power-of-two normalization preserves exact real evaluation. -/
theorem eval_normalizePowersOfTwo (bits : ℕ) (form : Form) :
    eval bits (normalizePowersOfTwo form) = eval bits form := by
  unfold eval normalizePowersOfTwo
  rw [termsValue_splitPowerTerms bits form.terms]
  push_cast
  ring

/-- The combined power and merge canonicalizer preserves exact evaluation. -/
theorem eval_powerCanonical (bits : ℕ) (form : Form) :
    eval bits (powerCanonical form) = eval bits form := by
  rw [powerCanonical, eval_fastCanonical, eval_normalizePowersOfTwo]

/-- Structural power canonicalization preserves exact evaluation.

Proof sketch: structural merge canonicalization preserves the normalized form, and power
normalization preserves the original form. -/
theorem eval_structuralPowerCanonical (bits : ℕ) (form : Form) :
    eval bits (structuralPowerCanonical form) = eval bits form := by
  rw [structuralPowerCanonical, eval_structuralFastCanonical, eval_normalizePowersOfTwo]

/-- Fold-based power canonicalization preserves exact evaluation.

Proof sketch: first use `eval_canonical` to combine equal residual logarithms, then use
`eval_normalizePowersOfTwo` to restore the original logarithm arguments. -/
theorem eval_foldPowerCanonical (bits : ℕ) (form : Form) :
    eval bits (foldPowerCanonical form) = eval bits form := by
  rw [foldPowerCanonical, eval_canonical, eval_normalizePowersOfTwo]

end

end MatrixMultiplication.SignedDyadicLogForm.Form
