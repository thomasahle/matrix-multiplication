/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SignedDyadicLogFormDefs
import Mathlib.Data.List.Sort

/-!
# Executable canonical signed dyadic logarithm forms

This definition-only module contains the canonicalizers used by generated dyadic-log
certificates.  It deliberately imports no real-valued evaluation theory.  Generated equality
checkers and bounded streaming folds can therefore reduce these functions without loading the
logarithm, entropy, or proof-tactic closure from `SignedDyadicLogCanonical`.

The available normalizers progressively add three operations:

* collect equal logarithm arguments and discard the trivial arguments zero and one;
* use an explicit-fuel merge sort whose reduction is stable on large literal lists; and
* remove powers of two from logarithm arguments, moving their exponents into the dyadic constant.

`SignedDyadicLogCanonical.lean` proves that every operation below preserves real evaluation.
-/

namespace MatrixMultiplication.SignedDyadicLogForm.Form

open MatrixMultiplication.SignedDyadicLogForm

/-! ## Collecting equal logarithm arguments -/

/-- Remove logarithm terms whose real value is identically zero. -/
def dropTrivialLogs (form : Form) : Form :=
  { constantNumerator := form.constantNumerator
    terms := form.terms.filter fun term ↦ 1 < term.argument }

/-- Combine equal arguments and remove the logarithms of zero and one. -/
def canonical (form : Form) : Form :=
  dropTrivialLogs (normalize form)

/-- Comparison used to merge argument-sorted logarithm runs. -/
@[reducible] def termLE (left right : Term) : Bool :=
  left.argument ≤ right.argument

/-- Merge two argument-sorted runs. -/
@[reducible] def mergeRuns (left right : List Term) : List Term :=
  left.merge right termLE

/-- Insert one sorted run into binary-counter merge bins. -/
@[reducible] def insertRun (run : List Term) :
    List (Option (List Term)) → List (Option (List Term))
  | [] => [some run]
  | none :: runs => some run :: runs
  | some stored :: runs => none :: insertRun (mergeRuns stored run) runs

/-- Build binary-counter merge bins from singleton terms. -/
@[reducible] def buildRuns (terms : List Term) : List (Option (List Term)) :=
  terms.foldl (fun runs term ↦ insertRun [term] runs) []

/-- Merge every occupied binary-counter bin. -/
@[reducible] def collapseRuns : List (Option (List Term)) → List Term
  | [] => []
  | none :: runs => collapseRuns runs
  | some run :: runs => mergeRuns run (collapseRuns runs)

/-- Kernel-reducible bottom-up merge sort.

Unlike `List.mergeSort`, this definition has no dependent split proofs, so kernel reduction can
evaluate it on large generated literals. -/
@[reducible] def bottomUpSort (terms : List Term) : List Term :=
  collapseRuns (buildRuns terms)

/-- Sort terms before combining equal arguments.

Since `normalizeTerms` processes the sorted list from right to left, every insertion is then at
the head of the accumulated list. -/
@[reducible] def fastNormalizeTerms (terms : List Term) : List Term :=
  normalizeTerms (bottomUpSort terms)

/-- Quasilinear executable normalizer for large generated forms. -/
@[reducible] def fastNormalize (form : Form) : Form :=
  ⟨form.constantNumerator, fastNormalizeTerms form.terms⟩

/-- Fast semantic canonicalizer used by large generated certificates. -/
@[reducible] def fastCanonical (form : Form) : Form :=
  dropTrivialLogs (fastNormalize form)

/-! ## Structurally recursive merge normalization

`List.merge` is efficient when evaluated normally, but its well-founded recursor can leave
`Eq.rec` terms that block kernel reduction inside equality checks.  This variant consumes an
explicit fuel argument and is structurally recursive throughout.
-/

/-- Merge two sorted term runs with explicit structural-recursion fuel. -/
@[reducible] def mergeRunsWithFuel : ℕ → List Term → List Term → List Term
  | 0, left, right => left ++ right
  | _ + 1, [], right => right
  | _ + 1, left, [] => left
  | fuel + 1, leftHead :: leftTail, rightHead :: rightTail =>
      if leftHead.argument ≤ rightHead.argument then
        leftHead :: mergeRunsWithFuel fuel leftTail (rightHead :: rightTail)
      else
        rightHead :: mergeRunsWithFuel fuel (leftHead :: leftTail) rightTail

/-- Kernel-friendly linear merge of two sorted runs. -/
@[reducible] def structuralMergeRuns (left right : List Term) : List Term :=
  mergeRunsWithFuel (left.length + right.length) left right

/-- Insert one sorted run into structural-merge binary-counter bins. -/
@[reducible] def structuralInsertRun (run : List Term) :
    List (Option (List Term)) → List (Option (List Term))
  | [] => [some run]
  | none :: runs => some run :: runs
  | some stored :: runs => none :: structuralInsertRun (structuralMergeRuns stored run) runs

/-- Build structural-merge binary-counter bins from singleton terms. -/
@[reducible] def structuralBuildRuns (terms : List Term) : List (Option (List Term)) :=
  terms.foldl (fun runs term ↦ structuralInsertRun [term] runs) []

/-- Merge every occupied structural-merge binary-counter bin. -/
@[reducible] def structuralCollapseRuns : List (Option (List Term)) → List Term
  | [] => []
  | none :: runs => structuralCollapseRuns runs
  | some run :: runs => structuralMergeRuns run (structuralCollapseRuns runs)

/-- Kernel-friendly bottom-up merge sort without well-founded recursion. -/
@[reducible] def structuralBottomUpSort (terms : List Term) : List Term :=
  structuralCollapseRuns (structuralBuildRuns terms)

/-- Quasilinear normalizer whose executable path is entirely structurally recursive. -/
@[reducible] def structuralFastNormalizeTerms (terms : List Term) : List Term :=
  normalizeTerms (structuralBottomUpSort terms)

/-- Form-level structural merge normalizer. -/
@[reducible] def structuralFastNormalize (form : Form) : Form :=
  ⟨form.constantNumerator, structuralFastNormalizeTerms form.terms⟩

/-- Structural merge canonicalizer for kernel-checked generated certificates. -/
@[reducible] def structuralFastCanonical (form : Form) : Form :=
  dropTrivialLogs (structuralFastNormalize form)

/-! ## Removing powers of two from logarithm arguments -/

/-- Bounded executable splitting of powers of two.

The first component is the extracted exponent and the second is the remaining factor. -/
@[reducible] def splitTwosWithFuel : ℕ → ℕ → ℕ × ℕ
  | 0, argument => (0, argument)
  | fuel + 1, argument =>
      if argument ≠ 0 ∧ argument % 2 = 0 then
        let tail := splitTwosWithFuel fuel (argument / 2)
        (tail.1 + 1, tail.2)
      else
        (0, argument)

/-- Fast power-of-two split used by the certificate normalizer. -/
@[reducible] def splitTwos (argument : ℕ) : ℕ × ℕ :=
  splitTwosWithFuel (Nat.log2 argument + 1) argument

/-- Replace one logarithm argument by its factor after removing powers of two. -/
@[reducible] def splitPowerTerm (term : Term) : Term :=
  ⟨(splitTwos term.argument).2, term.coefficient⟩

/-- Move every extracted power-of-two logarithm into the rational constant. -/
@[reducible] def normalizePowersOfTwo (form : Form) : Form :=
  { constantNumerator := form.constantNumerator +
      (form.terms.map fun term =>
        term.coefficient * ((splitTwos term.argument).1 : ℤ)).sum
    terms := form.terms.map splitPowerTerm }

/-- Fast canonical form after removing power-of-two factors. -/
@[reducible] def powerCanonical (form : Form) : Form :=
  fastCanonical (normalizePowersOfTwo form)

/-- Quasilinear, structurally recursive canonical form after removing power-of-two factors. -/
@[reducible] def structuralPowerCanonical (form : Form) : Form :=
  structuralFastCanonical (normalizePowersOfTwo form)

/-- Kernel-reduction-friendly canonical form after removing power-of-two factors.

This combines terms with the simple fold-based `canonical` function.  The merge version is
preferable for very long lists under ordinary evaluation; this fold version is useful for bounded
generated shards whose reductions should avoid dependent merge recursors. -/
@[reducible] def foldPowerCanonical (form : Form) : Form :=
  canonical (normalizePowersOfTwo form)

end MatrixMultiplication.SignedDyadicLogForm.Form
