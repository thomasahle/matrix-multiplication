/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.DyadicLogLinear
import MatrixMultiplication.SignedDyadicLogCanonical

/-!
# Small compositional certificates for signed dyadic logarithm forms

Large entropy certificates reduce to a dyadic rational constant plus finitely many positive and
negative integer multiples of `log₂` of positive integers.  This module provides the small trusted
checker for that representation:

* `Form.ofSignedFamilies` turns two finite nonnegative families into an exact signed form;
* `Form.eval_ofSignedFamilies` identifies its real value;
* `LowerBound` packages a directed lower bound for an exact form; and
* `LowerBound.constant`, `add`, `sum`, and the two power canonicalizers compose certificates
  without exposing the generated arithmetic again.

An untrusted producer may therefore split a large form into small term shards.  Each shard proves
its logarithm bounds using `DyadicLogLinear`; this file proves once and for all that adding those
shards and canonicalizing the result preserves the directed bound.  No matrix-multiplication
tensor, optimizer convention, or certificate constant occurs here.
-/

open scoped BigOperators

namespace MatrixMultiplication.SignedDyadicLogCertificate

open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogForm

noncomputable section

namespace Form

/-- The exact form consisting of an integer constant, a positive logarithm family, and a negative
logarithm family.  Coefficient magnitudes remain natural numbers in generated certificates. -/
def ofSignedFamilies {positiveCount negativeCount : ℕ} (constantNumerator : ℤ)
    (positiveArgument positiveCoefficient : Fin positiveCount → ℕ)
    (negativeArgument negativeCoefficient : Fin negativeCount → ℕ) :
    SignedDyadicLogForm.Form :=
  { constantNumerator := constantNumerator
    terms :=
      List.ofFn (fun index ↦
        { argument := positiveArgument index
          coefficient := (positiveCoefficient index : ℤ) }) ++
      List.ofFn (fun index ↦
        { argument := negativeArgument index
          coefficient := -(negativeCoefficient index : ℤ) }) }

/-- A signed-family form evaluates to its rational constant plus the positive log sum minus the
negative log sum.

Proof sketch: expand the two `List.ofFn` blocks, cast their signed coefficients to `ℝ`, and collect
the negative block with `Finset.sum_neg_distrib`. -/
theorem eval_ofSignedFamilies {positiveCount negativeCount : ℕ} (bits : ℕ)
    (constantNumerator : ℤ)
    (positiveArgument positiveCoefficient : Fin positiveCount → ℕ)
    (negativeArgument negativeCoefficient : Fin negativeCount → ℕ) :
    SignedDyadicLogForm.Form.eval bits
        (ofSignedFamilies constantNumerator positiveArgument positiveCoefficient
          negativeArgument negativeCoefficient) =
      (constantNumerator : ℝ) / (2 : ℝ) ^ bits +
        SignedDyadicLogForm.Form.natLogSum bits positiveArgument positiveCoefficient -
          SignedDyadicLogForm.Form.natLogSum bits negativeArgument negativeCoefficient := by
  unfold SignedDyadicLogForm.Form.eval ofSignedFamilies
    SignedDyadicLogForm.Form.termsValue SignedDyadicLogForm.Form.natLogSum
  rw [List.map_append, List.sum_append]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply,
    SignedDyadicLogForm.Form.termValue, Int.cast_natCast, Int.cast_neg]
  simp_rw [neg_div, neg_mul]
  rw [Finset.sum_neg_distrib]
  ring

end Form

/-! ## Common-denominator term certificates -/

/-- Directed lower bounds for individual scaled logarithms combine into a lower bound for the
whole dyadic logarithm sum.

This is the proof-engineering interface used by large generated certificates.  Each logarithm can
be bounded independently at a common rational denominator; the generated proof then performs only
one linear weighted sum instead of normalizing a sum of unrelated atanh denominators.

Proof sketch: apply the certified lower logarithm bound term by term, multiply by the nonnegative
dyadic coefficient, and sum the resulting inequalities.
-/
theorem weightedLowerWithScale_le_natLogSum {count : ℕ} (steps bits : ℕ)
    (argument coefficient scale : Fin count → ℕ) (lower : Fin count → ℝ)
    (hscale : ∀ term, 2 ^ scale term ≤ argument term)
    (hlower : ∀ term,
      lower term ≤ FastDyadicLog.numeratorLogLower (argument term) (scale term) steps) :
    ∑ term, DyadicEntropy.mass bits (coefficient term) * lower term ≤
      SignedDyadicLogForm.Form.natLogSum bits argument coefficient := by
  unfold SignedDyadicLogForm.Form.natLogSum SignedDyadicLogForm.log2Nat
  apply Finset.sum_le_sum
  intro term _
  have hcoefficient : 0 ≤ (coefficient term : ℝ) / (2 : ℝ) ^ bits :=
    div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)
  exact mul_le_mul_of_nonneg_left
    ((hlower term).trans (FastDyadicLog.numeratorLogLower_le (hscale term))) hcoefficient

/-- Directed upper bounds for individual scaled logarithms combine into an upper bound for the
whole dyadic logarithm sum.

Proof sketch: use the certified upper logarithm bound at each index, enlarge it to the supplied
rational endpoint, multiply by the nonnegative dyadic coefficient, and sum.
-/
theorem natLogSum_le_weightedUpperWithScale {count : ℕ} (steps bits : ℕ)
    (argument coefficient scale : Fin count → ℕ) (upper : Fin count → ℝ)
    (hscale : ∀ term, 2 ^ scale term ≤ argument term)
    (hupper : ∀ term,
      FastDyadicLog.numeratorLogUpper (argument term) (scale term) steps ≤ upper term) :
    SignedDyadicLogForm.Form.natLogSum bits argument coefficient ≤
      ∑ term, DyadicEntropy.mass bits (coefficient term) * upper term := by
  unfold SignedDyadicLogForm.Form.natLogSum SignedDyadicLogForm.log2Nat
  apply Finset.sum_le_sum
  intro term _
  have hcoefficient : 0 ≤ (coefficient term : ℝ) / (2 : ℝ) ^ bits :=
    div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)
  exact mul_le_mul_of_nonneg_left
    ((FastDyadicLog.le_numeratorLogUpper (hscale term)).trans (hupper term)) hcoefficient

/-- A kernel-checked lower bound for the exact value of one signed dyadic logarithm form. -/
structure LowerBound (bits : ℕ) where
  form : SignedDyadicLogForm.Form
  lower : ℝ
  lower_le_eval : lower ≤ SignedDyadicLogForm.Form.eval bits form

namespace LowerBound

/-- Reordering logarithmic terms while retaining the constant does not change a form's value.

Proof sketch: map `termValue` across the supplied list permutation and use invariance of a finite
sum under permutation. -/
theorem eval_eq_of_constant_eq_of_terms_perm {bits : ℕ}
    {left right : SignedDyadicLogForm.Form}
    (hconstant : left.constantNumerator = right.constantNumerator)
    (hterms : left.terms.Perm right.terms) :
    SignedDyadicLogForm.Form.eval bits left = SignedDyadicLogForm.Form.eval bits right := by
  unfold SignedDyadicLogForm.Form.eval SignedDyadicLogForm.Form.termsValue
  rw [hconstant, (hterms.map (SignedDyadicLogForm.Form.termValue bits)).sum_eq]

/-- Transport a lower-bound certificate to an exact form that differs only by term order.

This constructor lets generated checkers retain the producer's original bounded shard order while
using sign-separated arithmetic internally.  The permutation is an explicit checked premise; no
canonicalization or whole-certificate computation is hidden in the transport.

Proof sketch: keep the certified endpoint and rewrite the exact evaluation by permutation
invariance. -/
def reorder {bits : ℕ} (certificate : LowerBound bits)
    (form : SignedDyadicLogForm.Form)
    (hconstant : certificate.form.constantNumerator = form.constantNumerator)
    (hterms : certificate.form.terms.Perm form.terms) : LowerBound bits :=
  { form := form
    lower := certificate.lower
    lower_le_eval := certificate.lower_le_eval.trans_eq
      (eval_eq_of_constant_eq_of_terms_perm hconstant hterms) }

/-- The exact constant form is its own lower-bound certificate. -/
def constant (bits : ℕ) (constantNumerator : ℤ) : LowerBound bits :=
  { form := { constantNumerator := constantNumerator, terms := [] }
    lower := (constantNumerator : ℝ) / (2 : ℝ) ^ bits
    lower_le_eval := by
      simp [SignedDyadicLogForm.Form.eval, SignedDyadicLogForm.Form.termsValue] }

/-- Directed bounds for the positive and negative logarithm sums give a lower bound for the exact
signed-family form.

Proof sketch: add the positive lower bound to the unchanged rational constant, subtract the
negative upper bound, and invoke `Form.eval_ofSignedFamilies`. -/
def ofSignedFamilies {positiveCount negativeCount : ℕ} (bits : ℕ)
    (constantNumerator : ℤ)
    (positiveArgument positiveCoefficient : Fin positiveCount → ℕ)
    (negativeArgument negativeCoefficient : Fin negativeCount → ℕ)
    (positiveLower negativeUpper : ℝ)
    (hpositive : positiveLower ≤
      SignedDyadicLogForm.Form.natLogSum bits positiveArgument positiveCoefficient)
    (hnegative : SignedDyadicLogForm.Form.natLogSum bits
      negativeArgument negativeCoefficient ≤ negativeUpper) : LowerBound bits :=
  { form := Form.ofSignedFamilies constantNumerator positiveArgument positiveCoefficient
      negativeArgument negativeCoefficient
    lower := (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveLower - negativeUpper
    lower_le_eval := by
      rw [Form.eval_ofSignedFamilies]
      exact sub_le_sub (add_le_add_right hpositive _) hnegative }

/-- Lower-bound certificates add exactly when their exact forms add. -/
def add {bits : ℕ} (left right : LowerBound bits) : LowerBound bits :=
  { form := SignedDyadicLogForm.Form.add left.form right.form
    lower := left.lower + right.lower
    lower_le_eval := by
      rw [SignedDyadicLogForm.Form.eval_add]
      exact add_le_add left.lower_le_eval right.lower_le_eval }

/-- Sum a finite list of lower-bound certificates. -/
def sum {bits : ℕ} : List (LowerBound bits) → LowerBound bits
  | [] => constant bits 0
  | certificate :: certificates => add certificate (sum certificates)

/-- The exact form carried by a certificate sum is the exact form sum of its entries.

This aggregate-projection law is intentionally not a global simp lemma.  Generated checkers use
it as an explicit rewrite at the certificate boundary; exposing the fields of every certificate
sum during unrelated simplification can create large terms and fragile record-eta goals. -/
theorem sum_form {bits : ℕ} (certificates : List (LowerBound bits)) :
    (sum certificates).form =
      SignedDyadicLogForm.Form.sum (certificates.map LowerBound.form) := by
  induction certificates with
  | nil => rfl
  | cons certificate certificates ih =>
      simp only [sum, add, SignedDyadicLogForm.Form.sum, List.map_cons]
      rw [ih]

/-- The rational endpoint carried by a certificate sum is the sum of its endpoints.

Like `sum_form`, this remains an explicit boundary rewrite rather than a global simp rule. -/
theorem sum_lower {bits : ℕ} (certificates : List (LowerBound bits)) :
    (sum certificates).lower = (certificates.map LowerBound.lower).sum := by
  induction certificates with
  | nil => simp [sum, constant]
  | cons certificate certificates ih => simp [sum, add, ih]

/-- Pointwise evaluation-preserving rewrites transport the sum of lower-bound certificates to the
sum of the corresponding exact forms.

This is the compositional checker used when each small generated shard extracts powers of two
independently.  It avoids ever comparing or canonicalizing the complete parent form: the caller
only proves one evaluation equality per shard and separately proves that the raw forms concatenate
to the intended source form.

Proof sketch: induct on the `Forall₂` witness.  At each head, add the stored certificate bound to
the induction hypothesis and rewrite the head evaluation by the supplied equality. -/
theorem sum_lower_le_eval_sum_of_forall₂ {bits : ℕ}
    {certificates : List (LowerBound bits)}
    {forms : List SignedDyadicLogForm.Form}
    (h : List.Forall₂
      (fun certificate form ↦
        SignedDyadicLogForm.Form.eval bits certificate.form =
          SignedDyadicLogForm.Form.eval bits form)
      certificates forms) :
    (sum certificates).lower ≤ SignedDyadicLogForm.Form.eval bits
      (SignedDyadicLogForm.Form.sum forms) := by
  induction certificates generalizing forms with
  | nil =>
      cases h
      simp [sum, constant, SignedDyadicLogForm.Form.sum]
  | cons certificate certificates ih =>
      cases h with
      | cons hhead htail =>
          rw [sum, add, SignedDyadicLogForm.Form.sum,
            SignedDyadicLogForm.Form.eval_add]
          exact add_le_add (certificate.lower_le_eval.trans_eq hhead) (ih htail)

/-- Extracting powers of two, combining equal log arguments, and removing trivial logarithms does
not change a certificate's lower bound.

Proof sketch: `Form.eval_powerCanonical` says that the canonicalized and original forms have
identical real evaluations, so the existing directed inequality transports across that equality. -/
def powerCanonical {bits : ℕ} (certificate : LowerBound bits) : LowerBound bits :=
  { form := SignedDyadicLogForm.Form.powerCanonical certificate.form
    lower := certificate.lower
    lower_le_eval := certificate.lower_le_eval.trans_eq
      (SignedDyadicLogForm.Form.eval_powerCanonical bits certificate.form).symm }

/-- Canonicalize a bounded certificate through the kernel-friendly fold implementation.

Proof sketch: `Form.eval_foldPowerCanonical` identifies the new form's value with the old form's
value, so the certificate's existing directed inequality transports unchanged. -/
def foldPowerCanonical {bits : ℕ} (certificate : LowerBound bits) : LowerBound bits :=
  { form := SignedDyadicLogForm.Form.foldPowerCanonical certificate.form
    lower := certificate.lower
    lower_le_eval := certificate.lower_le_eval.trans_eq
      (SignedDyadicLogForm.Form.eval_foldPowerCanonical bits certificate.form).symm }

/-- Canonicalize a large certificate through the structurally recursive merge implementation.

This is quasilinear like `powerCanonical`, but its evaluator contains no well-founded merge
recursor, so generated kernel checks do not get stuck on dependent reduction artifacts. -/
def structuralPowerCanonical {bits : ℕ} (certificate : LowerBound bits) : LowerBound bits :=
  { form := SignedDyadicLogForm.Form.structuralPowerCanonical certificate.form
    lower := certificate.lower
    lower_le_eval := certificate.lower_le_eval.trans_eq
      (SignedDyadicLogForm.Form.eval_structuralPowerCanonical bits certificate.form).symm }

end LowerBound

end

end MatrixMultiplication.SignedDyadicLogCertificate
