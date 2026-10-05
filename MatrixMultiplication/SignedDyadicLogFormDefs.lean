/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Init

/-!
# Executable signed dyadic log-linear forms

This definition-only module contains the exact syntax and canonical normalization used by dyadic
entropy certificates.  It deliberately imports no real analysis and states no semantic theorem.
Consequently generated equality checkers can normalize large integer forms without loading the
logarithm, entropy, or tactic closure.

`SignedDyadicLogForm.lean` extends this syntax with real-valued evaluation and proves that every
exact operation and normalization preserves that evaluation.
-/

namespace MatrixMultiplication.SignedDyadicLogForm

/-- One integer-weighted logarithm of a positive natural-number argument. -/
structure Term where
  argument : Nat
  coefficient : Int
  deriving DecidableEq, Repr

/-- A dyadic rational constant numerator plus a finite list of logarithmic terms. -/
structure Form where
  constantNumerator : Int
  terms : List Term
  deriving DecidableEq, Repr

namespace Form

/-- The exact zero form. -/
def zero : Form := ⟨0, []⟩

/-- Add two forms by adding constants and concatenating their term lists. -/
def add (left right : Form) : Form :=
  ⟨left.constantNumerator + right.constantNumerator, left.terms ++ right.terms⟩

/-- Negate the constant and every logarithmic coefficient. -/
def neg (form : Form) : Form :=
  ⟨-form.constantNumerator,
    form.terms.map fun term => ⟨term.argument, -term.coefficient⟩⟩

/-- Subtraction of exact forms. -/
def sub (left right : Form) : Form := left.add right.neg

/-- Sum a finite list of exact forms. -/
def sum : List Form → Form
  | [] => zero
  | form :: forms => add form (sum forms)

/-- Scale a form by a natural-number multiplicity. -/
def scaleNat (scalar : Nat) (form : Form) : Form :=
  ⟨scalar * form.constantNumerator,
    form.terms.map fun term => ⟨term.argument, scalar * term.coefficient⟩⟩

/-- Insert into an argument-sorted term list, combining equal arguments and dropping zeros. -/
def insert (term : Term) : List Term → List Term
  | [] => if term.coefficient = 0 then [] else [term]
  | head :: tail =>
      if term.coefficient = 0 then head :: tail
      else if term.argument < head.argument then term :: head :: tail
      else if term.argument = head.argument then
        let coefficient := term.coefficient + head.coefficient
        if coefficient = 0 then tail else ⟨term.argument, coefficient⟩ :: tail
      else head :: insert term tail

/-- Canonicalize logarithmic terms by argument and combine their coefficients. -/
def normalizeTerms (terms : List Term) : List Term :=
  terms.foldr insert []

/-- Canonicalize the logarithmic part of a form, retaining its constant numerator. -/
def normalize (form : Form) : Form :=
  ⟨form.constantNumerator, normalizeTerms form.terms⟩

/-- A compact form whose displayed logarithmic coefficients are all nonpositive. -/
def ofNegativeFamily {count : Nat} (constantNumerator : Int)
    (argument coefficient : Fin count → Nat) : Form :=
  ⟨constantNumerator,
    List.ofFn fun index => ⟨argument index, -(coefficient index : Int)⟩⟩

end Form

end MatrixMultiplication.SignedDyadicLogForm
