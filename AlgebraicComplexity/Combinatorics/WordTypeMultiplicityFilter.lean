/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.WordTypeCore

/-!
# `WordType.multiplicity` as a position-filter cardinality, at any decidability instance

Layer 2 (`AlgebraicComplexity/Combinatorics/`).  `Combinatorics/WordTypeCore.lean` defines

```text
noncomputable def multiplicity (word : Fin n → ι) (i : ι) : ℕ := by
  classical
  exact (Finset.univ.filter fun j ↦ word j = i).card
```

The `classical` in that body is what makes the definition total without a `DecidableEq ι`
hypothesis, and it is also a recurring nuisance: the `Finset.filter` inside `multiplicity` carries
`Classical.propDecidable`, whereas a client that has `[DecidableEq ι]` in scope and writes the
*same* filter gets the instance derived from `DecidableEq ι`.  The two terms are propositionally
equal and definitionally *not*, so `rw`, `simp` and `exact` all fail between them with an
unhelpful "motive is not type correct" or a silent non-match.

This module retires that mismatch once and for all.  `Finset.card` and `Finset.filter` do not
depend on which `Decidable` instance is supplied --- `Decidable p` is a subsingleton --- so
`congr` discharges the difference, and the resulting equation can then be used with whatever
instance the call site happens to have.

## Principal results

* `multiplicity_eq_card_filter` --- stated for an **arbitrary** `DecidablePred`, hence usable at
  the ambient `DecidableEq ι` instance, at `Classical.propDecidable`, and at any bespoke instance
  a client constructs.
* `multiplicity_eq_card_filter_of_decidableEq` --- the common specialization, with the instance
  found by the ambient `[DecidableEq ι]`.
* `card_filter_eq_multiplicity` --- the same equation oriented for `simp`, which normalizes a raw
  position-filter cardinality into the abstract `multiplicity`.

## Why the `simp` direction is this way round

`multiplicity` is the abstract normal form: the whole word-type API (`typeClass`,
`sum_multiplicity`, `profileEntropyNats`, the method-of-types counting) is phrased in it, and a
bare `(Finset.univ.filter _).card` is what leaks out of a concrete construction.  Rewriting
concrete into abstract therefore lands in the API rather than out of it.  Clients that genuinely
need to compute should use `multiplicity_eq_card_filter` explicitly in the other direction.
-/

namespace AlgebraicComplexity.WordType

universe u

variable {ι : Type u}

/-- **`multiplicity word i` is the number of positions carrying the letter `i`**, computed with
*any* decidability instance for the position predicate.

Stating it at an arbitrary `[DecidablePred fun j ↦ word j = i]` rather than at a fixed instance is
the whole point: the instance in `multiplicity`'s own body is `Classical.propDecidable`, and a
client's is whatever `[DecidableEq ι]` produces, so a lemma pinned to either one fails against the
other.  `Decidable` is a subsingleton, so `congr` closes the gap. -/
theorem multiplicity_eq_card_filter {n : ℕ} (word : Fin n → ι) (i : ι)
    [DecidablePred fun j : Fin n ↦ word j = i] :
    multiplicity word i = (Finset.univ.filter fun j ↦ word j = i).card := by
  unfold multiplicity
  -- `Decidable p` is a subsingleton, so the two filters differ only in a proof-irrelevant
  -- instance argument.  (If a future Mathlib makes `congr` too eager here, the drop-in
  -- replacement is `simp only [Finset.filter_congr_decidable]`.)
  congr

/-- The common specialization of `multiplicity_eq_card_filter`: the position predicate is decided
by the ambient `[DecidableEq ι]`. -/
theorem multiplicity_eq_card_filter_of_decidableEq [DecidableEq ι] {n : ℕ}
    (word : Fin n → ι) (i : ι) :
    multiplicity word i = (Finset.univ.filter fun j ↦ word j = i).card :=
  multiplicity_eq_card_filter word i

/-- `simp`-oriented form: a raw position-filter cardinality normalizes to `multiplicity`. -/
@[simp] theorem card_filter_eq_multiplicity {n : ℕ} (word : Fin n → ι) (i : ι)
    [DecidablePred fun j : Fin n ↦ word j = i] :
    (Finset.univ.filter fun j ↦ word j = i).card = multiplicity word i :=
  (multiplicity_eq_card_filter word i).symm

end AlgebraicComplexity.WordType
