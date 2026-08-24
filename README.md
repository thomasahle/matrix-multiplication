# Lean verification of the repeated-orientation candidate

This branch contains a layered Lean 4 / Mathlib verification of the proposed bound

\[
\omega \le 2.37071.
\]

## What Lean currently proves

`RepeatedOrientationVerification/Certificate.lean` proves, without `sorry`:

- the exact rational endpoint inequality;
- the exact integer comparison `7^462 < 2^1297`;
- the resulting analytic bound `log₂ 7 < 1297/462`;
- positivity of the conservative scalar feasibility margin.

The fully formal rational slack is

\[
\frac{251285619532691}{23100000000000000000}
\approx 1.0878\times 10^{-5}.
\]

`RepeatedOrientationVerification/Regionwise.lean` proves the abstract repeated-orientation theorem:
for any monoidal extraction relation preserved by coordinate orientation, an arbitrary assignment of
orientations to finitely many labelled regions is valid. No injectivity assumption is used, and a
corollary specializes to six copies of one orientation.

## What remains explicit

A complete formal verification still needs two instantiations, both represented as hypotheses rather
than hidden axioms:

1. reconstruct the retained-exponent and matrix-size lower bounds from the binary certificate inside
   Lean; and
2. instantiate the abstract regionwise system with the full tensor-degeneration, hashing, interface-
   tensor, and asymptotic-sum machinery of the published laser-method proof.

`UPSTREAM_AUDIT.md` records the exact source locations where the published proof decomposes into
labelled tensor factors, applies the one-region procedure under a coordinate permutation, and tensors
all region outputs.

## Build

```bash
lake update
lake exe cache get
lake build
```

The project is pinned to Lean 4.30.0 and Mathlib 4.30.0. GitHub Actions compiles every theorem and
prints its axiom dependencies.
