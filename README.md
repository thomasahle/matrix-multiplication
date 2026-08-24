# Lean verification of the repeated-orientation candidate

This branch contains two related developments:

1. a reusable `AlgebraicComplexity.Tensor` library built on Mathlib's module tensor product; and
2. a layered Lean verification of the proposed rounded bound

\[
\omega < 2.37071.
\]

## Algebraic-complexity tensor library

The library deliberately reuses Mathlib's tensor products, linear maps, finite sums, matrices, and
polynomials. The custom layer adds the notions that are specific to algebraic complexity.

| Module | Main contents |
|---|---|
| `Basic` | right-associated trilinear tensors, pure tensors, three-coordinate maps, coordinate permutations |
| `Restriction` | exact tensor restriction, transitivity, restriction equivalence |
| `Rank` | explicit finite rank witnesses and monotonicity under restriction |
| `DirectSum` | coordinatewise direct sums with injections and projections |
| `ExternalProduct` | external product of trilinear tensors and bilinearity |
| `RankProduct` | multiplication of explicit rank bounds under external products |
| `MatrixMultiplication` | the rectangular tensor `⟨m,n,p⟩`, schoolbook rank certificate, cyclic symmetry |
| `MonomialDegeneration` | coordinate tensors, integer-weight leading parts, variable zeroing, support monotonicity |
| `Coordinates` | standard-basis realization and proof that variable zeroing is an exact restriction |
| `CoppersmithWinograd` | `CW_q`, its elementary rank certificate, and cyclic symmetry |

All theorems in this layer compile without `sorryAx`. The abstract tensor representation currently
keeps the scalar ring and tensor factors in one Lean universe. That covers all finite-dimensional
coordinate spaces used here; widening this API is a later refactor rather than a mathematical
restriction.

The next algebraic layers are constructive polynomial degeneration and border rank, tensor powers
and asymptotic rank, matrix-tensor product equivalences, and eventually the asymptotic-sum and
laser-method machinery.

## What Lean currently proves about the candidate bound

`RepeatedOrientationVerification/Certificate.lean` proves, without `sorry`:

- the exact rational endpoint inequality at the stronger value `2.370709`;
- the exact integer comparison `7^462 < 2^1297`;
- the resulting analytic bound `log₂ 7 < 1297/462`;
- positivity of the conservative scalar feasibility margin;
- the implication `omega ≤ 2.370709`, and hence `omega < 2.37071`, once the two explicit
  certificate/theorem interfaces below are supplied.

The fully formal rational slack at `2.370709` is

\[
\frac{1123045738686689}{231000000000000000000}
\approx 4.8617\times 10^{-6}.
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
lake build
```

The project is pinned to Lean 4.30.0 and Mathlib 4.30.0. GitHub Actions compiles every theorem,
rejects any dependency on `sorryAx`, and archives a reproducible source bundle.
