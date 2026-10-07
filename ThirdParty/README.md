# Vendored third-party Lean developments

Everything under this directory was written elsewhere and is kept here, with its upstream module
names, so that this repository can check it with its own toolchain and connect it to its own
definitions. Nothing in `AlgebraicComplexity/` or `MatrixMultiplication/` imports these files; the
only modules that do are the bridge in `OpenAIBridge/` and its root `OpenAIBridge.lean`.

The files are **not** covered by this repository's module-documentation and copyright-header
gates, which describe hand-written sources of this project. They are covered by the trust scan
(`scripts/trust_scan.sh`), by the same kernel check, and by the same two kinds of enforcing axiom
audit as everything else: `OpenAIBridge/Audit.lean` asserts that the bridged theorem uses only
`propext`, `Classical.choice` and `Quot.sound`, and the root `OpenAIBridge.lean` runs
`#axiom_census_roots OAI FixedPointTheorems OpenAIBridge`, which checks the same for every
declaration of every vendored module and fails if any of them declares an axiom.

## `OAI/` — `ω ≤ 9/4` over every field, and two rectangular bounds over `ℂ`

* Original result: OpenAI, *An Upper Bound of 9/4 for the Matrix Multiplication Exponent*
  (October 2, 2026), with its Lean proof over `ℂ` in <https://github.com/openai/math>, directory
  `lean/OAI/LinearAlgebra/MatrixMultiplication`, commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
* Vendored source: the all-fields generalization of that proof,
  <https://github.com/selanavot/matrix-multiplication-all-fields>, directory `lean/OAI`, commit
  `c4aaf797f2a8e631e3bc17347fc1fe627341c16e`. It is a source fork of the OpenAI subtree: 120
  upstream modules (40 of them modified) and 6 new ones. `OAI/UPSTREAM.md` is that repository's
  own provenance note, copied unchanged.
* Licence: Apache-2.0 (`OAI/LICENSE`), as in both upstream repositories.
* Upstream toolchain: Lean `v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
* What is vendored: all 126 modules of `lean/OAI` of the fork, and 130 further modules of the
  same directory of `openai/math` at the commit above. The latter are what OpenAI's two other
  matrix-multiplication theorems need beyond the fork: `ω(1, 0.709, 1) < 2.092`
  (`CW75ReorderedRectangular.rectangularOmega_lt_target`) and the dual exponent `α > 0.465`
  (`DualExponentBound.alpha_gt`), both over `ℂ` and both stated in the arithmetic-program model.
  The fork modified none of the modules those two theorems share with it, so the 256 files form
  one consistent tree. Not vendored: the remaining 259 modules of the upstream directory,
  which none of the three theorems imports, and the upstream `Main.lean`, which imports them.
* Changes made here are listed in `OAI/CHANGES.md`. They are limited to what this repository's
  older toolchain (Lean `v4.33.0-rc1` and the Mathlib pinned in `lake-manifest.json`) requires:
  59 of the 256 files, about 180 lines, all inside proofs or `import` lines; no statement was
  changed. Each modified file says so in its first line; every other file is byte-identical to
  its upstream source.

## `FixedPointTheorems/` — Brouwer's fixed-point theorem

* Source: <https://github.com/harfe/fixed-point-theorems-lean4>, commit
  `770940ddf9878cf61952ed53d910b92bca841838`, the revision pinned by both repositories above.
* Licence: MIT (`FixedPointTheorems/LICENSE`).
* What is vendored: `brouwer.lean` and its four imports. `kakutani.lean` is not needed and is not
  included.
* Used by `OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Convex/FixedPoint.lean`.
