# Audit of the repeated-orientation interface

The proposed extension needs two structural facts from the extraction proof:

1. each labelled region is processed by a one-region procedure that is equivariant under a
   permutation of the `X`, `Y`, and `Z` roles; and
2. the outputs of different labelled regions are combined only by tensor product.

The arXiv v2 source of Alman–Duan–Vassilevska Williams–Xu–Xu–Zhou, downloaded from
`https://arxiv.org/e-print/2404.16349`, states both facts explicitly.

## Global stage

In `global.tex`, lines 134–138, the source tensor power is written as

```tex
\bigotimes_{r=1}^6
  (\mathrm{CW}_q^{\otimes 2^{\ell-1}})^{\otimes A_r n},
```

and the paper says that it analyzes the first region while the remaining regions are obtained by
permuting the roles of the three dimensions. At the end of the proof, line 473 says:

> In the end, we take the tensor product over the output tensor of the algorithm over all 6
> regions.

The proof does not invoke injectivity or pairwise distinctness of the assigned permutations in this
assembly step.

## Constituent stage

In `constituent.tex`, lines 153–170, each interface-tensor term is divided into six labelled regions,
and after zeroing the result is explicitly isomorphic to a tensor product over `r` and `t`. The proof
then analyzes the first region. At line 497 it concludes:

> The above algorithm was described for the first region; the algorithm for other regions is
> identical except that we permute the roles of the X, Y, Z-dimensions. In the end, we take the
> tensor product over the output tensor of the algorithm over all 6 regions.

Again, no comparison between the permutations assigned to distinct labels occurs in the tensoring
step.

## Lean status

`RepeatedOrientationVerification/Regionwise.lean` proves the abstract theorem implied by these two
facts: for any monoidal extraction relation preserved by orientation, an arbitrary function from
region labels to orientations is valid. The function need not be injective; a corollary specializes
to six copies of one orientation.

This is not yet a formal instantiation with the actual tensors and hashing algorithms of the paper.
Completing that instantiation would require formal definitions of tensor restriction, degeneration,
direct sums, interface tensors, typicality, hashing, and the asymptotic estimates used by the
published proof. The current Lean development therefore verifies the algebraic repeated-label step
but does not yet formalize the full laser-method extraction theorem.
