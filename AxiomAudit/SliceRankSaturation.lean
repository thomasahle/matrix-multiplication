/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.SliceRankSaturation

set_option autoImplicit false

/-!
# Axiom audit for the saturation step of the slice-rank degeneration proof

Focused trust audit for `AlgebraicComplexity/Tensor/SliceRankSaturation.lean`, the valuative
("saturation") half of Proposition 5.1 of J. Alman, *Limits on the Universal Method for Matrix
Multiplication*, PhD thesis, MIT, 2019 (quoting Corollary 2 of T. Tao and W. Sawin, *Notes on the
"slice rank" of tensors*, blog post, 2016).

The umbrella audit asserts the leading-term client `sliceRank_le_of_hasLeadingTerm`.  Asserted
here are the two remaining declarations the `README.md` Results row for this step names: the
monotonicity conclusion over a field, and the polynomial-linear-map existence lemma that the
saturation argument runs on.
-/

namespace AlgebraicComplexity.Tensor

#assert_axioms sliceRank_le_of_polynomialDegenerates
#assert_axioms exists_polynomialLinearMap_fixing_list

end AlgebraicComplexity.Tensor
