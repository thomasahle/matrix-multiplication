/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SegmentedAvailableWordNonempty

set_option autoImplicit false

/-! # Axiom audit for the existence of segmented available words

`[duan2023faster]`, `hole_lemma.tex`.

Exact source lines: `papers/sources/2210.10173/hole_lemma.tex:1-168` (whole file).
-/

#assert_axioms AlgebraicComplexity.exists_word_segmentMultiplicity
#assert_axioms AlgebraicComplexity.segmentedAvailableWord_nonempty
#assert_axioms AlgebraicComplexity.card_segmentedAvailableWord_pos
