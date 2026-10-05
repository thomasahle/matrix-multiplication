/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.DomainWordShuffle

/-! Focused trust audit for the domain-general word transporters of [duan2023faster] §5: the
position permutation between two words with equal letter fibres, and the transporter/stabilizer
translation that makes the fibre count target-independent.

Exact source lines: `papers/sources/2210.10173/hole_lemma.tex:1-168` (§5).
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.WordShuffle.domainPermOfSameFiberCard
#assert_axioms AlgebraicComplexity.WordShuffle.domainPermOfSameFiberCard_map
#assert_axioms AlgebraicComplexity.WordShuffle.domainTransporter
#assert_axioms AlgebraicComplexity.WordShuffle.mem_domainTransporter
#assert_axioms AlgebraicComplexity.WordShuffle.card_domainTransporter_eq_card_stabilizer
