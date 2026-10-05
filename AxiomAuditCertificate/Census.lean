/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Census
import AxiomAuditCertificate.CensusRoots
import MatrixMultiplicationCertificate

/-!
# Enforcing axiom census for the generated certificate cone

`AxiomAudit/CensusAll.lean` censuses the ordinary targets.  This module does the same for the
opt-in generated certificate umbrella, whose roughly 590 sealed `opaque … := by …` declarations
under `MatrixMultiplication/Generated/` are exactly the surface where a bodiless postulate would
be least visible to a reader.  `scripts/trust_scan.sh` checks the *shape* of those declarations
(an explicit body must appear before the next command); the census checks what the kernel
accepted.

`AxiomAuditCertificate.CensusRoots` extends this closure to the modules that are built only
because a focused audit imports them and that reach the generated tables; the roots which do not
reach them belong to `AxiomAudit.CensusRoots` instead, so the ordinary census stays independent of
this cone.

Kept out of the ordinary `AxiomAudit.*` target for the usual reason: this closure reconstructs
multi-thousand-entry numeral tables and belongs to the deliberately opt-in build.

```text
lake build AxiomAuditCertificate.Census
```
-/

#axiom_census
