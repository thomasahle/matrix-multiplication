/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Census
import AxiomAuditCertificate.LegalHybridQ20ModeSchedule
import AxiomAuditCertificate.LegalHybridQ20PrimaryArray
import AxiomAuditCertificate.LegalHybridQ20PrimaryData
import AxiomAuditCertificate.LegalHybridQ20PrimaryTopData0
import AxiomAuditCertificate.LegalHybridQ20PrimaryTopData1
import AxiomAuditCertificate.LegalHybridQ20Row44Top
import AxiomAuditCertificate.LegalHybridQ20Row44SlotProfile
import AxiomAuditCertificate.LegalHybridQ20Row44SplitType
import AxiomAuditCertificate.LegalHybridQ20Row44TopCorrespondence
import AxiomAuditCertificate.LegalHybridQ20Root0DualData
import AxiomAuditCertificate.LegalHybridQ20RootDualData

set_option autoImplicit false

/-!
# Enforcing axiom census for the q20 Total-Weight images

This is the second recognized certificate-tier census root, beside
`AxiomAuditCertificate/Census.lean`.  It exists because that root imports
`MatrixMultiplicationCertificate`, and so drags in the whole generated certificate library, which
has never been captured end to end; a census whose closure cannot be replayed is not evidence.
This root censuses the q20 Total-Weight companions together with the transitive providers they
need: the schedule, the primary top-data image, row 44's exact split profile and its correspondence
with the reconstructed top table, and the positive factors and exact integer partition totals
for the six canonical roots, together with their geometry and semantic providers. This registers
those finite inputs without importing the whole generated certificate library. It is
not a census of the companions alone: their transitive providers are inside its closure and are
audited by it.

It reaches `MatrixMultiplication/Generated/`, so it stays in the deliberately opt-in certificate
tier and the tier split is unchanged: the ordinary `AxiomAudit.CensusAll` closure remains
independent of every generated table. The explicit primary-data companion imports also run the
assertions in those supplied audits; importing only row 44's final correspondence companion would
not reach all of them. Both root-partition audits are explicit too: the six-root source imports
the root-zero source but not its focused audit. Further q20 companions join by adding their audit
import here as they are accepted, rather than by inventing another root. Each import enlarges the
closure by that companion's own providers.

`#axiom_census` walks `Environment.constants` and fails elaboration if any constant originating in
this repository is an `axiom`, or depends on one outside the allowlist.  That is the whole content
of this module.

**What this module does not assert.**  It is a trust-boundary check, not a mathematical claim.  It
does not assert that any schedule row realizes either reader, does not construct a tensor
restriction or degeneration, does not supply a hashing, repair-density or entropy inequality, does
not validate the q20 numerical certificate, and does not prove any exponent bound.  The audited
content is finite schedule and primary top data, row 44's exact counts, its split type and the
correspondence with the reconstructed top table. Row 44's raw mass is 1696; these facts do not
construct a supported fine reference, a selected CW input, or an extraction rate. The root
partition data verifies the arithmetic underlying `eq:partition` and `prop:dual` in
`better_bound/paper.tex:2274-2307`; it does not establish marginal matching, the full dual bound,
or the certificate's entropy inequalities. The surrounding programme is described in that paper.

```text
lake build AxiomAuditCertificate.CensusQ20
```

## References

- [duan2023faster] Ran Duan, Hongxun Wu, and Renfei Zhou, *Faster Matrix Multiplication via
  Asymmetric Hashing*.
- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

#axiom_census
