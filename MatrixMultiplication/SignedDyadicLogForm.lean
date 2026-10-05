/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SignedDyadicLogFormNormalize

/-!
# Signed dyadic log-linear forms

Compatibility umbrella for the real evaluation, additive algebra, and normalization laws of
exact signed dyadic logarithm forms.  The implementation is split into smaller proof modules so
clients that do not normalize forms need not load the normalization induction.
-/
