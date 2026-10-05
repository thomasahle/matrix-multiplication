/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedProductReindex
import AlgebraicComplexity.Tensor.PartitionedProductRealization

/-!
# External products of partitioned tensors

This stable facade re-exports the finite product support, block-reindexing laws, and direct-sum
realization theorem.  Their proof environments are split so clients needing only constituent data
do not load reindexing or direct-sum tensor-product machinery.
-/
