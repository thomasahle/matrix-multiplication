/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.SimplifiedVolumeSchemaDefs

set_option autoImplicit false

/-!
# Canonical legal-hybrid q20 primary-data provenance

This manifest pins the isolated top-law source image for the Total-Weight candidate described in
`better_bound/paper.tex:148-159`. The other six primary fields and the categorical factors are
the existing repository objects named below.  The q20 support and numerators are self-contained in
matched blocks capped at 200 entries, and the untrusted generator requires the
ordered support to equal 90df exactly before rendering.  No semantic bridge, logarithmic bound,
restriction, or endpoint is asserted here.

The downstream ordered-child laws follow [alman2025more],
`papers/sources/2404.16349/constituent.tex:41-47`; the q20 data are this project's own candidate.
The strings record provenance of the original exporter image, before documentation and layout
cleanup. They are not assertions that the present source files retain those original byte hashes.
-/

namespace MatrixMultiplication.Generated.LegalHybridQ20Primary.Manifest

/-- Version tag for the original primary-data export boundary. -/
def schema : String := "legal-hybrid-q20-primary-lean-boundary-v1"

/-- Digest identifying the q20 candidate used by the exporter. -/
def candidateSHA256 : String := "0e8355da17679e855c12f0a2cdf53d53709417e8508c9941be8920456cc43b8d"

/-- Digest identifying the predecessor whose ordered support was retained. -/
def legacyCandidateSHA256 : String :=
  "90dfb5ea1f9560845093afcf88dc12d11af836d3b34983886f0e915729bbfb8d"

/-- Digest of the original candidate archive. -/
def archiveSHA256 : String := "1087c436aa466c3185770dad7e53a50b260460dcb712645776c319a81197bb7b"

/-- Digest of the static table used in the original export. -/
def staticTableSHA256 : String := "9d3a6eb6ee490e4cb3fff9f4bea1667ab24b5459457a71497298d61e121562cd"

/-- Digest of the exporter that produced the original source image. -/
def exporterSHA256 : String := "9112f21f68709d36c7af9939923fe1b3687f4bf068c20e6e62b13cc6f4f96e9a"

/-- Digest of the original base renderer. -/
def baseRendererSHA256 : String :=
  "d8421785be7784df8a00f6c8a9bb151047af3e8cfad89146117c4ed4cb06b766"

/-- Digest of the archive loader used by that renderer. -/
def archiveLoaderSHA256 : String :=
  "31f92b3875a4fca8729d3a545afe985cb9c12807c775dcfdc0ffba1b72e119a6"

/-- Digest of the array helper source in the original, pre-cleanup export image. -/
def arrayCoreSHA256 : String := "bc005e8cc63b82b898d79fa618f570fee3792903ed7febf1e2873dd9498f1d35"

/-- Digest of the existing primary source set named by the original export. -/
def existingPrimarySourceSetSHA256 : String :=
  "6457cd9818314d7d1787a8eed57d86432672c125dd43203433e60d08c6c918e3"

/-- Digest of the existing sparse categorical factors named by the export. -/
def existingSparseFactorsSHA256 : String :=
  "94f9d300aaab3ffe03b6f1faccd37dbc901d799f60938879e521976d8c2ac486"

/-- Digest of the common ordered top support checked by the untrusted exporter. -/
def orderedTopSupportSHA256 : String :=
  "5f2fd1544082df747938a20e1de8b59c00eb3e915f23ea93c06baa70cc910fcf"

/-- Literal coarsening specification recorded in the candidate provenance. -/
def coarseningSpecification : String := "2:1=0|0;2:2=0|0|0;2:3=0|0"

/-- Binary denominator exponent of the top-law mass table. -/
def topProbabilityBits : Nat := 20

/-- Exporter's recorded number of positive top-law entries. -/
def activeTopValues : Nat := 2244

/-- Exporter's recorded number of positive entries across all primary fields. -/
def activePrimaryValues : Nat := 31315

/-- Maximum number of entries in an individual generated data block. -/
def dataBlockLimit : Nat := 200

/-- Number of bounded data blocks in the original top-law export. -/
def dataBlockCount : Nat := 12

/-- Number of finite checks recorded for each individual data block. -/
def decisionsPerDataBlock : Nat := 6

/-- Number of finite checks recorded for the block-append boundaries. -/
def appendBoundaryDecisionCount : Nat := 20

/-- Total finite-check count expected by the exporter; this is provenance, not a census theorem. -/
def expectedKernelDecisionCount : Nat := 93

end MatrixMultiplication.Generated.LegalHybridQ20Primary.Manifest
