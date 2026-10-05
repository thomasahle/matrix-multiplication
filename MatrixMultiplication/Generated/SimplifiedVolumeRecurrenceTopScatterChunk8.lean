import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometry

/-! Exact sparse top-entry child scatter; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk8

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.Generated.SimplifiedVolumeRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def expectedEntries : List TopScatterEntry := [
    ⟨133, 205, 115⟩, ⟨133, 211, 47⟩, ⟨133, 217, 106⟩, ⟨133, 223, 110⟩,
    ⟨133, 229, 49⟩, ⟨133, 235, 5⟩, ⟨133, 241, 8⟩, ⟨133, 247, 6⟩,
    ⟨133, 253, 1⟩, ⟨133, 259, 1⟩, ⟨133, 265, 1⟩, ⟨139, 19, 3⟩,
    ⟨139, 25, 6⟩, ⟨139, 31, 3⟩, ⟨139, 67, 6⟩, ⟨139, 73, 26⟩,
    ⟨139, 79, 27⟩, ⟨139, 85, 6⟩, ⟨139, 109, 6⟩, ⟨139, 115, 41⟩,
    ⟨139, 121, 67⟩, ⟨139, 127, 40⟩, ⟨139, 133, 6⟩, ⟨139, 145, 3⟩,
    ⟨139, 151, 25⟩, ⟨139, 157, 68⟩, ⟨139, 163, 71⟩, ⟨139, 169, 27⟩,
    ⟨139, 181, 7⟩, ⟨139, 187, 25⟩, ⟨139, 193, 42⟩, ⟨139, 199, 27⟩,
    ⟨139, 211, 3⟩, ⟨139, 217, 6⟩, ⟨139, 223, 6⟩, ⟨145, 7, 1⟩,
    ⟨145, 13, 3⟩, ⟨145, 19, 22⟩, ⟨145, 25, 53⟩, ⟨145, 31, 22⟩,
    ⟨145, 37, 3⟩, ⟨145, 43, 1⟩, ⟨145, 61, 4⟩, ⟨145, 67, 48⟩,
    ⟨145, 73, 224⟩, ⟨145, 79, 215⟩, ⟨145, 85, 47⟩, ⟨145, 91, 3⟩,
    ⟨145, 97, 1⟩, ⟨145, 109, 46⟩, ⟨145, 115, 341⟩, ⟨145, 121, 592⟩,
    ⟨145, 127, 336⟩, ⟨145, 133, 47⟩, ⟨145, 139, 3⟩, ⟨145, 151, 218⟩,
    ⟨145, 157, 586⟩, ⟨145, 163, 595⟩, ⟨145, 169, 216⟩, ⟨145, 175, 20⟩,
    ⟨145, 187, 225⟩, ⟨145, 193, 350⟩, ⟨145, 199, 225⟩, ⟨145, 205, 52⟩,
    ⟨145, 217, 49⟩, ⟨145, 223, 49⟩, ⟨145, 229, 22⟩, ⟨145, 241, 4⟩,
    ⟨145, 247, 3⟩, ⟨145, 259, 1⟩, ⟨151, 1, 3⟩, ⟨151, 7, 5⟩,
    ⟨151, 13, 26⟩, ⟨151, 19, 221⟩, ⟨151, 25, 545⟩, ⟨151, 31, 206⟩,
    ⟨151, 37, 25⟩, ⟨151, 43, 5⟩, ⟨151, 49, 3⟩, ⟨151, 55, 4⟩,
    ⟨151, 61, 35⟩, ⟨151, 67, 473⟩, ⟨151, 73, 2322⟩, ⟨151, 79, 2205⟩,
    ⟨151, 85, 456⟩, ⟨151, 91, 31⟩, ⟨151, 97, 5⟩, ⟨151, 103, 25⟩,
    ⟨151, 109, 468⟩, ⟨151, 115, 3418⟩, ⟨151, 121, 5738⟩, ⟨151, 127, 3241⟩,
    ⟨151, 133, 436⟩, ⟨151, 139, 25⟩, ⟨151, 145, 219⟩, ⟨151, 151, 2210⟩,
    ⟨151, 157, 5610⟩, ⟨151, 163, 5699⟩, ⟨151, 169, 2025⟩, ⟨151, 175, 200⟩,
    ⟨151, 181, 569⟩, ⟨151, 187, 2210⟩, ⟨151, 193, 3431⟩, ⟨151, 199, 2211⟩,
    ⟨151, 205, 482⟩, ⟨151, 211, 212⟩, ⟨151, 217, 479⟩, ⟨151, 223, 499⟩,
    ⟨151, 229, 214⟩, ⟨151, 235, 25⟩, ⟨151, 241, 34⟩, ⟨151, 247, 27⟩,
    ⟨151, 253, 4⟩, ⟨151, 259, 5⟩, ⟨151, 265, 3⟩, ⟨157, 1, 9⟩,
    ⟨157, 7, 12⟩, ⟨157, 13, 71⟩, ⟨157, 19, 591⟩, ⟨157, 25, 1533⟩,
    ⟨157, 31, 581⟩, ⟨157, 37, 69⟩, ⟨157, 43, 12⟩, ⟨157, 49, 9⟩,
    ⟨157, 55, 11⟩, ⟨157, 61, 90⟩, ⟨157, 67, 1329⟩, ⟨157, 73, 6276⟩
  ]

opaque recurrence_eq :
    topScatteredEntryRangeWithPairs generatedPrimaryTables
        PairGeometry.expectedIndices 1024 128 = expectedEntries := by
  unfold generatedPrimaryTables topChunks
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  decide

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatterChunk8
