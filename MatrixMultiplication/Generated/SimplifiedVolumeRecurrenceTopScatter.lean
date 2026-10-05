import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceTopScatterChunk0
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceTopScatterChunk1
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceTopScatterChunk2
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceTopScatterChunk3
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceTopScatterChunk4
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceTopScatterChunk5
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceTopScatterChunk6
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceTopScatterChunk7
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceTopScatterChunk8
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceTopScatterChunk9
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceTopScatterChunk10
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceTopScatterChunk11
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceTopScatterChunk12
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceTopScatterChunk13
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceTopScatterChunk14
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceTopScatterChunk15
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceTopScatterChunk16
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceTopScatterChunk17
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceTopScatterChunk18

namespace MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatter

open MatrixMultiplication.SimplifiedVolumeReconstruction

def expectedEntries : List TopScatterEntry :=
  TopScatterChunk0.expectedEntries ++
    TopScatterChunk1.expectedEntries ++
    TopScatterChunk2.expectedEntries ++
    TopScatterChunk3.expectedEntries ++
    TopScatterChunk4.expectedEntries ++
    TopScatterChunk5.expectedEntries ++
    TopScatterChunk6.expectedEntries ++
    TopScatterChunk7.expectedEntries ++
    TopScatterChunk8.expectedEntries ++
    TopScatterChunk9.expectedEntries ++
    TopScatterChunk10.expectedEntries ++
    TopScatterChunk11.expectedEntries ++
    TopScatterChunk12.expectedEntries ++
    TopScatterChunk13.expectedEntries ++
    TopScatterChunk14.expectedEntries ++
    TopScatterChunk15.expectedEntries ++
    TopScatterChunk16.expectedEntries ++
    TopScatterChunk17.expectedEntries ++
    TopScatterChunk18.expectedEntries

theorem recurrence_eq :
    topScatteredEntriesWithPairs generatedPrimaryTables PairGeometry.expectedIndices =
      expectedEntries := by
  unfold topScatteredEntriesWithPairs expectedEntries
  rw [TopScatterChunk0.recurrence_eq, TopScatterChunk1.recurrence_eq, TopScatterChunk2.recurrence_eq, TopScatterChunk3.recurrence_eq, TopScatterChunk4.recurrence_eq, TopScatterChunk5.recurrence_eq, TopScatterChunk6.recurrence_eq, TopScatterChunk7.recurrence_eq, TopScatterChunk8.recurrence_eq, TopScatterChunk9.recurrence_eq, TopScatterChunk10.recurrence_eq, TopScatterChunk11.recurrence_eq, TopScatterChunk12.recurrence_eq, TopScatterChunk13.recurrence_eq, TopScatterChunk14.recurrence_eq, TopScatterChunk15.recurrence_eq, TopScatterChunk16.recurrence_eq, TopScatterChunk17.recurrence_eq, TopScatterChunk18.recurrence_eq]

end MatrixMultiplication.Generated.SimplifiedVolumeRecurrence.TopScatter
