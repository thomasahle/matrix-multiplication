import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk23Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 96; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk23.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left2.expected,
    Slot0.Left5.expected,
    Slot0.Left12.expected,
    Slot1.Left0.expected,
    Slot1.Left2.expected,
    Slot1.Left5.expected,
    Slot1.Left12.expected,
    Slot2.Left0.expected,
    Slot2.Left3.expected,
    Slot2.Left5.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected,
    Slot3.Left6.expected,
    Slot3.Left7.expected,
    Slot3.Left8.expected,
    Slot3.Left9.expected,
    Slot3.Left10.expected,
    Slot3.Left11.expected,
    Slot3.Left12.expected,
    Slot3.Left13.expected,
    Slot3.Left14.expected,
    Slot3.Left15.expected,
    Slot4.Left0.expected,
    Slot4.Left3.expected,
    Slot4.Left5.expected,
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot6.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 2030995376952577013506375680 }, { target := 17, numerator := 36151717709755870840413487104 }, { target := 18, numerator := 2030995376952577013506375680 }, { target := 19, numerator := 32157426801749136047184281600 }, { target := 20, numerator := 54904575023617998598455689216 }, { target := 21, numerator := 2030995376952577013506375680 }, { target := 22, numerator := 54904575023617998598455689216 }, { target := 23, numerator := 54904575023617998598455689216 }, { target := 24, numerator := 36151717709755870840413487104 }, { target := 25, numerator := 2030995376952577013506375680 }, { target := 26, numerator := 85368370741977518820888150016 }, { target := 27, numerator := 29701079998924770615301767168 }, { target := 28, numerator := 85368370741977518820888150016 }, { target := 29, numerator := 29701079998924770615301767168 }, { target := 44, numerator := 15295102796173110575412281344 }, { target := 49, numerator := 2205080694977083614664065024 }, { target := 50, numerator := 2030995376952577013506375680 }, { target := 51, numerator := 36151717709755870840413487104 }, { target := 52, numerator := 2030995376952577013506375680 }, { target := 53, numerator := 32157426801749136047184281600 }, { target := 54, numerator := 54904575023617998598455689216 }, { target := 55, numerator := 2030995376952577013506375680 }, { target := 56, numerator := 54904575023617998598455689216 }, { target := 57, numerator := 54904575023617998598455689216 }, { target := 58, numerator := 36151717709755870840413487104 }, { target := 59, numerator := 2030995376952577013506375680 }, { target := 60, numerator := 299719177960183066432062357504 }, { target := 61, numerator := 108029230315498140949503016960 }, { target := 62, numerator := 299719177960183066432062357504 }, { target := 63, numerator := 108029230315498140949503016960 }, { target := 64, numerator := 503227688346376718006163079168 }, { target := 69, numerator := 17350503363109157915383037952 }, { target := 70, numerator := 2089023816294079213892272128 }, { target := 71, numerator := 83337356475559010328800919552 }, { target := 72, numerator := 29701079998924770615301767168 }, { target := 73, numerator := 83337356475559010328800919552 }, { target := 74, numerator := 29701079998924770615301767168 }, { target := 75, numerator := 503204293742820581783774429184 }, { target := 76, numerator := 2089023816294079213892272128 }, { target := 91, numerator := 2089023816294079213892272128 }, { target := 96, numerator := 89479853464596392995052322816 }, { target := 97, numerator := 2089023816294079213892272128 }, { target := 102, numerator := 17350503363109157915383037952 }, { target := 103, numerator := 89479853464596392995052322816 }, { target := 104, numerator := 15318497399729246797800931328 }, { target := 109, numerator := 2089023816294079213892272128 }, { target := 110, numerator := 2089023816294079213892272128 }, { target := 111, numerator := 2205080694977083614664065024 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk0

namespace RouteChunk1

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left1.expected,
    Slot6.Left2.expected,
    Slot6.Left3.expected,
    Slot6.Left4.expected,
    Slot6.Left5.expected,
    Slot6.Left6.expected,
    Slot6.Left7.expected,
    Slot6.Left8.expected,
    Slot6.Left9.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot8.Left0.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left2.expected,
    Slot9.Left3.expected,
    Slot10.Left0.expected,
    Slot11.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 16322104169401669537906032640 }, { target := 1, numerator := 2205080694977083614664065024 }, { target := 2, numerator := 541814768230280327840441303040 }, { target := 3, numerator := 17350503363109157915383037952 }, { target := 4, numerator := 2089023816294079213892272128 }, { target := 5, numerator := 541788455204237778177310588928 }, { target := 6, numerator := 2089023816294079213892272128 }, { target := 7, numerator := 2089023816294079213892272128 }, { target := 8, numerator := 89479853464596392995052322816 }, { target := 9, numerator := 2089023816294079213892272128 }, { target := 10, numerator := 17350503363109157915383037952 }, { target := 11, numerator := 89479853464596392995052322816 }, { target := 12, numerator := 16348417195444219201036746752 }, { target := 13, numerator := 2089023816294079213892272128 }, { target := 14, numerator := 2089023816294079213892272128 }, { target := 15, numerator := 2205080694977083614664065024 }, { target := 16, numerator := 83337375365024941807381774336 }, { target := 19, numerator := 299719177960183066432062357504 }, { target := 21, numerator := 83337356475559010328800919552 }, { target := 30, numerator := 29701079998924770615301767168 }, { target := 33, numerator := 108029230315498140949503016960 }, { target := 35, numerator := 29701079998924770615301767168 }, { target := 40, numerator := 36151717709755870840413487104 }, { target := 42, numerator := 36151717709755870840413487104 }, { target := 45, numerator := 2030995376952577013506375680 }, { target := 47, numerator := 2030995376952577013506375680 }, { target := 50, numerator := 83337375365024941807381774336 }, { target := 53, numerator := 299719177960183066432062357504 }, { target := 55, numerator := 83337356475559010328800919552 }, { target := 60, numerator := 32157426801749136047184281600 }, { target := 62, numerator := 32157426801749136047184281600 }, { target := 65, numerator := 54904575023617998598455689216 }, { target := 67, numerator := 54904575023617998598455689216 }, { target := 71, numerator := 2030995376952577013506375680 }, { target := 73, numerator := 2030995376952577013506375680 }, { target := 77, numerator := 29701079998924770615301767168 }, { target := 80, numerator := 108029230315498140949503016960 }, { target := 82, numerator := 29701079998924770615301767168 }, { target := 87, numerator := 54904575023617998598455689216 }, { target := 89, numerator := 54904575023617998598455689216 }, { target := 92, numerator := 54904575023617998598455689216 }, { target := 94, numerator := 54904575023617998598455689216 }, { target := 98, numerator := 36151717709755870840413487104 }, { target := 100, numerator := 36151717709755870840413487104 }, { target := 105, numerator := 2030995376952577013506375680 }, { target := 107, numerator := 2030995376952577013506375680 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk23.Parent2
