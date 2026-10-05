import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk0Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 3; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 61, numerator := 19975373873630154850304000 }, { target := 62, numerator := 1672520773586850689738342400 }, { target := 67, numerator := 1672521378870640608333004800 }, { target := 75, numerator := 19974768589840236255641600 }, { target := 132, numerator := 400306492427548303200092160 }, { target := 133, numerator := 33517316302680487822356381696 }, { target := 138, numerator := 33517328432567637790993416192 }, { target := 146, numerator := 400294362540398334563057664 }, { target := 177, numerator := 671971577108918409164226560 }, { target := 178, numerator := 56263598823461657202797838336 }, { target := 183, numerator := 56263619185208350064322281472 }, { target := 191, numerator := 671951215362225547639783424 }, { target := 203, numerator := 644805068640781398567813120 }, { target := 204, numerator := 53988970571383540264753692672 }, { target := 209, numerator := 53988990109944278836989394944 }, { target := 217, numerator := 644785530080042826332110848 }, { target := 219, numerator := 77120130010731831413964800 }, { target := 220, numerator := 8085906540292612992217907200 }, { target := 222, numerator := 87157990650275518060953600000 }, { target := 230, numerator := 8085912708422662638849228800 }, { target := 237, numerator := 77120130010731831413964800 }, { target := 272, numerator := 19975373873630154850304000 }, { target := 273, numerator := 1672520773586850689738342400 }, { target := 278, numerator := 1672521378870640608333004800 }, { target := 286, numerator := 19974768589840236255641600 }, { target := 317, numerator := 644805068640781398567813120 }, { target := 318, numerator := 53988970571383540264753692672 }, { target := 323, numerator := 53988990109944278836989394944 }, { target := 331, numerator := 644785530080042826332110848 }, { target := 343, numerator := 430669060715466138572554240 }, { target := 344, numerator := 36059547878532500870758662144 }, { target := 349, numerator := 36059560928451011515659583488 }, { target := 357, numerator := 430656010796955493671632896 }, { target := 359, numerator := 70489240327566103853137920 }, { target := 360, numerator := 7390669716267453744288890880 }, { target := 362, numerator := 79664032575672389405245440000 }, { target := 370, numerator := 7390675354053611271770603520 }, { target := 377, numerator := 70489240327566103853137920 }, { target := 392, numerator := 20774388828575361044316160 }, { target := 393, numerator := 1739421604530324717327876096 }, { target := 398, numerator := 1739422234025466232666324992 }, { target := 406, numerator := 20773759333433845705867264 }, { target := 418, numerator := 400306492427548303200092160 }, { target := 419, numerator := 33517316302680487822356381696 }, { target := 424, numerator := 33517328432567637790993416192 }, { target := 432, numerator := 400294362540398334563057664 }, { target := 434, numerator := 77120130010731831413964800 }, { target := 435, numerator := 8085906540292612992217907200 }, { target := 437, numerator := 87157990650275518060953600000 }, { target := 445, numerator := 8085912708422662638849228800 }, { target := 452, numerator := 77120130010731831413964800 }, { target := 453, numerator := 19176358918684948656291840 }, { target := 454, numerator := 1605619942643376662148808704 }, { target := 459, numerator := 1605620523715814983999684608 }, { target := 467, numerator := 19175777846246626805415936 }, { target := 469, numerator := 70489240327566103853137920 }, { target := 470, numerator := 7390669716267453744288890880 }, { target := 472, numerator := 79664032575672389405245440000 }, { target := 480, numerator := 7390675354053611271770603520 }, { target := 487, numerator := 70489240327566103853137920 }, { target := 488, numerator := 3301401685807686099249659904 }, { target := 490, numerator := 115540827918489371682130624512 }, { target := 493, numerator := 115540884586887166117873188864 }, { target := 500, numerator := 3301373351608788881378377728 }]

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
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 2, numerator := 29014219670751100192948224 }, { target := 3, numerator := 29014219670751100192948224 }, { target := 4, numerator := 29014219670751100192948224 }, { target := 5, numerator := 29014219670751100192948224 }, { target := 8, numerator := 773712524553362671811952640 }, { target := 9, numerator := 773712524553362671811952640 }, { target := 10, numerator := 773712524553362671811952640 }, { target := 11, numerator := 773712524553362671811952640 }, { target := 13, numerator := 739862601604153054920179712 }, { target := 14, numerator := 739862601604153054920179712 }, { target := 15, numerator := 739862601604153054920179712 }, { target := 16, numerator := 739862601604153054920179712 }, { target := 17, numerator := 231728298813530585180405760 }, { target := 19, numerator := 2244537238309708180981022720 }, { target := 24, numerator := 231728298813530585180405760 }, { target := 28, numerator := 24178516392292583494123520 }, { target := 29, numerator := 24178516392292583494123520 }, { target := 30, numerator := 24178516392292583494123520 }, { target := 31, numerator := 24178516392292583494123520 }, { target := 37, numerator := 238349107351060030471274496 }, { target := 39, numerator := 2308666873689985557580480512 }, { target := 44, numerator := 238349107351060030471274496 }, { target := 51, numerator := 231728298813530585180405760 }, { target := 53, numerator := 2244537238309708180981022720 }, { target := 58, numerator := 231728298813530585180405760 }, { target := 88, numerator := 205245064663412804016930816 }, { target := 90, numerator := 1988018696788598674583191552 }, { target := 95, numerator := 205245064663412804016930816 }, { target := 108, numerator := 9606793187955225117050535936 }, { target := 110, numerator := 93052100936782473445813256192 }, { target := 115, numerator := 9606793187955225117050535936 }, { target := 122, numerator := 2615219372324130889893150720 }, { target := 124, numerator := 25331205975209563756785827840 }, { target := 129, numerator := 2615219372324130889893150720 }, { target := 153, numerator := 238349107351060030471274496 }, { target := 155, numerator := 2308666873689985557580480512 }, { target := 160, numerator := 238349107351060030471274496 }, { target := 167, numerator := 9606793187955225117050535936 }, { target := 169, numerator := 93052100936782473445813256192 }, { target := 174, numerator := 9606793187955225117050535936 }, { target := 193, numerator := 231728298813530585180405760 }, { target := 195, numerator := 2244537238309708180981022720 }, { target := 200, numerator := 231728298813530585180405760 }, { target := 248, numerator := 231728298813530585180405760 }, { target := 250, numerator := 2244537238309708180981022720 }, { target := 255, numerator := 231728298813530585180405760 }, { target := 262, numerator := 198624256125883358726062080 }, { target := 264, numerator := 1923889061408321297983733760 }, { target := 269, numerator := 198624256125883358726062080 }, { target := 293, numerator := 231728298813530585180405760 }, { target := 295, numerator := 2244537238309708180981022720 }, { target := 300, numerator := 231728298813530585180405760 }, { target := 307, numerator := 2615219372324130889893150720 }, { target := 309, numerator := 25331205975209563756785827840 }, { target := 314, numerator := 2615219372324130889893150720 }, { target := 333, numerator := 198624256125883358726062080 }, { target := 335, numerator := 1923889061408321297983733760 }, { target := 340, numerator := 198624256125883358726062080 }, { target := 382, numerator := 231728298813530585180405760 }, { target := 384, numerator := 2244537238309708180981022720 }, { target := 389, numerator := 231728298813530585180405760 }, { target := 408, numerator := 205245064663412804016930816 }, { target := 410, numerator := 1988018696788598674583191552 }, { target := 415, numerator := 205245064663412804016930816 }]

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

namespace RouteChunk2

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot4.Left4.expected,
    Slot4.Left5.expected,
    Slot4.Left6.expected,
    Slot4.Left7.expected,
    Slot4.Left8.expected,
    Slot4.Left9.expected,
    Slot4.Left10.expected,
    Slot4.Left11.expected,
    Slot4.Left12.expected,
    Slot4.Left13.expected,
    Slot4.Left14.expected,
    Slot4.Left15.expected,
    Slot4.Left16.expected,
    Slot4.Left17.expected,
    Slot4.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 33, numerator := 759205414717987121715478528 }, { target := 34, numerator := 759205414717987121715478528 }, { target := 35, numerator := 759205414717987121715478528 }, { target := 36, numerator := 759205414717987121715478528 }, { target := 47, numerator := 24178516392292583494123520 }, { target := 48, numerator := 24178516392292583494123520 }, { target := 49, numerator := 24178516392292583494123520 }, { target := 50, numerator := 24178516392292583494123520 }, { target := 79, numerator := 739862601604153054920179712 }, { target := 80, numerator := 739862601604153054920179712 }, { target := 81, numerator := 739862601604153054920179712 }, { target := 82, numerator := 739862601604153054920179712 }, { target := 84, numerator := 420706185225890952797749248 }, { target := 85, numerator := 420706185225890952797749248 }, { target := 86, numerator := 420706185225890952797749248 }, { target := 87, numerator := 420706185225890952797749248 }, { target := 99, numerator := 759205414717987121715478528 }, { target := 100, numerator := 759205414717987121715478528 }, { target := 101, numerator := 759205414717987121715478528 }, { target := 102, numerator := 759205414717987121715478528 }, { target := 104, numerator := 11852308735501824428819349504 }, { target := 105, numerator := 11852308735501824428819349504 }, { target := 106, numerator := 11852308735501824428819349504 }, { target := 107, numerator := 11852308735501824428819349504 }, { target := 118, numerator := 464227514732017603087171584 }, { target := 119, numerator := 464227514732017603087171584 }, { target := 120, numerator := 464227514732017603087171584 }, { target := 121, numerator := 464227514732017603087171584 }, { target := 149, numerator := 773712524553362671811952640 }, { target := 150, numerator := 773712524553362671811952640 }, { target := 151, numerator := 773712524553362671811952640 }, { target := 152, numerator := 773712524553362671811952640 }, { target := 163, numerator := 739862601604153054920179712 }, { target := 164, numerator := 739862601604153054920179712 }, { target := 165, numerator := 739862601604153054920179712 }, { target := 166, numerator := 739862601604153054920179712 }, { target := 239, numerator := 24178516392292583494123520 }, { target := 240, numerator := 24178516392292583494123520 }, { target := 241, numerator := 24178516392292583494123520 }, { target := 242, numerator := 24178516392292583494123520 }, { target := 244, numerator := 464227514732017603087171584 }, { target := 245, numerator := 464227514732017603087171584 }, { target := 246, numerator := 464227514732017603087171584 }, { target := 247, numerator := 464227514732017603087171584 }, { target := 258, numerator := 24178516392292583494123520 }, { target := 259, numerator := 24178516392292583494123520 }, { target := 260, numerator := 24178516392292583494123520 }, { target := 261, numerator := 24178516392292583494123520 }, { target := 289, numerator := 744698304882611571619004416 }, { target := 290, numerator := 744698304882611571619004416 }, { target := 291, numerator := 744698304882611571619004416 }, { target := 292, numerator := 744698304882611571619004416 }, { target := 303, numerator := 420706185225890952797749248 }, { target := 304, numerator := 420706185225890952797749248 }, { target := 305, numerator := 420706185225890952797749248 }, { target := 306, numerator := 420706185225890952797749248 }, { target := 378, numerator := 29014219670751100192948224 }, { target := 379, numerator := 29014219670751100192948224 }, { target := 380, numerator := 29014219670751100192948224 }, { target := 381, numerator := 29014219670751100192948224 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk2

namespace RouteChunk3

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 219, numerator := 29014219670751100192948224 }, { target := 220, numerator := 773712524553362671811952640 }, { target := 221, numerator := 739862601604153054920179712 }, { target := 222, numerator := 24178516392292583494123520 }, { target := 223, numerator := 759205414717987121715478528 }, { target := 224, numerator := 24178516392292583494123520 }, { target := 225, numerator := 739862601604153054920179712 }, { target := 226, numerator := 420706185225890952797749248 }, { target := 227, numerator := 759205414717987121715478528 }, { target := 228, numerator := 11852308735501824428819349504 }, { target := 229, numerator := 464227514732017603087171584 }, { target := 230, numerator := 773712524553362671811952640 }, { target := 231, numerator := 739862601604153054920179712 }, { target := 232, numerator := 24178516392292583494123520 }, { target := 233, numerator := 464227514732017603087171584 }, { target := 234, numerator := 24178516392292583494123520 }, { target := 235, numerator := 744698304882611571619004416 }, { target := 236, numerator := 420706185225890952797749248 }, { target := 237, numerator := 29014219670751100192948224 }, { target := 359, numerator := 29014219670751100192948224 }, { target := 360, numerator := 773712524553362671811952640 }, { target := 361, numerator := 739862601604153054920179712 }, { target := 362, numerator := 24178516392292583494123520 }, { target := 363, numerator := 759205414717987121715478528 }, { target := 364, numerator := 24178516392292583494123520 }, { target := 365, numerator := 739862601604153054920179712 }, { target := 366, numerator := 420706185225890952797749248 }, { target := 367, numerator := 759205414717987121715478528 }, { target := 368, numerator := 11852308735501824428819349504 }, { target := 369, numerator := 464227514732017603087171584 }, { target := 370, numerator := 773712524553362671811952640 }, { target := 371, numerator := 739862601604153054920179712 }, { target := 372, numerator := 24178516392292583494123520 }, { target := 373, numerator := 464227514732017603087171584 }, { target := 374, numerator := 24178516392292583494123520 }, { target := 375, numerator := 744698304882611571619004416 }, { target := 376, numerator := 420706185225890952797749248 }, { target := 377, numerator := 29014219670751100192948224 }, { target := 434, numerator := 29014219670751100192948224 }, { target := 435, numerator := 773712524553362671811952640 }, { target := 436, numerator := 739862601604153054920179712 }, { target := 437, numerator := 24178516392292583494123520 }, { target := 438, numerator := 759205414717987121715478528 }, { target := 439, numerator := 24178516392292583494123520 }, { target := 440, numerator := 739862601604153054920179712 }, { target := 441, numerator := 420706185225890952797749248 }, { target := 442, numerator := 759205414717987121715478528 }, { target := 443, numerator := 11852308735501824428819349504 }, { target := 444, numerator := 464227514732017603087171584 }, { target := 445, numerator := 773712524553362671811952640 }, { target := 446, numerator := 739862601604153054920179712 }, { target := 447, numerator := 24178516392292583494123520 }, { target := 448, numerator := 464227514732017603087171584 }, { target := 449, numerator := 24178516392292583494123520 }, { target := 450, numerator := 744698304882611571619004416 }, { target := 451, numerator := 420706185225890952797749248 }, { target := 452, numerator := 29014219670751100192948224 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk3

namespace RouteChunk4

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot5.Left3.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 61, numerator := 231728298813530585180405760 }, { target := 62, numerator := 238349107351060030471274496 }, { target := 63, numerator := 231728298813530585180405760 }, { target := 64, numerator := 205245064663412804016930816 }, { target := 65, numerator := 9606793187955225117050535936 }, { target := 66, numerator := 2615219372324130889893150720 }, { target := 67, numerator := 238349107351060030471274496 }, { target := 68, numerator := 9606793187955225117050535936 }, { target := 69, numerator := 231728298813530585180405760 }, { target := 70, numerator := 231728298813530585180405760 }, { target := 71, numerator := 198624256125883358726062080 }, { target := 72, numerator := 231728298813530585180405760 }, { target := 73, numerator := 2615219372324130889893150720 }, { target := 74, numerator := 198624256125883358726062080 }, { target := 75, numerator := 231728298813530585180405760 }, { target := 76, numerator := 205245064663412804016930816 }, { target := 177, numerator := 2244537238309708180981022720 }, { target := 178, numerator := 2308666873689985557580480512 }, { target := 179, numerator := 2244537238309708180981022720 }, { target := 180, numerator := 1988018696788598674583191552 }, { target := 181, numerator := 93052100936782473445813256192 }, { target := 182, numerator := 25331205975209563756785827840 }, { target := 183, numerator := 2308666873689985557580480512 }, { target := 184, numerator := 93052100936782473445813256192 }, { target := 185, numerator := 2244537238309708180981022720 }, { target := 186, numerator := 2244537238309708180981022720 }, { target := 187, numerator := 1923889061408321297983733760 }, { target := 188, numerator := 2244537238309708180981022720 }, { target := 189, numerator := 25331205975209563756785827840 }, { target := 190, numerator := 1923889061408321297983733760 }, { target := 191, numerator := 2244537238309708180981022720 }, { target := 192, numerator := 1988018696788598674583191552 }, { target := 469, numerator := 29014219670751100192948224 }, { target := 470, numerator := 773712524553362671811952640 }, { target := 471, numerator := 739862601604153054920179712 }, { target := 472, numerator := 24178516392292583494123520 }, { target := 473, numerator := 759205414717987121715478528 }, { target := 474, numerator := 24178516392292583494123520 }, { target := 475, numerator := 739862601604153054920179712 }, { target := 476, numerator := 420706185225890952797749248 }, { target := 477, numerator := 759205414717987121715478528 }, { target := 478, numerator := 11852308735501824428819349504 }, { target := 479, numerator := 464227514732017603087171584 }, { target := 480, numerator := 773712524553362671811952640 }, { target := 481, numerator := 739862601604153054920179712 }, { target := 482, numerator := 24178516392292583494123520 }, { target := 483, numerator := 464227514732017603087171584 }, { target := 484, numerator := 24178516392292583494123520 }, { target := 485, numerator := 744698304882611571619004416 }, { target := 486, numerator := 420706185225890952797749248 }, { target := 487, numerator := 29014219670751100192948224 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk4

namespace RouteChunk5

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left7.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 2, numerator := 77120130010731831413964800 }, { target := 3, numerator := 70489240327566103853137920 }, { target := 4, numerator := 77120130010731831413964800 }, { target := 5, numerator := 70489240327566103853137920 }, { target := 8, numerator := 8085906540292612992217907200 }, { target := 9, numerator := 7390669716267453744288890880 }, { target := 10, numerator := 8085906540292612992217907200 }, { target := 11, numerator := 7390669716267453744288890880 }, { target := 17, numerator := 19975373873630154850304000 }, { target := 18, numerator := 400306492427548303200092160 }, { target := 19, numerator := 671971577108918409164226560 }, { target := 20, numerator := 644805068640781398567813120 }, { target := 21, numerator := 19975373873630154850304000 }, { target := 22, numerator := 644805068640781398567813120 }, { target := 23, numerator := 430669060715466138572554240 }, { target := 24, numerator := 20774388828575361044316160 }, { target := 25, numerator := 400306492427548303200092160 }, { target := 26, numerator := 19176358918684948656291840 }, { target := 37, numerator := 1672520773586850689738342400 }, { target := 38, numerator := 33517316302680487822356381696 }, { target := 39, numerator := 56263598823461657202797838336 }, { target := 40, numerator := 53988970571383540264753692672 }, { target := 41, numerator := 1672520773586850689738342400 }, { target := 42, numerator := 53988970571383540264753692672 }, { target := 43, numerator := 36059547878532500870758662144 }, { target := 44, numerator := 1739421604530324717327876096 }, { target := 45, numerator := 33517316302680487822356381696 }, { target := 46, numerator := 1605619942643376662148808704 }, { target := 153, numerator := 1672521378870640608333004800 }, { target := 154, numerator := 33517328432567637790993416192 }, { target := 155, numerator := 56263619185208350064322281472 }, { target := 156, numerator := 53988990109944278836989394944 }, { target := 157, numerator := 1672521378870640608333004800 }, { target := 158, numerator := 53988990109944278836989394944 }, { target := 159, numerator := 36059560928451011515659583488 }, { target := 160, numerator := 1739422234025466232666324992 }, { target := 161, numerator := 33517328432567637790993416192 }, { target := 162, numerator := 1605620523715814983999684608 }, { target := 382, numerator := 19974768589840236255641600 }, { target := 383, numerator := 400294362540398334563057664 }, { target := 384, numerator := 671951215362225547639783424 }, { target := 385, numerator := 644785530080042826332110848 }, { target := 386, numerator := 19974768589840236255641600 }, { target := 387, numerator := 644785530080042826332110848 }, { target := 388, numerator := 430656010796955493671632896 }, { target := 389, numerator := 20773759333433845705867264 }, { target := 390, numerator := 400294362540398334563057664 }, { target := 391, numerator := 19175777846246626805415936 }, { target := 392, numerator := 231728298813530585180405760 }, { target := 393, numerator := 238349107351060030471274496 }, { target := 394, numerator := 231728298813530585180405760 }, { target := 395, numerator := 205245064663412804016930816 }, { target := 396, numerator := 9606793187955225117050535936 }, { target := 397, numerator := 2615219372324130889893150720 }, { target := 398, numerator := 238349107351060030471274496 }, { target := 399, numerator := 9606793187955225117050535936 }, { target := 400, numerator := 231728298813530585180405760 }, { target := 401, numerator := 231728298813530585180405760 }, { target := 402, numerator := 198624256125883358726062080 }, { target := 403, numerator := 231728298813530585180405760 }, { target := 404, numerator := 2615219372324130889893150720 }, { target := 405, numerator := 198624256125883358726062080 }, { target := 406, numerator := 231728298813530585180405760 }, { target := 407, numerator := 205245064663412804016930816 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk5

namespace RouteChunk6

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 3301401685807686099249659904 }, { target := 6, numerator := 115540827918489371682130624512 }, { target := 27, numerator := 115540884586887166117873188864 }, { target := 28, numerator := 87157990650275518060953600000 }, { target := 29, numerator := 79664032575672389405245440000 }, { target := 30, numerator := 87157990650275518060953600000 }, { target := 31, numerator := 79664032575672389405245440000 }, { target := 148, numerator := 3301373351608788881378377728 }, { target := 149, numerator := 8085912708422662638849228800 }, { target := 150, numerator := 7390675354053611271770603520 }, { target := 151, numerator := 8085912708422662638849228800 }, { target := 152, numerator := 7390675354053611271770603520 }, { target := 378, numerator := 77120130010731831413964800 }, { target := 379, numerator := 70489240327566103853137920 }, { target := 380, numerator := 77120130010731831413964800 }, { target := 381, numerator := 70489240327566103853137920 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk6

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0.Parent2
