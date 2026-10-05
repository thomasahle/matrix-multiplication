import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk5Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 65; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk5.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 83884754940516255053905920 }, { target := 27, numerator := 2298475406948363796807155712 }, { target := 29, numerator := 24482018499328704258949251072 }, { target := 37, numerator := 2304660425870411836560506880 }, { target := 44, numerator := 77691019813673897318940672 }, { target := 80, numerator := 114268855097567385585975296 }, { target := 82, numerator := 3884904368819256827907670016 }, { target := 85, numerator := 3884911381260520715915886592 }, { target := 92, numerator := 114272509455664822641229824 }, { target := 131, numerator := 58220125554794211982704640 }, { target := 134, numerator := 206835875793992900883251200 }, { target := 136, numerator := 58142760738811405559398400 }, { target := 157, numerator := 286710877895431593457090560 }, { target := 158, numerator := 7855991261040561595892105216 }, { target := 160, numerator := 83677433659693905845153693696 }, { target := 168, numerator := 7877131123774829910388899840 }, { target := 175, numerator := 265541223922811717074026496 }, { target := 176, numerator := 3840790670325289157440569344 }, { target := 178, numerator := 130809051330972817236252688384 }, { target := 181, numerator := 130809289881534619374267138048 }, { target := 188, numerator := 3840909797266062750164975616 }, { target := 227, numerator := 2175299205467430005598322688 }, { target := 230, numerator := 7728082205068050241201111040 }, { target := 232, numerator := 2172408596401667272112865280 }, { target := 267, numerator := 83884917475426806855106560 }, { target := 268, numerator := 2298479860469089210850082816 }, { target := 270, numerator := 24482065935632115261606199296 }, { target := 278, numerator := 2304664891375215859036323840 }, { target := 285, numerator := 77691170347617342084612096 }, { target := 286, numerator := 3840790752678674893490880512 }, { target := 288, numerator := 130809037081484517044201193472 }, { target := 291, numerator := 130809275631840279499263442944 }, { target := 298, numerator := 3840909879896419863298572288 }, { target := 302, numerator := 24083794459314967670442426368 }, { target := 305, numerator := 85561353088231631295547965440 }, { target := 307, numerator := 24051791121830594887108526080 }, { target := 573, numerator := 114274141165541864360640512 }, { target := 575, numerator := 3885083254795853335837540352 }, { target := 578, numerator := 3885090267551243297854849024 }, { target := 585, numerator := 114277795706035086324400128 }, { target := 589, numerator := 2168347497898263168948371456 }, { target := 592, numerator := 7703385203650918301019668480 }, { target := 594, numerator := 2165466126489955308257935360 }, { target := 763, numerator := 58220125554794211982704640 }, { target := 766, numerator := 206835875793992900883251200 }, { target := 768, numerator := 58142760738811405559398400 }]

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
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left3.expected,
    Slot15.Left11.expected,
    Slot15.Left18.expected,
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot20.Left5.expected,
    Slot20.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 58220125554794211982704640 }, { target := 27, numerator := 2175299205467430005598322688 }, { target := 29, numerator := 24083794459314967670442426368 }, { target := 37, numerator := 2168347497898263168948371456 }, { target := 44, numerator := 58220125554794211982704640 }, { target := 80, numerator := 28425786532872726329163776 }, { target := 82, numerator := 1010907172358055663453077504 }, { target := 85, numerator := 1010903083725164508455370752 }, { target := 92, numerator := 28426901614570314055811072 }, { target := 131, numerator := 83884754940516255053905920 }, { target := 134, numerator := 286710877895431593457090560 }, { target := 136, numerator := 83884917475426806855106560 }, { target := 157, numerator := 206835875793992900883251200 }, { target := 158, numerator := 7728082205068050241201111040 }, { target := 160, numerator := 85561353088231631295547965440 }, { target := 168, numerator := 7703385203650918301019668480 }, { target := 175, numerator := 206835875793992900883251200 }, { target := 176, numerator := 1055020870852023333920178176 }, { target := 178, numerator := 37519741594427867087035695104 }, { target := 181, numerator := 37519589845134019679907479552 }, { target := 188, numerator := 1055062257023072626773327872 }, { target := 227, numerator := 2298475406948363796807155712 }, { target := 230, numerator := 7855991261040561595892105216 }, { target := 232, numerator := 2298479860469089210850082816 }, { target := 267, numerator := 58142760738811405559398400 }, { target := 268, numerator := 2172408596401667272112865280 }, { target := 270, numerator := 24051791121830594887108526080 }, { target := 278, numerator := 2165466126489955308257935360 }, { target := 285, numerator := 58142760738811405559398400 }, { target := 286, numerator := 1055023712307010330880376832 }, { target := 288, numerator := 37519842645184122009973424128 }, { target := 291, numerator := 37519690895481572936661336064 }, { target := 298, numerator := 1055065098589523714510946304 }, { target := 302, numerator := 24482018499328704258949251072 }, { target := 305, numerator := 83677433659693905845153693696 }, { target := 307, numerator := 24482065935632115261606199296 }, { target := 573, numerator := 28425269904693272336400384 }, { target := 575, numerator := 1010888799493282041100763136 }, { target := 578, numerator := 1010884710934700279954669568 }, { target := 585, numerator := 28426384966124661739880448 }, { target := 589, numerator := 2304660425870411836560506880 }, { target := 592, numerator := 7877131123774829910388899840 }, { target := 594, numerator := 2304664891375215859036323840 }, { target := 763, numerator := 77691019813673897318940672 }, { target := 766, numerator := 265541223922811717074026496 }, { target := 768, numerator := 77691170347617342084612096 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk5.Parent2
