import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk5Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 64; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk5.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 1307429047152558583610081280 }, { target := 37, numerator := 48367687575822039308390367232 }, { target := 40, numerator := 48367727792984726125429129216 }, { target := 47, numerator := 1307378350210366267415592960 }, { target := 86, numerator := 1775194226746508833550499840 }, { target := 89, numerator := 6304092336095531598933393408 }, { target := 91, numerator := 1774426952146175618640248832 }, { target := 122, numerator := 251095556437069504173834240 }, { target := 124, numerator := 251198954513360308980940800 }, { target := 145, numerator := 4686766466135760205831471104 }, { target := 147, numerator := 173309713565842108716138102784 }, { target := 150, numerator := 173309859970561155935368118272 }, { target := 157, numerator := 4686584449159875357944315904 }, { target := 161, numerator := 62443130469271724977853300736 }, { target := 164, numerator := 221815060494159202527593103360 }, { target := 166, numerator := 62414571827980300653535690752 }, { target := 197, numerator := 6068102866520525163447975936 }, { target := 199, numerator := 6070721288229966379776737280 }, { target := 216, numerator := 148281313340697721958301696 }, { target := 218, numerator := 7008830300803493241852788736 }, { target := 221, numerator := 7008789347599504925144383488 }, { target := 228, numerator := 148281313340697721958301696 }, { target := 232, numerator := 62443273641950974417255268352 }, { target := 235, numerator := 221815567535174848965846761472 }, { target := 237, numerator := 62414714971854526876275965952 }, { target := 242, numerator := 66583858854854094748303491072 }, { target := 244, numerator := 66611795890000003395716382720 }, { target := 406, numerator := 1775143529804316517356011520 }, { target := 409, numerator := 6303910319119646751046238208 }, { target := 411, numerator := 1774376324075280604009070592 }, { target := 416, numerator := 6065801824079987118662746112 }, { target := 418, numerator := 6068422745716189390123827200 }, { target := 498, numerator := 242614569222199732770701312 }, { target := 500, numerator := 242712478955279445131264000 }]

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
    Slot15.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot19.Left5.expected,
    Slot19.Left12.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected,
    Slot20.Left5.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 251095556437069504173834240 }, { target := 17, numerator := 6068102866520525163447975936 }, { target := 19, numerator := 66583858854854094748303491072 }, { target := 27, numerator := 6065801824079987118662746112 }, { target := 34, numerator := 242614569222199732770701312 }, { target := 35, numerator := 615846413304183634752700416 }, { target := 37, numerator := 21074816006796591110081740800 }, { target := 40, numerator := 21074878064368332843572527104 }, { target := 47, numerator := 615846413304183634752700416 }, { target := 86, numerator := 148081233710233384812281856 }, { target := 89, numerator := 524365858205881752788926464 }, { target := 91, numerator := 148281313340697721958301696 }, { target := 126, numerator := 251198954513360308980940800 }, { target := 127, numerator := 6070721288229966379776737280 }, { target := 129, numerator := 66611795890000003395716382720 }, { target := 137, numerator := 6068422745716189390123827200 }, { target := 144, numerator := 242712478955279445131264000 }, { target := 145, numerator := 2141691728165653145890848768 }, { target := 147, numerator := 73290609702837639937680998400 }, { target := 150, numerator := 73290825516691870619315208192 }, { target := 157, numerator := 2141691728165653145890848768 }, { target := 161, numerator := 6999373113346905440618807296 }, { target := 164, numerator := 24785262774520546126225997824 }, { target := 166, numerator := 7008830300803493241852788736 }, { target := 216, numerator := 1774426952146175618640248832 }, { target := 218, numerator := 62414571827980300653535690752 }, { target := 221, numerator := 62414714971854526876275965952 }, { target := 228, numerator := 1774376324075280604009070592 }, { target := 232, numerator := 6999332215402084551746387968 }, { target := 235, numerator := 24785117952078177588836564992 }, { target := 237, numerator := 7008789347599504925144383488 }, { target := 406, numerator := 148081233710233384812281856 }, { target := 409, numerator := 524365858205881752788926464 }, { target := 411, numerator := 148281313340697721958301696 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk5.Parent1
