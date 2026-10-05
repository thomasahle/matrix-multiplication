import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk2Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 34; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk2.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left6.expected,
    Slot9.Left14.expected,
    Slot14.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 19269241834347156754923520 }, { target := 30, numerator := 1053321668699870675391741952 }, { target := 35, numerator := 1053617817619576253904322560 }, { target := 43, numerator := 18978192721053818367770624 }, { target := 71, numerator := 838169985036729477758976 }, { target := 72, numerator := 41173517060172323103965184 }, { target := 74, numerator := 459525795250463517324607488 }, { target := 82, numerator := 41173581856274911850397696 }, { target := 89, numerator := 838040392831551984893952 }, { target := 104, numerator := 367503018614441096555528192 }, { target := 105, numerator := 18891001875033098415249555456 }, { target := 110, numerator := 18895393746860289410887319552 }, { target := 118, numerator := 363290219449310162423119872 }, { target := 146, numerator := 28386451677144306885328896 }, { target := 147, numerator := 1394430811496359724228542464 }, { target := 149, numerator := 15562841683846477078434152448 }, { target := 157, numerator := 1394433005957468853702230016 }, { target := 164, numerator := 28382062754926047937953792 }, { target := 200, numerator := 8803131433760614216892416 }, { target := 202, numerator := 323871059001715847329742848 }, { target := 205, numerator := 323871415922400890579845120 }, { target := 212, numerator := 8802774513075570966790144 }, { target := 226, numerator := 367483418650499304843640832 }, { target := 227, numerator := 18889994365062239039023742976 }, { target := 232, numerator := 18894386002658620790005563392 }, { target := 240, numerator := 363270844165731655574618112 }, { target := 242, numerator := 308068026817890743129997312 }, { target := 243, numerator := 15133259821185570769477828608 }, { target := 245, numerator := 168897965260028765493742534656 }, { target := 253, numerator := 15133283636888621899371773952 }, { target := 260, numerator := 308020395411788483342106624 }, { target := 296, numerator := 515325240950217003583406080 }, { target := 298, numerator := 18959041197180390933255946240 }, { target := 301, numerator := 18959062090908878803409305600 }, { target := 308, numerator := 515304347221729133430046720 }, { target := 624, numerator := 10484989446314383290400768 }, { target := 625, numerator := 538966879882504427299405824 }, { target := 630, numerator := 539092181519294448384606208 }, { target := 638, numerator := 10364796815101791188287488 }, { target := 640, numerator := 28386407984909571997040640 }, { target := 641, numerator := 1394428665197870909761781760 }, { target := 643, numerator := 15562817729625649259552440320 }, { target := 651, numerator := 1394430859655602339514941440 }, { target := 658, numerator := 28382019069446712490721280 }, { target := 659, numerator := 515496313848555718506971136 }, { target := 661, numerator := 18965335043997100762629931008 }, { target := 664, numerator := 18965355944661695008887275520 }, { target := 671, numerator := 515475413183961472249626624 }, { target := 1017, numerator := 837973369980422480461824 }, { target := 1018, numerator := 41163858716972658003542016 }, { target := 1020, numerator := 459418001256738332356902912 }, { target := 1028, numerator := 41163923497875598007599104 }, { target := 1035, numerator := 837843808174542472347648 }, { target := 1036, numerator := 8632058535421899293327360 }, { target := 1038, numerator := 317577212185006017955758080 }, { target := 1041, numerator := 317577562169584685101875200 }, { target := 1048, numerator := 8631708550843232147210240 }]

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
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left3.expected,
    Slot15.Left11.expected,
    Slot15.Left18.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left6.expected,
    Slot16.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 838169985036729477758976 }, { target := 72, numerator := 28386451677144306885328896 }, { target := 74, numerator := 308068026817890743129997312 }, { target := 82, numerator := 28386407984909571997040640 }, { target := 89, numerator := 837973369980422480461824 }, { target := 104, numerator := 323871059001715847329742848 }, { target := 105, numerator := 18959041197180390933255946240 }, { target := 110, numerator := 18965335043997100762629931008 }, { target := 118, numerator := 317577212185006017955758080 }, { target := 146, numerator := 41173517060172323103965184 }, { target := 147, numerator := 1394430811496359724228542464 }, { target := 149, numerator := 15133259821185570769477828608 }, { target := 157, numerator := 1394428665197870909761781760 }, { target := 164, numerator := 41163858716972658003542016 }, { target := 200, numerator := 10466110400586542538031104 }, { target := 202, numerator := 367503018614441096555528192 }, { target := 205, numerator := 367483418650499304843640832 }, { target := 212, numerator := 10484989446314383290400768 }, { target := 226, numerator := 323871415922400890579845120 }, { target := 227, numerator := 18959062090908878803409305600 }, { target := 232, numerator := 18965355944661695008887275520 }, { target := 240, numerator := 317577562169584685101875200 }, { target := 242, numerator := 459525795250463517324607488 }, { target := 243, numerator := 15562841683846477078434152448 }, { target := 245, numerator := 168897965260028765493742534656 }, { target := 253, numerator := 15562817729625649259552440320 }, { target := 260, numerator := 459418001256738332356902912 }, { target := 296, numerator := 537996427749653671808335872 }, { target := 298, numerator := 18891001875033098415249555456 }, { target := 301, numerator := 18889994365062239039023742976 }, { target := 308, numerator := 538966879882504427299405824 }, { target := 624, numerator := 8802774513075570966790144 }, { target := 625, numerator := 515304347221729133430046720 }, { target := 630, numerator := 515475413183961472249626624 }, { target := 638, numerator := 8631708550843232147210240 }, { target := 640, numerator := 41173581856274911850397696 }, { target := 641, numerator := 1394433005957468853702230016 }, { target := 643, numerator := 15133283636888621899371773952 }, { target := 651, numerator := 1394430859655602339514941440 }, { target := 658, numerator := 41163923497875598007599104 }, { target := 659, numerator := 538121503771020535397351424 }, { target := 661, numerator := 18895393746860289410887319552 }, { target := 664, numerator := 18894386002658620790005563392 }, { target := 671, numerator := 539092181519294448384606208 }, { target := 1017, numerator := 838040392831551984893952 }, { target := 1018, numerator := 28382062754926047937953792 }, { target := 1020, numerator := 308020395411788483342106624 }, { target := 1028, numerator := 28382019069446712490721280 }, { target := 1035, numerator := 837843808174542472347648 }, { target := 1036, numerator := 10346134185631919074443264 }, { target := 1038, numerator := 363290219449310162423119872 }, { target := 1041, numerator := 363270844165731655574618112 }, { target := 1048, numerator := 10364796815101791188287488 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk2.Parent1
