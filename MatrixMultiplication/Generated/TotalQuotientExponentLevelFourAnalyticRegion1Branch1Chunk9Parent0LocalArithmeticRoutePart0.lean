import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk9Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 38; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk9.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left1.expected,
    Slot0.Left2.expected,
    Slot0.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 89, numerator := 233020451730719773424615424 }, { target := 90, numerator := 174765338798039830068461568 }, { target := 91, numerator := 184474524286819820627820544 }, { target := 92, numerator := 237875044475109768704294912 }, { target := 93, numerator := 3184612840319836903469744128 }, { target := 94, numerator := 5568217877815324585792372736 }, { target := 95, numerator := 169910746053649834788782080 }, { target := 96, numerator := 3184612840319836903469744128 }, { target := 97, numerator := 179619931542429825348141056 }, { target := 98, numerator := 184474524286819820627820544 }, { target := 99, numerator := 184474524286819820627820544 }, { target := 100, numerator := 179619931542429825348141056 }, { target := 101, numerator := 5568217877815324585792372736 }, { target := 102, numerator := 179619931542429825348141056 }, { target := 103, numerator := 233020451730719773424615424 }, { target := 104, numerator := 237875044475109768704294912 }, { target := 160, numerator := 232340430957186544513843200 }, { target := 161, numerator := 174255323217889908385382400 }, { target := 162, numerator := 183936174507772681073459200 }, { target := 163, numerator := 237180856602127930857881600 }, { target := 164, numerator := 3175319223081549441689190400 }, { target := 165, numerator := 5551968214747770136612044800 }, { target := 166, numerator := 169414897572948522041344000 }, { target := 167, numerator := 3175319223081549441689190400 }, { target := 168, numerator := 179095748862831294729420800 }, { target := 169, numerator := 183936174507772681073459200 }, { target := 170, numerator := 183936174507772681073459200 }, { target := 171, numerator := 179095748862831294729420800 }, { target := 172, numerator := 5551968214747770136612044800 }, { target := 173, numerator := 179095748862831294729420800 }, { target := 174, numerator := 232340430957186544513843200 }, { target := 175, numerator := 237180856602127930857881600 }, { target := 205, numerator := 230753715818942343722041344 }, { target := 206, numerator := 173065286864206757791531008 }, { target := 207, numerator := 182680025023329355446616064 }, { target := 208, numerator := 235561084898503642549583872 }, { target := 209, numerator := 3153634116192212030867898368 }, { target := 210, numerator := 5514052334256809755191279616 }, { target := 211, numerator := 168257917784645458963988480 }, { target := 212, numerator := 3153634116192212030867898368 }, { target := 213, numerator := 177872655943768056619073536 }, { target := 214, numerator := 182680025023329355446616064 }, { target := 215, numerator := 182680025023329355446616064 }, { target := 216, numerator := 177872655943768056619073536 }, { target := 217, numerator := 5514052334256809755191279616 }, { target := 218, numerator := 177872655943768056619073536 }, { target := 219, numerator := 230753715818942343722041344 }, { target := 220, numerator := 235561084898503642549583872 }, { target := 231, numerator := 232340430957186544513843200 }, { target := 232, numerator := 174255323217889908385382400 }, { target := 233, numerator := 183936174507772681073459200 }, { target := 234, numerator := 237180856602127930857881600 }, { target := 235, numerator := 3175319223081549441689190400 }, { target := 236, numerator := 5551968214747770136612044800 }, { target := 237, numerator := 169414897572948522041344000 }, { target := 238, numerator := 3175319223081549441689190400 }, { target := 239, numerator := 179095748862831294729420800 }, { target := 240, numerator := 183936174507772681073459200 }, { target := 241, numerator := 183936174507772681073459200 }, { target := 242, numerator := 179095748862831294729420800 }, { target := 243, numerator := 5551968214747770136612044800 }, { target := 244, numerator := 179095748862831294729420800 }, { target := 245, numerator := 232340430957186544513843200 }, { target := 246, numerator := 237180856602127930857881600 }]

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
    Slot1.Left0.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left6.expected,
    Slot4.Left14.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left2.expected,
    Slot7.Left3.expected,
    Slot7.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 174765338798039830068461568 }, { target := 1, numerator := 20656141011651978086389383168 }, { target := 3, numerator := 289165847437177702781550592 }, { target := 4, numerator := 288485826663644473870778368 }, { target := 5, numerator := 286899111525400273078976512 }, { target := 6, numerator := 288485826663644473870778368 }, { target := 7, numerator := 196022660674793528338780520448 }, { target := 9, numerator := 10022140257374624099904520192 }, { target := 10, numerator := 10021630241794474178221441024 }, { target := 11, numerator := 10020440205440791027627589632 }, { target := 12, numerator := 10021630241794474178221441024 }, { target := 14, numerator := 184474524286819820627820544 }, { target := 15, numerator := 183936174507772681073459200 }, { target := 16, numerator := 182680025023329355446616064 }, { target := 17, numerator := 183936174507772681073459200 }, { target := 30, numerator := 237875044475109768704294912 }, { target := 31, numerator := 237180856602127930857881600 }, { target := 32, numerator := 235561084898503642549583872 }, { target := 33, numerator := 237180856602127930857881600 }, { target := 36, numerator := 3184612840319836903469744128 }, { target := 37, numerator := 3175319223081549441689190400 }, { target := 38, numerator := 3153634116192212030867898368 }, { target := 39, numerator := 3175319223081549441689190400 }, { target := 55, numerator := 20656155178751426695325024256 }, { target := 56, numerator := 9847376099168204987247362048 }, { target := 57, numerator := 9847376099168204987247362048 }, { target := 58, numerator := 9847376099168204987247362048 }, { target := 59, numerator := 9847376099168204987247362048 }, { target := 89, numerator := 56145395706457929356935168 }, { target := 90, numerator := 9847374918576584269836058624 }, { target := 95, numerator := 9847376099168204987247362048 }, { target := 103, numerator := 56144215114837211945631744 }, { target := 160, numerator := 56145395706457929356935168 }, { target := 161, numerator := 9847374918576584269836058624 }, { target := 166, numerator := 9847376099168204987247362048 }, { target := 174, numerator := 56144215114837211945631744 }, { target := 176, numerator := 174765338798039830068461568 }, { target := 177, numerator := 56144215114837211945631744 }, { target := 178, numerator := 56144215114837211945631744 }, { target := 179, numerator := 56144215114837211945631744 }, { target := 180, numerator := 56144215114837211945631744 }, { target := 205, numerator := 56145395706457929356935168 }, { target := 206, numerator := 9847374918576584269836058624 }, { target := 211, numerator := 9847376099168204987247362048 }, { target := 219, numerator := 56144215114837211945631744 }, { target := 231, numerator := 56145395706457929356935168 }, { target := 232, numerator := 9847374918576584269836058624 }, { target := 237, numerator := 9847376099168204987247362048 }, { target := 245, numerator := 56144215114837211945631744 }, { target := 247, numerator := 174765338798039830068461568 }, { target := 248, numerator := 20656141011651978086389383168 }, { target := 250, numerator := 196022660674793528338780520448 }, { target := 258, numerator := 20656155178751426695325024256 }, { target := 265, numerator := 174765338798039830068461568 }]

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
    Slot7.Left5.expected,
    Slot7.Left6.expected,
    Slot7.Left7.expected,
    Slot7.Left8.expected,
    Slot7.Left9.expected,
    Slot7.Left10.expected,
    Slot7.Left11.expected,
    Slot7.Left12.expected,
    Slot7.Left13.expected,
    Slot7.Left14.expected,
    Slot7.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 41, numerator := 5568217877815324585792372736 }, { target := 42, numerator := 5551968214747770136612044800 }, { target := 43, numerator := 5514052334256809755191279616 }, { target := 44, numerator := 5551968214747770136612044800 }, { target := 56, numerator := 169910746053649834788782080 }, { target := 57, numerator := 169414897572948522041344000 }, { target := 58, numerator := 168257917784645458963988480 }, { target := 59, numerator := 169414897572948522041344000 }, { target := 61, numerator := 3184612840319836903469744128 }, { target := 62, numerator := 3175319223081549441689190400 }, { target := 63, numerator := 3153634116192212030867898368 }, { target := 64, numerator := 3175319223081549441689190400 }, { target := 75, numerator := 179619931542429825348141056 }, { target := 76, numerator := 179095748862831294729420800 }, { target := 77, numerator := 177872655943768056619073536 }, { target := 78, numerator := 179095748862831294729420800 }, { target := 107, numerator := 184474524286819820627820544 }, { target := 108, numerator := 183936174507772681073459200 }, { target := 109, numerator := 182680025023329355446616064 }, { target := 110, numerator := 183936174507772681073459200 }, { target := 112, numerator := 184474524286819820627820544 }, { target := 113, numerator := 183936174507772681073459200 }, { target := 114, numerator := 182680025023329355446616064 }, { target := 115, numerator := 183936174507772681073459200 }, { target := 127, numerator := 179619931542429825348141056 }, { target := 128, numerator := 179095748862831294729420800 }, { target := 129, numerator := 177872655943768056619073536 }, { target := 130, numerator := 179095748862831294729420800 }, { target := 132, numerator := 5568217877815324585792372736 }, { target := 133, numerator := 5551968214747770136612044800 }, { target := 134, numerator := 5514052334256809755191279616 }, { target := 135, numerator := 5551968214747770136612044800 }, { target := 146, numerator := 179619931542429825348141056 }, { target := 147, numerator := 179095748862831294729420800 }, { target := 148, numerator := 177872655943768056619073536 }, { target := 149, numerator := 179095748862831294729420800 }, { target := 177, numerator := 233020451730719773424615424 }, { target := 178, numerator := 232340430957186544513843200 }, { target := 179, numerator := 230753715818942343722041344 }, { target := 180, numerator := 232340430957186544513843200 }, { target := 191, numerator := 237875044475109768704294912 }, { target := 192, numerator := 237180856602127930857881600 }, { target := 193, numerator := 235561084898503642549583872 }, { target := 194, numerator := 237180856602127930857881600 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk9.Parent0
