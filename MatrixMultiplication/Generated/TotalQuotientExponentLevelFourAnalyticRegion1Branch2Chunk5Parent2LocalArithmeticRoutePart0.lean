import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk5Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 24; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk5.Parent2

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
    Slot0.Left3.expected,
    Slot0.Left4.expected,
    Slot0.Left5.expected,
    Slot0.Left6.expected,
    Slot0.Left7.expected,
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot0.Left10.expected,
    Slot0.Left11.expected,
    Slot0.Left12.expected,
    Slot0.Left13.expected,
    Slot0.Left14.expected,
    Slot0.Left15.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot1.Left4.expected,
    Slot1.Left5.expected,
    Slot1.Left6.expected,
    Slot1.Left7.expected,
    Slot1.Left8.expected,
    Slot1.Left9.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot3.Left0.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left5.expected,
    Slot4.Left12.expected,
    Slot5.Left0.expected,
    Slot5.Left3.expected,
    Slot5.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 9573672460187563220306755584 }, { target := 2, numerator := 346953058854001955950641020928 }, { target := 5, numerator := 346953186357896993431061790720 }, { target := 12, numerator := 9573544956292525739885985792 }, { target := 16, numerator := 25749840143742433339480473600 }, { target := 19, numerator := 87285003804274562577308057600 }, { target := 21, numerator := 25749840143742433339480473600 }, { target := 26, numerator := 60293137466447778126955020288 }, { target := 28, numerator := 60266687663166212663324704768 }, { target := 30, numerator := 25573987576907119160576704512 }, { target := 33, numerator := 86688911095367321662145953792 }, { target := 35, numerator := 25573987576907119160576704512 }, { target := 40, numerator := 44101613899541672293281300480 }, { target := 42, numerator := 44101613899541672293281300480 }, { target := 44, numerator := 8287701231404915783939129344 }, { target := 45, numerator := 1798881619586568211962789888 }, { target := 47, numerator := 1798881619586568211962789888 }, { target := 49, numerator := 2727336649050603418137133056 }, { target := 50, numerator := 25749840143742433339480473600 }, { target := 53, numerator := 87285003804274562577308057600 }, { target := 55, numerator := 25749840143742433339480473600 }, { target := 60, numerator := 236959939751353457650912198656 }, { target := 62, numerator := 236869506081885200613524897792 }, { target := 64, numerator := 194715098786451200884495876096 }, { target := 65, numerator := 36325803027780377441571176448 }, { target := 67, numerator := 36325803027780377441571176448 }, { target := 69, numerator := 67487074954167059048797569024 }, { target := 70, numerator := 2147052255635581414278168576 }, { target := 71, numerator := 60293118572710182401813250048 }, { target := 73, numerator := 60266668777971945431304765440 }, { target := 75, numerator := 194715193233780858277400150016 }, { target := 76, numerator := 2205080694977083614664065024 }, { target := 77, numerator := 25825205529528996559010660352 }, { target := 80, numerator := 87540472108091951540948959232 }, { target := 82, numerator := 25825205529528996559010660352 }, { target := 87, numerator := 36383831467121879641957072896 }, { target := 89, numerator := 36383831467121879641957072896 }, { target := 91, numerator := 2205080694977083614664065024 }, { target := 92, numerator := 32611982909924236616873803776 }, { target := 94, numerator := 32611982909924236616873803776 }, { target := 96, numerator := 37312286496585914848131416064 }, { target := 97, numerator := 2030995376952577013506375680 }, { target := 98, numerator := 44101613899541672293281300480 }, { target := 100, numerator := 44101613899541672293281300480 }, { target := 102, numerator := 67487074954167059048797569024 }, { target := 103, numerator := 37312286496585914848131416064 }, { target := 104, numerator := 8287654007740087087486992384 }, { target := 105, numerator := 1798881619586568211962789888 }, { target := 107, numerator := 1798881619586568211962789888 }, { target := 109, numerator := 2147052255635581414278168576 }, { target := 110, numerator := 2030995376952577013506375680 }, { target := 111, numerator := 2727336649050603418137133056 }]

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
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot7.Left0.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 8287701231404915783939129344 }, { target := 1, numerator := 2727336649050603418137133056 }, { target := 2, numerator := 194715098786451200884495876096 }, { target := 3, numerator := 67487074954167059048797569024 }, { target := 4, numerator := 2147052255635581414278168576 }, { target := 5, numerator := 194715193233780858277400150016 }, { target := 6, numerator := 2205080694977083614664065024 }, { target := 7, numerator := 2205080694977083614664065024 }, { target := 8, numerator := 37312286496585914848131416064 }, { target := 9, numerator := 2030995376952577013506375680 }, { target := 10, numerator := 67487074954167059048797569024 }, { target := 11, numerator := 37312286496585914848131416064 }, { target := 12, numerator := 8287654007740087087486992384 }, { target := 13, numerator := 2147052255635581414278168576 }, { target := 14, numerator := 2030995376952577013506375680 }, { target := 15, numerator := 2727336649050603418137133056 }, { target := 16, numerator := 60293137466447778126955020288 }, { target := 17, numerator := 44101613899541672293281300480 }, { target := 18, numerator := 1798881619586568211962789888 }, { target := 19, numerator := 236959939751353457650912198656 }, { target := 20, numerator := 36325803027780377441571176448 }, { target := 21, numerator := 60293118572710182401813250048 }, { target := 22, numerator := 36383831467121879641957072896 }, { target := 23, numerator := 32611982909924236616873803776 }, { target := 24, numerator := 44101613899541672293281300480 }, { target := 25, numerator := 1798881619586568211962789888 }, { target := 26, numerator := 25749840143742433339480473600 }, { target := 27, numerator := 25573987576907119160576704512 }, { target := 28, numerator := 25749840143742433339480473600 }, { target := 29, numerator := 25825205529528996559010660352 }, { target := 44, numerator := 9573672460187563220306755584 }, { target := 50, numerator := 60266687663166212663324704768 }, { target := 51, numerator := 44101613899541672293281300480 }, { target := 52, numerator := 1798881619586568211962789888 }, { target := 53, numerator := 236869506081885200613524897792 }, { target := 54, numerator := 36325803027780377441571176448 }, { target := 55, numerator := 60266668777971945431304765440 }, { target := 56, numerator := 36383831467121879641957072896 }, { target := 57, numerator := 32611982909924236616873803776 }, { target := 58, numerator := 44101613899541672293281300480 }, { target := 59, numerator := 1798881619586568211962789888 }, { target := 60, numerator := 87285003804274562577308057600 }, { target := 61, numerator := 86688911095367321662145953792 }, { target := 62, numerator := 87285003804274562577308057600 }, { target := 63, numerator := 87540472108091951540948959232 }, { target := 64, numerator := 346953058854001955950641020928 }, { target := 71, numerator := 25749840143742433339480473600 }, { target := 72, numerator := 25573987576907119160576704512 }, { target := 73, numerator := 25749840143742433339480473600 }, { target := 74, numerator := 25825205529528996559010660352 }, { target := 75, numerator := 346953186357896993431061790720 }, { target := 104, numerator := 9573544956292525739885985792 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk5.Parent2
