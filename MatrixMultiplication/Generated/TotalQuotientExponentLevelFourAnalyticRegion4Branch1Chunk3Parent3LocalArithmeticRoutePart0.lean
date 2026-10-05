import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk3Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 45; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk3.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left6.expected,
    Slot8.Left14.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 144663323746799523228286976 }, { target := 15, numerator := 7436224960689132969884909568 }, { target := 20, numerator := 7437953770369082665579053056 }, { target := 28, numerator := 143005003954479768079958016 }, { target := 56, numerator := 4938966363854090702684160 }, { target := 57, numerator := 167857774302078079164481536 }, { target := 59, numerator := 1848264909417916290161442816 }, { target := 67, numerator := 167860389587417689485213696 }, { target := 74, numerator := 4938312542519188122501120 }, { target := 110, numerator := 13222346691011754307092480 }, { target := 112, numerator := 439735294426389597766287360 }, { target := 115, numerator := 439735294426389597766287360 }, { target := 122, numerator := 13222238697507439729704960 }, { target := 136, numerator := 466897364493511043309371392 }, { target := 137, numerator := 24000235484727905278079533056 }, { target := 142, numerator := 24005815175988781903094218752 }, { target := 150, numerator := 461545177633234719785091072 }, { target := 152, numerator := 173424985795090334802247680 }, { target := 153, numerator := 5894094022785973651167510528 }, { target := 155, numerator := 64899270828651357866943315968 }, { target := 163, numerator := 5894185854920363426298462208 }, { target := 170, numerator := 173402027761492891019509760 }, { target := 206, numerator := 447803562646551341909934080 }, { target := 208, numerator := 14892593279181352941974978560 }, { target := 211, numerator := 14892593279181352941974978560 }, { target := 218, numerator := 447799905211369459453788160 }, { target := 257, numerator := 123008232762666160274538496 }, { target := 260, numerator := 419331717056351134071914496 }, { target := 262, numerator := 123008431051935628746817536 }, { target := 267, numerator := 144376848871530760689942528 }, { target := 268, numerator := 7421499102310457305416597504 }, { target := 273, numerator := 7423224488451360616001568768 }, { target := 281, numerator := 142721813028061040395419648 }, { target := 283, numerator := 173415736555503120317153280 }, { target := 284, numerator := 5893779674265105214407180288 }, { target := 286, numerator := 64895809569005421024172310528 }, { target := 294, numerator := 5893871501501830394772717568 }, { target := 301, numerator := 173392779746321825225768960 }, { target := 302, numerator := 4859852211032775433398517760 }, { target := 304, numerator := 161623998585663631665733304320 }, { target := 307, numerator := 161623998585663631665733304320 }, { target := 314, numerator := 4859812518194356883575275520 }, { target := 353, numerator := 7200761190975656207822356480 }, { target := 356, numerator := 24547198886682965752393236480 }, { target := 358, numerator := 7200772798602593913463111680 }, { target := 660, numerator := 4947875401525453620510720 }, { target := 661, numerator := 168160560578500780319834112 }, { target := 663, numerator := 1851598858364232467451215872 }, { target := 671, numerator := 168163180581361000311160832 }, { target := 678, numerator := 4947220400810398622679040 }, { target := 679, numerator := 447802873390331621225267200 }, { target := 681, numerator := 14892570356602343564666470400 }, { target := 684, numerator := 14892570356602343564666470400 }, { target := 691, numerator := 447799215960779238303334400 }, { target := 695, numerator := 7203151632951511501888290816 }, { target := 698, numerator := 24555347838307959821687586816 }, { target := 700, numerator := 7203163244431841638697926656 }, { target := 966, numerator := 13219245038023011226091520 }, { target := 968, numerator := 439632142820847399878000640 }, { target := 971, numerator := 439632142820847399878000640 }, { target := 978, numerator := 13219137069851444552663040 }, { target := 982, numerator := 120617790786810866208604160 }, { target := 985, numerator := 411182765431357064777564160 }, { target := 987, numerator := 120617985222687903512002560 }]

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
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left3.expected,
    Slot14.Left11.expected,
    Slot14.Left18.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left6.expected,
    Slot15.Left14.expected,
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 123008232762666160274538496 }, { target := 15, numerator := 7200761190975656207822356480 }, { target := 20, numerator := 7203151632951511501888290816 }, { target := 28, numerator := 120617790786810866208604160 }, { target := 56, numerator := 14548006784619446343303168 }, { target := 57, numerator := 714643349477353332211187712 }, { target := 59, numerator := 7975929115045127858719555584 }, { target := 67, numerator := 714644474134829627634352128 }, { target := 74, numerator := 14545757469666855496974336 }, { target := 110, numerator := 14548006784619446343303168 }, { target := 112, numerator := 535227537967823214612578304 }, { target := 115, numerator := 535228127812992135604469760 }, { target := 122, numerator := 14547416939450525351411712 }, { target := 136, numerator := 419331717056351134071914496 }, { target := 137, numerator := 24547198886682965752393236480 }, { target := 142, numerator := 24555347838307959821687586816 }, { target := 150, numerator := 411182765431357064777564160 }, { target := 152, numerator := 535227537967823214612578304 }, { target := 153, numerator := 26292041661008066244652302336 }, { target := 155, numerator := 293437923589967012663396401152 }, { target := 163, numerator := 26292083037648935776036061184 }, { target := 170, numerator := 535144784686084151845060608 }, { target := 206, numerator := 714643349477353332211187712 }, { target := 208, numerator := 26292041661008066244652302336 }, { target := 211, numerator := 26292070636037665239953571840 }, { target := 218, numerator := 714614374447754336909918208 }, { target := 257, numerator := 144663323746799523228286976 }, { target := 260, numerator := 466897364493511043309371392 }, { target := 262, numerator := 144376848871530760689942528 }, { target := 267, numerator := 123008431051935628746817536 }, { target := 268, numerator := 7200772798602593913463111680 }, { target := 273, numerator := 7203163244431841638697926656 }, { target := 281, numerator := 120617985222687903512002560 }, { target := 283, numerator := 535228127812992135604469760 }, { target := 284, numerator := 26292070636037665239953571840 }, { target := 286, numerator := 293438246971948188218299514880 }, { target := 294, numerator := 26292112012724133717564456960 }, { target := 301, numerator := 535145374440055180382699520 }, { target := 302, numerator := 7975929115045127858719555584 }, { target := 304, numerator := 293437923589967012663396401152 }, { target := 307, numerator := 293438246971948188218299514880 }, { target := 314, numerator := 7975605733063952303816441856 }, { target := 353, numerator := 7436224960689132969884909568 }, { target := 356, numerator := 24000235484727905278079533056 }, { target := 358, numerator := 7421499102310457305416597504 }, { target := 660, numerator := 14547416939450525351411712 }, { target := 661, numerator := 714614374447754336909918208 }, { target := 663, numerator := 7975605733063952303816441856 }, { target := 671, numerator := 714615499059631686105956352 }, { target := 678, numerator := 14545167715695826959335424 }, { target := 679, numerator := 714644474134829627634352128 }, { target := 681, numerator := 26292083037648935776036061184 }, { target := 684, numerator := 26292112012724133717564456960 }, { target := 691, numerator := 714615499059631686105956352 }, { target := 695, numerator := 7437953770369082665579053056 }, { target := 698, numerator := 24005815175988781903094218752 }, { target := 700, numerator := 7423224488451360616001568768 }, { target := 966, numerator := 14545757469666855496974336 }, { target := 968, numerator := 535144784686084151845060608 }, { target := 971, numerator := 535145374440055180382699520 }, { target := 978, numerator := 14545167715695826959335424 }, { target := 982, numerator := 143005003954479768079958016 }, { target := 985, numerator := 461545177633234719785091072 }, { target := 987, numerator := 142721813028061040395419648 }]

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
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot20.Left5.expected,
    Slot20.Left12.expected,
    Slot21.Left0.expected,
    Slot21.Left1.expected,
    Slot21.Left3.expected,
    Slot21.Left11.expected,
    Slot21.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 13222346691011754307092480 }, { target := 57, numerator := 447803562646551341909934080 }, { target := 59, numerator := 4859852211032775433398517760 }, { target := 67, numerator := 447802873390331621225267200 }, { target := 74, numerator := 13219245038023011226091520 }, { target := 110, numerator := 4938966363854090702684160 }, { target := 112, numerator := 173424985795090334802247680 }, { target := 115, numerator := 173415736555503120317153280 }, { target := 122, numerator := 4947875401525453620510720 }, { target := 152, numerator := 439735294426389597766287360 }, { target := 153, numerator := 14892593279181352941974978560 }, { target := 155, numerator := 161623998585663631665733304320 }, { target := 163, numerator := 14892570356602343564666470400 }, { target := 170, numerator := 439632142820847399878000640 }, { target := 206, numerator := 167857774302078079164481536 }, { target := 208, numerator := 5894094022785973651167510528 }, { target := 211, numerator := 5893779674265105214407180288 }, { target := 218, numerator := 168160560578500780319834112 }, { target := 283, numerator := 439735294426389597766287360 }, { target := 284, numerator := 14892593279181352941974978560 }, { target := 286, numerator := 161623998585663631665733304320 }, { target := 294, numerator := 14892570356602343564666470400 }, { target := 301, numerator := 439632142820847399878000640 }, { target := 302, numerator := 1848264909417916290161442816 }, { target := 304, numerator := 64899270828651357866943315968 }, { target := 307, numerator := 64895809569005421024172310528 }, { target := 314, numerator := 1851598858364232467451215872 }, { target := 660, numerator := 13222238697507439729704960 }, { target := 661, numerator := 447799905211369459453788160 }, { target := 663, numerator := 4859812518194356883575275520 }, { target := 671, numerator := 447799215960779238303334400 }, { target := 678, numerator := 13219137069851444552663040 }, { target := 679, numerator := 167860389587417689485213696 }, { target := 681, numerator := 5894185854920363426298462208 }, { target := 684, numerator := 5893871501501830394772717568 }, { target := 691, numerator := 168163180581361000311160832 }, { target := 966, numerator := 4938312542519188122501120 }, { target := 968, numerator := 173402027761492891019509760 }, { target := 971, numerator := 173392779746321825225768960 }, { target := 978, numerator := 4947220400810398622679040 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk3.Parent3
