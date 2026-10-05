import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk15Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 62; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
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
    Slot2.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 257, numerator := 14875454421039382423142400 }, { target := 258, numerator := 264783088694501007131934720 }, { target := 259, numerator := 14875454421039382423142400 }, { target := 260, numerator := 235528028333123555033088000 }, { target := 261, numerator := 402133117848764638172282880 }, { target := 262, numerator := 14875454421039382423142400 }, { target := 263, numerator := 402133117848764638172282880 }, { target := 264, numerator := 402133117848764638172282880 }, { target := 265, numerator := 264783088694501007131934720 }, { target := 266, numerator := 14875454421039382423142400 }, { target := 353, numerator := 15300467404497650492375040 }, { target := 354, numerator := 272348319800058178764275712 }, { target := 355, numerator := 15300467404497650492375040 }, { target := 356, numerator := 242257400571212799462604800 }, { target := 357, numerator := 413622635501586484977205248 }, { target := 358, numerator := 15300467404497650492375040 }, { target := 359, numerator := 413622635501586484977205248 }, { target := 360, numerator := 413622635501586484977205248 }, { target := 361, numerator := 272348319800058178764275712 }, { target := 362, numerator := 15300467404497650492375040 }, { target := 379, numerator := 14875454421039382423142400 }, { target := 380, numerator := 264783088694501007131934720 }, { target := 381, numerator := 14875454421039382423142400 }, { target := 382, numerator := 235528028333123555033088000 }, { target := 383, numerator := 402133117848764638172282880 }, { target := 384, numerator := 14875454421039382423142400 }, { target := 385, numerator := 402133117848764638172282880 }, { target := 386, numerator := 402133117848764638172282880 }, { target := 387, numerator := 264783088694501007131934720 }, { target := 388, numerator := 14875454421039382423142400 }, { target := 389, numerator := 241785163922925834941235200 }, { target := 391, numerator := 241785163922925834941235200 }, { target := 524, numerator := 13175402487206310146211840 }, { target := 525, numerator := 234522164272272320602570752 }, { target := 526, numerator := 13175402487206310146211840 }, { target := 527, numerator := 208610539380766577315020800 }, { target := 528, numerator := 356175047237477250952593408 }, { target := 529, numerator := 13175402487206310146211840 }, { target := 530, numerator := 356175047237477250952593408 }, { target := 531, numerator := 356175047237477250952593408 }, { target := 532, numerator := 234522164272272320602570752 }, { target := 533, numerator := 13175402487206310146211840 }, { target := 656, numerator := 4845374685015433732222353408 }, { target := 658, numerator := 4845374685015433732222353408 }, { target := 731, numerator := 8133652914367225087423152128 }, { target := 733, numerator := 8133652914367225087423152128 }, { target := 745, numerator := 7804825091432045951903072256 }, { target := 747, numerator := 7804825091432045951903072256 }, { target := 872, numerator := 241785163922925834941235200 }, { target := 874, numerator := 241785163922925834941235200 }, { target := 947, numerator := 7804825091432045951903072256 }, { target := 949, numerator := 7804825091432045951903072256 }, { target := 961, numerator := 5212888134178281001333030912 }, { target := 963, numerator := 5212888134178281001333030912 }, { target := 992, numerator := 251456570479842868338884608 }, { target := 994, numerator := 251456570479842868338884608 }, { target := 1006, numerator := 4845374685015433732222353408 }, { target := 1008, numerator := 4845374685015433732222353408 }, { target := 1011, numerator := 232113757366008801543585792 }, { target := 1013, numerator := 232113757366008801543585792 }]

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
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 620, numerator := 616693838997946968456560640 }, { target := 621, numerator := 10977150334163456038526779392 }, { target := 622, numerator := 616693838997946968456560640 }, { target := 623, numerator := 9764319117467493667228876800 }, { target := 624, numerator := 16671290114244499713942355968 }, { target := 625, numerator := 616693838997946968456560640 }, { target := 626, numerator := 16671290114244499713942355968 }, { target := 627, numerator := 16671290114244499713942355968 }, { target := 628, numerator := 10977150334163456038526779392 }, { target := 629, numerator := 616693838997946968456560640 }, { target := 646, numerator := 167880128466015887346892800 }, { target := 647, numerator := 2988266286695082794774691840 }, { target := 648, numerator := 167880128466015887346892800 }, { target := 649, numerator := 2658102034045251549659136000 }, { target := 650, numerator := 4538359472864629487944335360 }, { target := 651, numerator := 167880128466015887346892800 }, { target := 652, numerator := 4538359472864629487944335360 }, { target := 653, numerator := 4538359472864629487944335360 }, { target := 654, numerator := 2988266286695082794774691840 }, { target := 655, numerator := 167880128466015887346892800 }, { target := 695, numerator := 15300467404497650492375040 }, { target := 696, numerator := 272348319800058178764275712 }, { target := 697, numerator := 15300467404497650492375040 }, { target := 698, numerator := 242257400571212799462604800 }, { target := 699, numerator := 413622635501586484977205248 }, { target := 700, numerator := 15300467404497650492375040 }, { target := 701, numerator := 413622635501586484977205248 }, { target := 702, numerator := 413622635501586484977205248 }, { target := 703, numerator := 272348319800058178764275712 }, { target := 704, numerator := 15300467404497650492375040 }, { target := 721, numerator := 616693838997946968456560640 }, { target := 722, numerator := 10977150334163456038526779392 }, { target := 723, numerator := 616693838997946968456560640 }, { target := 724, numerator := 9764319117467493667228876800 }, { target := 725, numerator := 16671290114244499713942355968 }, { target := 726, numerator := 616693838997946968456560640 }, { target := 727, numerator := 16671290114244499713942355968 }, { target := 728, numerator := 16671290114244499713942355968 }, { target := 729, numerator := 10977150334163456038526779392 }, { target := 730, numerator := 616693838997946968456560640 }, { target := 735, numerator := 14875454421039382423142400 }, { target := 736, numerator := 264783088694501007131934720 }, { target := 737, numerator := 14875454421039382423142400 }, { target := 738, numerator := 235528028333123555033088000 }, { target := 739, numerator := 402133117848764638172282880 }, { target := 740, numerator := 14875454421039382423142400 }, { target := 741, numerator := 402133117848764638172282880 }, { target := 742, numerator := 402133117848764638172282880 }, { target := 743, numerator := 264783088694501007131934720 }, { target := 744, numerator := 14875454421039382423142400 }, { target := 836, numerator := 14875454421039382423142400 }, { target := 837, numerator := 264783088694501007131934720 }, { target := 838, numerator := 14875454421039382423142400 }, { target := 839, numerator := 235528028333123555033088000 }, { target := 840, numerator := 402133117848764638172282880 }, { target := 841, numerator := 14875454421039382423142400 }, { target := 842, numerator := 402133117848764638172282880 }, { target := 843, numerator := 402133117848764638172282880 }, { target := 844, numerator := 264783088694501007131934720 }, { target := 845, numerator := 14875454421039382423142400 }]

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
    Slot2.Left10.expected,
    Slot2.Left11.expected,
    Slot2.Left12.expected,
    Slot2.Left13.expected,
    Slot2.Left14.expected,
    Slot2.Left15.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 749, numerator := 19807040628566084398385987584 }, { target := 862, numerator := 12750389503748042076979200 }, { target := 863, numerator := 226956933166715148970229760 }, { target := 864, numerator := 12750389503748042076979200 }, { target := 865, numerator := 201881167142677332885504000 }, { target := 866, numerator := 344685529584655404147671040 }, { target := 867, numerator := 12750389503748042076979200 }, { target := 868, numerator := 344685529584655404147671040 }, { target := 869, numerator := 344685529584655404147671040 }, { target := 870, numerator := 226956933166715148970229760 }, { target := 871, numerator := 12750389503748042076979200 }, { target := 911, numerator := 14875454421039382423142400 }, { target := 912, numerator := 264783088694501007131934720 }, { target := 913, numerator := 14875454421039382423142400 }, { target := 914, numerator := 235528028333123555033088000 }, { target := 915, numerator := 402133117848764638172282880 }, { target := 916, numerator := 14875454421039382423142400 }, { target := 917, numerator := 402133117848764638172282880 }, { target := 918, numerator := 402133117848764638172282880 }, { target := 919, numerator := 264783088694501007131934720 }, { target := 920, numerator := 14875454421039382423142400 }, { target := 937, numerator := 167880128466015887346892800 }, { target := 938, numerator := 2988266286695082794774691840 }, { target := 939, numerator := 167880128466015887346892800 }, { target := 940, numerator := 2658102034045251549659136000 }, { target := 941, numerator := 4538359472864629487944335360 }, { target := 942, numerator := 167880128466015887346892800 }, { target := 943, numerator := 4538359472864629487944335360 }, { target := 944, numerator := 4538359472864629487944335360 }, { target := 945, numerator := 2988266286695082794774691840 }, { target := 946, numerator := 167880128466015887346892800 }, { target := 951, numerator := 12750389503748042076979200 }, { target := 952, numerator := 226956933166715148970229760 }, { target := 953, numerator := 12750389503748042076979200 }, { target := 954, numerator := 201881167142677332885504000 }, { target := 955, numerator := 344685529584655404147671040 }, { target := 956, numerator := 12750389503748042076979200 }, { target := 957, numerator := 344685529584655404147671040 }, { target := 958, numerator := 344685529584655404147671040 }, { target := 959, numerator := 226956933166715148970229760 }, { target := 960, numerator := 12750389503748042076979200 }, { target := 965, numerator := 19807040628566084398385987584 }, { target := 982, numerator := 14875454421039382423142400 }, { target := 983, numerator := 264783088694501007131934720 }, { target := 984, numerator := 14875454421039382423142400 }, { target := 985, numerator := 235528028333123555033088000 }, { target := 986, numerator := 402133117848764638172282880 }, { target := 987, numerator := 14875454421039382423142400 }, { target := 988, numerator := 402133117848764638172282880 }, { target := 989, numerator := 402133117848764638172282880 }, { target := 990, numerator := 264783088694501007131934720 }, { target := 991, numerator := 14875454421039382423142400 }, { target := 996, numerator := 13175402487206310146211840 }, { target := 997, numerator := 234522164272272320602570752 }, { target := 998, numerator := 13175402487206310146211840 }, { target := 999, numerator := 208610539380766577315020800 }, { target := 1000, numerator := 356175047237477250952593408 }, { target := 1001, numerator := 13175402487206310146211840 }, { target := 1002, numerator := 356175047237477250952593408 }, { target := 1003, numerator := 356175047237477250952593408 }, { target := 1004, numerator := 234522164272272320602570752 }, { target := 1005, numerator := 13175402487206310146211840 }, { target := 1010, numerator := 19807040628566084398385987584 }, { target := 1015, numerator := 19807040628566084398385987584 }]

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
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left7.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left6.expected,
    Slot5.Left14.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 178053802970571884415942656 }, { target := 111, numerator := 211438891027554112743931904 }, { target := 112, numerator := 161361258942080770251948032 }, { target := 113, numerator := 1663690221506281045011464192 }, { target := 114, numerator := 200310528341893369967935488 }, { target := 115, numerator := 161361258942080770251948032 }, { target := 116, numerator := 200310528341893369967935488 }, { target := 117, numerator := 200310528341893369967935488 }, { target := 118, numerator := 8579967630644432680293236736 }, { target := 119, numerator := 200310528341893369967935488 }, { target := 120, numerator := 1663690221506281045011464192 }, { target := 121, numerator := 8579967630644432680293236736 }, { target := 122, numerator := 178053802970571884415942656 }, { target := 123, numerator := 200310528341893369967935488 }, { target := 124, numerator := 200310528341893369967935488 }, { target := 125, numerator := 211438891027554112743931904 }, { target := 206, numerator := 18668620109475580500911325184 }, { target := 207, numerator := 22168986380002251844832198656 }, { target := 208, numerator := 16918436974212244828950888448 }, { target := 209, numerator := 174434919147912455305390194688 }, { target := 210, numerator := 21002197623160028063525240832 }, { target := 211, numerator := 16918436974212244828950888448 }, { target := 212, numerator := 21002197623160028063525240832 }, { target := 213, numerator := 21002197623160028063525240832 }, { target := 214, numerator := 899594131525354535387664482304 }, { target := 215, numerator := 21002197623160028063525240832 }, { target := 216, numerator := 174434919147912455305390194688 }, { target := 217, numerator := 899594131525354535387664482304 }, { target := 218, numerator := 18668620109475580500911325184 }, { target := 219, numerator := 21002197623160028063525240832 }, { target := 220, numerator := 21002197623160028063525240832 }, { target := 221, numerator := 22168986380002251844832198656 }, { target := 257, numerator := 10562165034379946751783075840 }, { target := 260, numerator := 37785448040736457492613038080 }, { target := 262, numerator := 10562161523083758027732418560 }, { target := 353, numerator := 884360940917035601569832239104 }, { target := 356, numerator := 3163742875964174135045073666048 }, { target := 358, numerator := 884360646919243369506234433536 }, { target := 389, numerator := 30508685740935683900323135488 }, { target := 391, numerator := 30508685740935683900323135488 }, { target := 695, numerator := 884361260966478590710181265408 }, { target := 698, numerator := 3163744020919925079031463018496 }, { target := 700, numerator := 884360966968579961105386831872 }, { target := 731, numerator := 295509359832318151370301505536 }, { target := 733, numerator := 295509359832318151370301505536 }, { target := 982, numerator := 10561844984936957611434049536 }, { target := 985, numerator := 37784303084985513506223685632 }, { target := 987, numerator := 10561841473747166428580020224 }, { target := 992, numerator := 30508685740935683900323135488 }, { target := 994, numerator := 30508685740935683900323135488 }]

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
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left2.expected,
    Slot7.Left3.expected,
    Slot7.Left4.expected,
    Slot7.Left5.expected,
    Slot7.Left6.expected,
    Slot7.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 302, numerator := 201229065516299663381102592000 }, { target := 303, numerator := 238959515300605850265059328000 }, { target := 304, numerator := 182363840624146569939124224000 }, { target := 305, numerator := 1880234080917924979717177344000 }, { target := 306, numerator := 226382698705837121303740416000 }, { target := 307, numerator := 182363840624146569939124224000 }, { target := 308, numerator := 226382698705837121303740416000 }, { target := 309, numerator := 226382698705837121303740416000 }, { target := 310, numerator := 9696725594566690029176881152000 }, { target := 311, numerator := 226382698705837121303740416000 }, { target := 312, numerator := 1880234080917924979717177344000 }, { target := 313, numerator := 9696725594566690029176881152000 }, { target := 314, numerator := 201229065516299663381102592000 }, { target := 315, numerator := 226382698705837121303740416000 }, { target := 316, numerator := 226382698705837121303740416000 }, { target := 317, numerator := 238959515300605850265059328000 }, { target := 389, numerator := 8394782892875716986646036480 }, { target := 391, numerator := 8394778889932252991673335808 }, { target := 656, numerator := 200933190532702645293269647360 }, { target := 658, numerator := 200933094720313926445858553856 }, { target := 679, numerator := 18668634350362005404685172736 }, { target := 680, numerator := 22169003291054881418063642624 }, { target := 681, numerator := 16918449880015567397995937792 }, { target := 682, numerator := 174435052211194988000027082752 }, { target := 683, numerator := 21002213644157256080270819328 }, { target := 684, numerator := 16918449880015567397995937792 }, { target := 685, numerator := 21002213644157256080270819328 }, { target := 686, numerator := 21002213644157256080270819328 }, { target := 687, numerator := 899594817758069135438266761216 }, { target := 688, numerator := 21002213644157256080270819328 }, { target := 689, numerator := 174435052211194988000027082752 }, { target := 690, numerator := 899594817758069135438266761216 }, { target := 691, numerator := 18668634350362005404685172736 }, { target := 692, numerator := 21002213644157256080270819328 }, { target := 693, numerator := 21002213644157256080270819328 }, { target := 694, numerator := 22169003291054881418063642624 }, { target := 731, numerator := 150293693727291062180275814400 }, { target := 733, numerator := 150293622061690335818667786240 }, { target := 745, numerator := 174394844613289088367743467520 }, { target := 747, numerator := 174394761455366804085084782592 }, { target := 872, numerator := 8394782892875716986646036480 }, { target := 874, numerator := 8394778889932252991673335808 }, { target := 947, numerator := 174124045165131807174625853440 }, { target := 949, numerator := 174123962136336731407934029824 }, { target := 961, numerator := 174936443509603650753978695680 }, { target := 963, numerator := 174936360093426949439386288128 }, { target := 966, numerator := 178053802970571884415942656 }, { target := 967, numerator := 211438891027554112743931904 }, { target := 968, numerator := 161361258942080770251948032 }, { target := 969, numerator := 1663690221506281045011464192 }, { target := 970, numerator := 200310528341893369967935488 }, { target := 971, numerator := 161361258942080770251948032 }, { target := 972, numerator := 200310528341893369967935488 }, { target := 973, numerator := 200310528341893369967935488 }, { target := 974, numerator := 8579967630644432680293236736 }, { target := 975, numerator := 200310528341893369967935488 }, { target := 976, numerator := 1663690221506281045011464192 }, { target := 977, numerator := 8579967630644432680293236736 }, { target := 978, numerator := 178053802970571884415942656 }, { target := 979, numerator := 200310528341893369967935488 }, { target := 980, numerator := 200310528341893369967935488 }, { target := 981, numerator := 211438891027554112743931904 }, { target := 992, numerator := 8394782892875716986646036480 }, { target := 994, numerator := 8394778889932252991673335808 }]

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
    Slot7.Left8.expected,
    Slot7.Left9.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left6.expected,
    Slot8.Left14.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 2046455593160752988715745280 }, { target := 57, numerator := 34380453965100650210424520704 }, { target := 58, numerator := 74490983591051408789253128192 }, { target := 59, numerator := 2455746711792903586458894336 }, { target := 60, numerator := 39291947388686457383342309376 }, { target := 61, numerator := 2865037830425054184202043392 }, { target := 62, numerator := 74490983591051408789253128192 }, { target := 63, numerator := 74490983591051408789253128192 }, { target := 64, numerator := 39291947388686457383342309376 }, { target := 65, numerator := 919267852447810242531112779776 }, { target := 66, numerator := 73672401353787107593766830080 }, { target := 67, numerator := 34380453965100650210424520704 }, { target := 68, numerator := 74490983591051408789253128192 }, { target := 69, numerator := 2865037830425054184202043392 }, { target := 70, numerator := 73672401353787107593766830080 }, { target := 71, numerator := 2865037830425054184202043392 }, { target := 72, numerator := 74490983591051408789253128192 }, { target := 73, numerator := 74490983591051408789253128192 }, { target := 74, numerator := 2455746711792903586458894336 }, { target := 110, numerator := 2299504356705225212185018368 }, { target := 112, numerator := 84917636652357143018015293440 }, { target := 115, numerator := 84917615858170310336748453888 }, { target := 122, numerator := 2299525150892057893451857920 }, { target := 206, numerator := 339624759731447760143083634688 }, { target := 208, numerator := 12541890543030708303656166359040 }, { target := 211, numerator := 12541887471838133144069244715008 }, { target := 218, numerator := 339627830924022919730005278720 }, { target := 257, numerator := 75319101430780425899108990976 }, { target := 260, numerator := 273951807675569549051921694720 }, { target := 262, numerator := 75319101430780425899108990976 }, { target := 302, numerator := 3539852072369414602255729950720 }, { target := 304, numerator := 130722027643930639147831237017600 }, { target := 307, numerator := 130721995633404049682677125611520 }, { target := 314, numerator := 3539884082896004067409841356800 }, { target := 353, numerator := 6333526138411145678625599127552 }, { target := 356, numerator := 23036399819145116184554703421440 }, { target := 358, numerator := 6333526138411145678625599127552 }, { target := 679, numerator := 339624759731447760143083634688 }, { target := 681, numerator := 12541890543030708303656166359040 }, { target := 684, numerator := 12541887471838133144069244715008 }, { target := 691, numerator := 339627830924022919730005278720 }, { target := 695, numerator := 6333524610423369913701047992320 }, { target := 698, numerator := 23036394261524202960170935910400 }, { target := 700, numerator := 6333524610423369913701047992320 }, { target := 966, numerator := 2299504356705225212185018368 }, { target := 968, numerator := 84917636652357143018015293440 }, { target := 971, numerator := 84917615858170310336748453888 }, { target := 978, numerator := 2299525150892057893451857920 }, { target := 982, numerator := 75320629418556190823660126208 }, { target := 985, numerator := 273957365296482773435689205760 }, { target := 987, numerator := 75320629418556190823660126208 }, { target := 1006, numerator := 200933190532702645293269647360 }, { target := 1008, numerator := 200933094720313926445858553856 }, { target := 1011, numerator := 8394782892875716986646036480 }, { target := 1013, numerator := 8394778889932252991673335808 }]

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
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 152, numerator := 74164228075345470184761589760 }, { target := 153, numerator := 1245959031665803899103994707968 }, { target := 154, numerator := 2699577901942575114725321867264 }, { target := 155, numerator := 88997073690414564221713907712 }, { target := 156, numerator := 1423953179046633027547422523392 }, { target := 157, numerator := 103829919305483658258666225664 }, { target := 158, numerator := 2699577901942575114725321867264 }, { target := 159, numerator := 2699577901942575114725321867264 }, { target := 160, numerator := 1423953179046633027547422523392 }, { target := 161, numerator := 33314571251445185206994906120192 }, { target := 162, numerator := 2669912210712436926651417231360 }, { target := 163, numerator := 1245959031665803899103994707968 }, { target := 164, numerator := 2699577901942575114725321867264 }, { target := 165, numerator := 103829919305483658258666225664 }, { target := 166, numerator := 2669912210712436926651417231360 }, { target := 167, numerator := 103829919305483658258666225664 }, { target := 168, numerator := 2699577901942575114725321867264 }, { target := 169, numerator := 2699577901942575114725321867264 }, { target := 170, numerator := 88997073690414564221713907712 }, { target := 257, numerator := 85395233564003813360350003200 }, { target := 260, numerator := 293146905407302465364542095360 }, { target := 262, numerator := 85395233564003813360350003200 }, { target := 283, numerator := 74164255330409839090624102400 }, { target := 284, numerator := 1245959489550885296722484920320 }, { target := 285, numerator := 2699578894026918142898717327360 }, { target := 286, numerator := 88997106396491806908748922880 }, { target := 287, numerator := 1423953702343868910539982766080 }, { target := 288, numerator := 103829957462573774726873743360 }, { target := 289, numerator := 2699578894026918142898717327360 }, { target := 290, numerator := 2699578894026918142898717327360 }, { target := 291, numerator := 1423953702343868910539982766080 }, { target := 292, numerator := 33314583494420099719508346798080 }, { target := 293, numerator := 2669913191894754207262467686400 }, { target := 294, numerator := 1245959489550885296722484920320 }, { target := 295, numerator := 2699578894026918142898717327360 }, { target := 296, numerator := 103829957462573774726873743360 }, { target := 297, numerator := 2669913191894754207262467686400 }, { target := 298, numerator := 103829957462573774726873743360 }, { target := 299, numerator := 2699578894026918142898717327360 }, { target := 300, numerator := 2699578894026918142898717327360 }, { target := 301, numerator := 88997106396491806908748922880 }, { target := 353, numerator := 66418514994225188169161113600 }, { target := 356, numerator := 228003148650124139727977185280 }, { target := 358, numerator := 66418514994225188169161113600 }, { target := 660, numerator := 2046428338096384082853232640 }, { target := 661, numerator := 34379996080019252591934308352 }, { target := 662, numerator := 74489991506708380615857668096 }, { target := 663, numerator := 2455714005715660899423879168 }, { target := 664, numerator := 39291424091450574390782066688 }, { target := 665, numerator := 2864999673334937715994525696 }, { target := 666, numerator := 74489991506708380615857668096 }, { target := 667, numerator := 74489991506708380615857668096 }, { target := 668, numerator := 39291424091450574390782066688 }, { target := 669, numerator := 919255609472895730017672101888 }, { target := 670, numerator := 73671420171469826982716375040 }, { target := 671, numerator := 34379996080019252591934308352 }, { target := 672, numerator := 74489991506708380615857668096 }, { target := 673, numerator := 2864999673334937715994525696 }, { target := 674, numerator := 73671420171469826982716375040 }, { target := 675, numerator := 2864999673334937715994525696 }, { target := 676, numerator := 74489991506708380615857668096 }, { target := 677, numerator := 74489991506708380615857668096 }, { target := 678, numerator := 2455714005715660899423879168 }]

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

namespace RouteChunk7

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot11.Left2.expected,
    Slot11.Left3.expected,
    Slot11.Left4.expected,
    Slot11.Left5.expected,
    Slot11.Left6.expected,
    Slot11.Left7.expected,
    Slot11.Left8.expected,
    Slot11.Left9.expected,
    Slot11.Left10.expected,
    Slot11.Left11.expected,
    Slot11.Left12.expected,
    Slot11.Left13.expected,
    Slot11.Left14.expected,
    Slot11.Left15.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 3094952843294817121097220096 }, { target := 112, numerator := 116285329030960959426995945472 }, { target := 115, numerator := 116276534125513203366645202944 }, { target := 122, numerator := 3103747748742573181447962624 }, { target := 206, numerator := 494100534092909263503985999872 }, { target := 208, numerator := 18564626374145477460105262792704 }, { target := 211, numerator := 18563222292177492864449441169408 }, { target := 218, numerator := 495504616060893859159807623168 }, { target := 302, numerator := 4930380301427014684021780119552 }, { target := 304, numerator := 185247053712409301941732679614464 }, { target := 307, numerator := 185233043085828521096606203772928 }, { target := 314, numerator := 4944390928007795529148255961088 }, { target := 379, numerator := 75906874279114500764755558400 }, { target := 382, numerator := 260575027028713302546259640320 }, { target := 384, numerator := 75906874279114500764755558400 }, { target := 524, numerator := 89190577277959538398587781120 }, { target := 527, numerator := 306175656758738130491855077376 }, { target := 529, numerator := 89190577277959538398587781120 }, { target := 620, numerator := 1053207880622713698110983372800 }, { target := 623, numerator := 3615478500023397072829352509440 }, { target := 625, numerator := 1053207880622713698110983372800 }, { target := 646, numerator := 2368294477508372423860373422080 }, { target := 649, numerator := 8129940843295855039443300777984 }, { target := 651, numerator := 2368294477508372423860373422080 }, { target := 679, numerator := 494100534092909263503985999872 }, { target := 681, numerator := 18564626374145477460105262792704 }, { target := 684, numerator := 18563222292177492864449441169408 }, { target := 691, numerator := 495504616060893859159807623168 }, { target := 695, numerator := 66418514994225188169161113600 }, { target := 698, numerator := 228003148650124139727977185280 }, { target := 700, numerator := 66418514994225188169161113600 }, { target := 721, numerator := 1053207880622713698110983372800 }, { target := 724, numerator := 3615478500023397072829352509440 }, { target := 726, numerator := 1053207880622713698110983372800 }, { target := 735, numerator := 75906874279114500764755558400 }, { target := 738, numerator := 260575027028713302546259640320 }, { target := 740, numerator := 75906874279114500764755558400 }, { target := 836, numerator := 74009202422136638245636669440 }, { target := 839, numerator := 254060651352995469982603149312 }, { target := 841, numerator := 74009202422136638245636669440 }, { target := 862, numerator := 74009202422136638245636669440 }, { target := 865, numerator := 254060651352995469982603149312 }, { target := 867, numerator := 74009202422136638245636669440 }, { target := 911, numerator := 74009202422136638245636669440 }, { target := 914, numerator := 254060651352995469982603149312 }, { target := 916, numerator := 74009202422136638245636669440 }, { target := 937, numerator := 2368294477508372423860373422080 }, { target := 940, numerator := 8129940843295855039443300777984 }, { target := 942, numerator := 2368294477508372423860373422080 }, { target := 951, numerator := 74009202422136638245636669440 }, { target := 954, numerator := 254060651352995469982603149312 }, { target := 956, numerator := 74009202422136638245636669440 }, { target := 966, numerator := 3094599699428626475601887232 }, { target := 968, numerator := 116272060508707312580872372224 }, { target := 971, numerator := 116263266606785965438374248448 }, { target := 978, numerator := 3103393601349973618100011008 }, { target := 982, numerator := 85395233564003813360350003200 }, { target := 985, numerator := 293146905407302465364542095360 }, { target := 987, numerator := 85395233564003813360350003200 }, { target := 996, numerator := 89190577277959538398587781120 }, { target := 999, numerator := 306175656758738130491855077376 }, { target := 1001, numerator := 89190577277959538398587781120 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk7

namespace RouteChunk8

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 84914584969834936362074112000 }, { target := 15, numerator := 66044677198760506059390976000 }, { target := 16, numerator := 75479631084297721210732544000 }, { target := 17, numerator := 88688566524049822422610739200 }, { target := 18, numerator := 1047279881294630881798914048000 }, { target := 19, numerator := 2354964489830088901774855372800 }, { target := 20, numerator := 66044677198760506059390976000 }, { target := 21, numerator := 1047279881294630881798914048000 }, { target := 22, numerator := 75479631084297721210732544000 }, { target := 23, numerator := 73592640307190278180464230400 }, { target := 24, numerator := 73592640307190278180464230400 }, { target := 25, numerator := 73592640307190278180464230400 }, { target := 26, numerator := 2354964489830088901774855372800 }, { target := 27, numerator := 73592640307190278180464230400 }, { target := 28, numerator := 84914584969834936362074112000 }, { target := 29, numerator := 88688566524049822422610739200 }, { target := 56, numerator := 3100317642815175618447015936 }, { target := 57, numerator := 494957009277677696964731338752 }, { target := 59, numerator := 4938926635802863210081793605632 }, { target := 67, numerator := 494957009277677696964731338752 }, { target := 74, numerator := 3099963886808464621685440512 }, { target := 136, numerator := 291496922825272620343728537600 }, { target := 137, numerator := 226719828864100926934011084800 }, { target := 138, numerator := 259108375844686773638869811200 }, { target := 139, numerator := 304452341617506959025672028160 }, { target := 140, numerator := 3595128714845028984239318630400 }, { target := 141, numerator := 8084181326354227337532738109440 }, { target := 142, numerator := 226719828864100926934011084800 }, { target := 143, numerator := 3595128714845028984239318630400 }, { target := 144, numerator := 259108375844686773638869811200 }, { target := 145, numerator := 252630666448569604297898065920 }, { target := 146, numerator := 252630666448569604297898065920 }, { target := 147, numerator := 252630666448569604297898065920 }, { target := 148, numerator := 8084181326354227337532738109440 }, { target := 149, numerator := 252630666448569604297898065920 }, { target := 150, numerator := 291496922825272620343728537600 }, { target := 151, numerator := 304452341617506959025672028160 }, { target := 152, numerator := 116486898330719948782910308352 }, { target := 153, numerator := 18596806347059579518451779108864 }, { target := 155, numerator := 185568161449820307838667560321024 }, { target := 163, numerator := 18596806347059579518451779108864 }, { target := 170, numerator := 116473606808774407939826909184 }, { target := 283, numerator := 116478088180159612108830408704 }, { target := 284, numerator := 18595399831252163505573465161728 }, { target := 286, numerator := 185554126537182011339450034946048 }, { target := 294, numerator := 18595399831252163505573465161728 }, { target := 301, numerator := 116464797663479995539671482368 }, { target := 660, numerator := 3109127793375512292526915584 }, { target := 661, numerator := 496363525085093709843045285888 }, { target := 663, numerator := 4952961548441159709299318980608 }, { target := 671, numerator := 496363525085093709843045285888 }, { target := 678, numerator := 3108773032102877021840867328 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk8

namespace RouteChunk9

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left2.expected,
    Slot15.Left3.expected,
    Slot15.Left4.expected,
    Slot15.Left5.expected,
    Slot15.Left6.expected,
    Slot15.Left7.expected,
    Slot15.Left8.expected,
    Slot15.Left9.expected,
    Slot15.Left10.expected,
    Slot15.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 2065933279643881982897684480 }, { target := 112, numerator := 74870105880631118695403356160 }, { target := 115, numerator := 74870133395102826137806438400 }, { target := 122, numerator := 2065905765172174540494602240 }, { target := 206, numerator := 34707679098017217312681099264 }, { target := 208, numerator := 1257817778794602794082776383488 }, { target := 211, numerator := 1257818241037727479115148165120 }, { target := 218, numerator := 34707216854892532280309317632 }, { target := 241, numerator := 75199971379037304177475715072 }, { target := 243, numerator := 2725271854054972720512682164224 }, { target := 246, numerator := 2725272855581742871416154357760 }, { target := 253, numerator := 75198969852267153274003521536 }, { target := 267, numerator := 84914584969834936362074112000 }, { target := 268, numerator := 66044677198760506059390976000 }, { target := 269, numerator := 75479631084297721210732544000 }, { target := 270, numerator := 88688566524049822422610739200 }, { target := 271, numerator := 1047279881294630881798914048000 }, { target := 272, numerator := 2354964489830088901774855372800 }, { target := 273, numerator := 66044677198760506059390976000 }, { target := 274, numerator := 1047279881294630881798914048000 }, { target := 275, numerator := 75479631084297721210732544000 }, { target := 276, numerator := 73592640307190278180464230400 }, { target := 277, numerator := 73592640307190278180464230400 }, { target := 278, numerator := 73592640307190278180464230400 }, { target := 279, numerator := 2354964489830088901774855372800 }, { target := 280, numerator := 73592640307190278180464230400 }, { target := 281, numerator := 84914584969834936362074112000 }, { target := 282, numerator := 88688566524049822422610739200 }, { target := 302, numerator := 2479119935572658379477221376 }, { target := 304, numerator := 89844127056757342434484027392 }, { target := 307, numerator := 89844160074123391365367726080 }, { target := 314, numerator := 2479086918206609448593522688 }, { target := 337, numerator := 39665918969162534071635542016 }, { target := 339, numerator := 1437506032908117478951744438272 }, { target := 342, numerator := 1437506561185974261845883617280 }, { target := 349, numerator := 39665390691305751177496363008 }, { target := 363, numerator := 2892306591501434776056758272 }, { target := 365, numerator := 104818148232883566173564698624 }, { target := 368, numerator := 104818186753143956592929013760 }, { target := 375, numerator := 2892268071241044356692443136 }, { target := 473, numerator := 75199971379037304177475715072 }, { target := 475, numerator := 2725271854054972720512682164224 }, { target := 478, numerator := 2725272855581742871416154357760 }, { target := 485, numerator := 75198969852267153274003521536 }, { target := 508, numerator := 75199971379037304177475715072 }, { target := 510, numerator := 2725271854054972720512682164224 }, { target := 513, numerator := 2725272855581742871416154357760 }, { target := 520, numerator := 75198969852267153274003521536 }, { target := 569, numerator := 39665918969162534071635542016 }, { target := 571, numerator := 1437506032908117478951744438272 }, { target := 574, numerator := 1437506561185974261845883617280 }, { target := 581, numerator := 39665390691305751177496363008 }, { target := 604, numerator := 928017229216031786717639868416 }, { target := 606, numerator := 33631651561579498517975187587072 }, { target := 609, numerator := 33631663921080189501102652129280 }, { target := 616, numerator := 928004869715340803590175326208 }, { target := 630, numerator := 74373598067179751384316641280 }, { target := 632, numerator := 2695323811702720273034520821760 }, { target := 635, numerator := 2695324802223701740961031782400 }, { target := 642, numerator := 74372607546198283457805680640 }, { target := 679, numerator := 34707679098017217312681099264 }, { target := 681, numerator := 1257817778794602794082776383488 }, { target := 684, numerator := 1257818241037727479115148165120 }, { target := 691, numerator := 34707216854892532280309317632 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk9

namespace RouteChunk10

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot15.Left12.expected,
    Slot15.Left13.expected,
    Slot15.Left14.expected,
    Slot15.Left15.expected,
    Slot15.Left16.expected,
    Slot15.Left17.expected,
    Slot15.Left18.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot16.Left5.expected,
    Slot16.Left12.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 74906167760655533213258612736 }, { target := 15, numerator := 6298802859143540713282257027072 }, { target := 20, numerator := 6298801339532890911981195755520 }, { target := 28, numerator := 74907687371305334514319884288 }, { target := 56, numerator := 2295524007917654347574411264 }, { target := 57, numerator := 339036883045463552843132698624 }, { target := 59, numerator := 3533724731986974962736494018560 }, { target := 67, numerator := 339036883045463552843132698624 }, { target := 74, numerator := 2295524007917654347574411264 }, { target := 136, numerator := 272449878905418400208435281920 }, { target := 137, numerator := 22910103767505066205472714915840 }, { target := 142, numerator := 22910098240353565882538419814400 }, { target := 150, numerator := 272455406056918723142730383360 }, { target := 152, numerator := 84770647667053854194789253120 }, { target := 153, numerator := 12520181039123385119154288721920 }, { target := 155, numerator := 130495753115367950108752399564800 }, { target := 163, numerator := 12520181039123385119154288721920 }, { target := 170, numerator := 84770647667053854194789253120 }, { target := 267, numerator := 74906167760655533213258612736 }, { target := 268, numerator := 6298802859143540713282257027072 }, { target := 273, numerator := 6298801339532890911981195755520 }, { target := 281, numerator := 74907687371305334514319884288 }, { target := 283, numerator := 84770626908860915635374260224 }, { target := 284, numerator := 12520177973246919758310470057984 }, { target := 286, numerator := 130495721160250284018043411496960 }, { target := 294, numerator := 12520177973246919758310470057984 }, { target := 301, numerator := 84770626908860915635374260224 }, { target := 660, numerator := 2295544766110592906989404160 }, { target := 661, numerator := 339039948921928913686951362560 }, { target := 663, numerator := 3533756687104641053445482086400 }, { target := 671, numerator := 339039948921928913686951362560 }, { target := 678, numerator := 2295544766110592906989404160 }, { target := 705, numerator := 75199971379037304177475715072 }, { target := 707, numerator := 2725271854054972720512682164224 }, { target := 710, numerator := 2725272855581742871416154357760 }, { target := 717, numerator := 75198969852267153274003521536 }, { target := 785, numerator := 2892306591501434776056758272 }, { target := 787, numerator := 104818148232883566173564698624 }, { target := 790, numerator := 104818186753143956592929013760 }, { target := 797, numerator := 2892268071241044356692443136 }, { target := 820, numerator := 74373598067179751384316641280 }, { target := 822, numerator := 2695323811702720273034520821760 }, { target := 825, numerator := 2695324802223701740961031782400 }, { target := 832, numerator := 74372607546198283457805680640 }, { target := 846, numerator := 2892306591501434776056758272 }, { target := 848, numerator := 104818148232883566173564698624 }, { target := 851, numerator := 104818186753143956592929013760 }, { target := 858, numerator := 2892268071241044356692443136 }, { target := 895, numerator := 75199971379037304177475715072 }, { target := 897, numerator := 2725271854054972720512682164224 }, { target := 900, numerator := 2725272855581742871416154357760 }, { target := 907, numerator := 75198969852267153274003521536 }, { target := 921, numerator := 75199971379037304177475715072 }, { target := 923, numerator := 2725271854054972720512682164224 }, { target := 926, numerator := 2725272855581742871416154357760 }, { target := 933, numerator := 75198969852267153274003521536 }, { target := 966, numerator := 2479119935572658379477221376 }, { target := 968, numerator := 89844127056757342434484027392 }, { target := 971, numerator := 89844160074123391365367726080 }, { target := 978, numerator := 2479086918206609448593522688 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk10

namespace RouteChunk11

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot19.Left0.expected,
    Slot19.Left1.expected,
    Slot19.Left2.expected,
    Slot19.Left3.expected,
    Slot19.Left4.expected,
    Slot19.Left5.expected,
    Slot19.Left6.expected,
    Slot19.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 8094969218130155665694392320 }, { target := 5, numerator := 193757005156534693675652874240 }, { target := 6, numerator := 144926061808459238530980249600 }, { target := 7, numerator := 168166457305671620926038343680 }, { target := 8, numerator := 8094969218130155665694392320 }, { target := 9, numerator := 167905329266377099775532072960 }, { target := 10, numerator := 168688713384260663227050885120 }, { target := 11, numerator := 8094969218130155665694392320 }, { target := 12, numerator := 193757005156534693675652874240 }, { target := 13, numerator := 8094969218130155665694392320 }, { target := 56, numerator := 173902289429807254986555392 }, { target := 57, numerator := 18233341402259828623947071488 }, { target := 59, numerator := 196537196113069878483615744000 }, { target := 67, numerator := 18233355311104860200948989952 }, { target := 74, numerator := 173902289429807254986555392 }, { target := 91, numerator := 206508968697896115296534528 }, { target := 92, numerator := 21652092915183546490937147392 }, { target := 94, numerator := 233387920384270480699293696000 }, { target := 102, numerator := 21652109431937021488626925568 }, { target := 109, numerator := 206508968697896115296534528 }, { target := 126, numerator := 8094965358148958241970716672 }, { target := 127, numerator := 193756912766017000501363605504 }, { target := 128, numerator := 144925992702344252396572508160 }, { target := 129, numerator := 168166377117675132510617468928 }, { target := 130, numerator := 8094965358148958241970716672 }, { target := 131, numerator := 167905249202896133857650671616 }, { target := 132, numerator := 168688632947233129816551063552 }, { target := 133, numerator := 8094965358148958241970716672 }, { target := 134, numerator := 193756912766017000501363605504 }, { target := 135, numerator := 8094965358148958241970716672 }, { target := 152, numerator := 157598949795762824831565824 }, { target := 153, numerator := 16523965645797969690452033536 }, { target := 155, numerator := 178111833977469577375776768000 }, { target := 163, numerator := 16523978250688779557110022144 }, { target := 170, numerator := 157598949795762824831565824 }, { target := 187, numerator := 1624899516859761538780626944 }, { target := 188, numerator := 170367783727365273705005449216 }, { target := 190, numerator := 1836394426181496677081284608000 }, { target := 198, numerator := 170367913688136037502617124864 }, { target := 205, numerator := 1624899516859761538780626944 }, { target := 222, numerator := 195640075608533161859874816 }, { target := 223, numerator := 20512509077542307201940455424 }, { target := 225, numerator := 221104345627203613294067712000 }, { target := 233, numerator := 20512524724992967726067613696 }, { target := 240, numerator := 195640075608533161859874816 }, { target := 283, numerator := 157598949795762824831565824 }, { target := 284, numerator := 16523965645797969690452033536 }, { target := 286, numerator := 178111833977469577375776768000 }, { target := 294, numerator := 16523978250688779557110022144 }, { target := 301, numerator := 157598949795762824831565824 }, { target := 318, numerator := 195640075608533161859874816 }, { target := 319, numerator := 20512509077542307201940455424 }, { target := 321, numerator := 221104345627203613294067712000 }, { target := 329, numerator := 20512524724992967726067613696 }, { target := 336, numerator := 195640075608533161859874816 }, { target := 419, numerator := 195640075608533161859874816 }, { target := 420, numerator := 20512509077542307201940455424 }, { target := 422, numerator := 221104345627203613294067712000 }, { target := 430, numerator := 20512524724992967726067613696 }, { target := 437, numerator := 195640075608533161859874816 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk11

namespace RouteChunk12

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot19.Left8.expected,
    Slot19.Left9.expected,
    Slot19.Left10.expected,
    Slot19.Left11.expected,
    Slot19.Left12.expected,
    Slot19.Left13.expected,
    Slot19.Left14.expected,
    Slot19.Left15.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected,
    Slot20.Left5.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 30508685740935683900323135488 }, { target := 6, numerator := 295509359832318151370301505536 }, { target := 11, numerator := 30508685740935683900323135488 }, { target := 14, numerator := 10562165034379946751783075840 }, { target := 15, numerator := 884360940917035601569832239104 }, { target := 20, numerator := 884361260966478590710181265408 }, { target := 28, numerator := 10561844984936957611434049536 }, { target := 126, numerator := 30508685740935683900323135488 }, { target := 128, numerator := 295509359832318151370301505536 }, { target := 133, numerator := 30508685740935683900323135488 }, { target := 136, numerator := 37785448040736457492613038080 }, { target := 137, numerator := 3163742875964174135045073666048 }, { target := 142, numerator := 3163744020919925079031463018496 }, { target := 150, numerator := 37784303084985513506223685632 }, { target := 267, numerator := 10562161523083758027732418560 }, { target := 268, numerator := 884360646919243369506234433536 }, { target := 273, numerator := 884360966968579961105386831872 }, { target := 281, numerator := 10561841473747166428580020224 }, { target := 454, numerator := 8379916571898837099664637952 }, { target := 455, numerator := 878619138821395491816449507328 }, { target := 457, numerator := 9470636137698554769429233664000 }, { target := 465, numerator := 878619809053865450933229453312 }, { target := 472, numerator := 8379916571898837099664637952 }, { target := 489, numerator := 195640075608533161859874816 }, { target := 490, numerator := 20512509077542307201940455424 }, { target := 492, numerator := 221104345627203613294067712000 }, { target := 500, numerator := 20512524724992967726067613696 }, { target := 507, numerator := 195640075608533161859874816 }, { target := 550, numerator := 1624899516859761538780626944 }, { target := 551, numerator := 170367783727365273705005449216 }, { target := 553, numerator := 1836394426181496677081284608000 }, { target := 561, numerator := 170367913688136037502617124864 }, { target := 568, numerator := 1624899516859761538780626944 }, { target := 585, numerator := 8379916571898837099664637952 }, { target := 586, numerator := 878619138821395491816449507328 }, { target := 588, numerator := 9470636137698554769429233664000 }, { target := 596, numerator := 878619809053865450933229453312 }, { target := 603, numerator := 8379916571898837099664637952 }, { target := 660, numerator := 173902289429807254986555392 }, { target := 661, numerator := 18233341402259828623947071488 }, { target := 663, numerator := 196537196113069878483615744000 }, { target := 671, numerator := 18233355311104860200948989952 }, { target := 678, numerator := 173902289429807254986555392 }, { target := 766, numerator := 195640075608533161859874816 }, { target := 767, numerator := 20512509077542307201940455424 }, { target := 769, numerator := 221104345627203613294067712000 }, { target := 777, numerator := 20512524724992967726067613696 }, { target := 784, numerator := 195640075608533161859874816 }, { target := 801, numerator := 195640075608533161859874816 }, { target := 802, numerator := 20512509077542307201940455424 }, { target := 804, numerator := 221104345627203613294067712000 }, { target := 812, numerator := 20512524724992967726067613696 }, { target := 819, numerator := 195640075608533161859874816 }, { target := 876, numerator := 206508968697896115296534528 }, { target := 877, numerator := 21652092915183546490937147392 }, { target := 879, numerator := 233387920384270480699293696000 }, { target := 887, numerator := 21652109431937021488626925568 }, { target := 894, numerator := 206508968697896115296534528 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk12

namespace RouteChunk13

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot23.Left0.expected,
    Slot23.Left1.expected,
    Slot23.Left2.expected,
    Slot23.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 14875454421039382423142400 }, { target := 15, numerator := 15300467404497650492375040 }, { target := 16, numerator := 14875454421039382423142400 }, { target := 17, numerator := 13175402487206310146211840 }, { target := 18, numerator := 616693838997946968456560640 }, { target := 19, numerator := 167880128466015887346892800 }, { target := 20, numerator := 15300467404497650492375040 }, { target := 21, numerator := 616693838997946968456560640 }, { target := 22, numerator := 14875454421039382423142400 }, { target := 23, numerator := 14875454421039382423142400 }, { target := 24, numerator := 12750389503748042076979200 }, { target := 25, numerator := 14875454421039382423142400 }, { target := 26, numerator := 167880128466015887346892800 }, { target := 27, numerator := 12750389503748042076979200 }, { target := 28, numerator := 14875454421039382423142400 }, { target := 29, numerator := 13175402487206310146211840 }, { target := 40, numerator := 264783088694501007131934720 }, { target := 41, numerator := 272348319800058178764275712 }, { target := 42, numerator := 264783088694501007131934720 }, { target := 43, numerator := 234522164272272320602570752 }, { target := 44, numerator := 10977150334163456038526779392 }, { target := 45, numerator := 2988266286695082794774691840 }, { target := 46, numerator := 272348319800058178764275712 }, { target := 47, numerator := 10977150334163456038526779392 }, { target := 48, numerator := 264783088694501007131934720 }, { target := 49, numerator := 264783088694501007131934720 }, { target := 50, numerator := 226956933166715148970229760 }, { target := 51, numerator := 264783088694501007131934720 }, { target := 52, numerator := 2988266286695082794774691840 }, { target := 53, numerator := 226956933166715148970229760 }, { target := 54, numerator := 264783088694501007131934720 }, { target := 55, numerator := 234522164272272320602570752 }, { target := 75, numerator := 14875454421039382423142400 }, { target := 76, numerator := 15300467404497650492375040 }, { target := 77, numerator := 14875454421039382423142400 }, { target := 78, numerator := 13175402487206310146211840 }, { target := 79, numerator := 616693838997946968456560640 }, { target := 80, numerator := 167880128466015887346892800 }, { target := 81, numerator := 15300467404497650492375040 }, { target := 82, numerator := 616693838997946968456560640 }, { target := 83, numerator := 14875454421039382423142400 }, { target := 84, numerator := 14875454421039382423142400 }, { target := 85, numerator := 12750389503748042076979200 }, { target := 86, numerator := 14875454421039382423142400 }, { target := 87, numerator := 167880128466015887346892800 }, { target := 88, numerator := 12750389503748042076979200 }, { target := 89, numerator := 14875454421039382423142400 }, { target := 90, numerator := 13175402487206310146211840 }, { target := 136, numerator := 235528028333123555033088000 }, { target := 137, numerator := 242257400571212799462604800 }, { target := 138, numerator := 235528028333123555033088000 }, { target := 139, numerator := 208610539380766577315020800 }, { target := 140, numerator := 9764319117467493667228876800 }, { target := 141, numerator := 2658102034045251549659136000 }, { target := 142, numerator := 242257400571212799462604800 }, { target := 143, numerator := 9764319117467493667228876800 }, { target := 144, numerator := 235528028333123555033088000 }, { target := 145, numerator := 235528028333123555033088000 }, { target := 146, numerator := 201881167142677332885504000 }, { target := 147, numerator := 235528028333123555033088000 }, { target := 148, numerator := 2658102034045251549659136000 }, { target := 149, numerator := 201881167142677332885504000 }, { target := 150, numerator := 235528028333123555033088000 }, { target := 151, numerator := 208610539380766577315020800 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk13

namespace RouteChunk14

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot23.Left4.expected,
    Slot23.Left5.expected,
    Slot23.Left6.expected,
    Slot23.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 171, numerator := 402133117848764638172282880 }, { target := 172, numerator := 413622635501586484977205248 }, { target := 173, numerator := 402133117848764638172282880 }, { target := 174, numerator := 356175047237477250952593408 }, { target := 175, numerator := 16671290114244499713942355968 }, { target := 176, numerator := 4538359472864629487944335360 }, { target := 177, numerator := 413622635501586484977205248 }, { target := 178, numerator := 16671290114244499713942355968 }, { target := 179, numerator := 402133117848764638172282880 }, { target := 180, numerator := 402133117848764638172282880 }, { target := 181, numerator := 344685529584655404147671040 }, { target := 182, numerator := 402133117848764638172282880 }, { target := 183, numerator := 4538359472864629487944335360 }, { target := 184, numerator := 344685529584655404147671040 }, { target := 185, numerator := 402133117848764638172282880 }, { target := 186, numerator := 356175047237477250952593408 }, { target := 267, numerator := 14875454421039382423142400 }, { target := 268, numerator := 15300467404497650492375040 }, { target := 269, numerator := 14875454421039382423142400 }, { target := 270, numerator := 13175402487206310146211840 }, { target := 271, numerator := 616693838997946968456560640 }, { target := 272, numerator := 167880128466015887346892800 }, { target := 273, numerator := 15300467404497650492375040 }, { target := 274, numerator := 616693838997946968456560640 }, { target := 275, numerator := 14875454421039382423142400 }, { target := 276, numerator := 14875454421039382423142400 }, { target := 277, numerator := 12750389503748042076979200 }, { target := 278, numerator := 14875454421039382423142400 }, { target := 279, numerator := 167880128466015887346892800 }, { target := 280, numerator := 12750389503748042076979200 }, { target := 281, numerator := 14875454421039382423142400 }, { target := 282, numerator := 13175402487206310146211840 }, { target := 403, numerator := 402133117848764638172282880 }, { target := 404, numerator := 413622635501586484977205248 }, { target := 405, numerator := 402133117848764638172282880 }, { target := 406, numerator := 356175047237477250952593408 }, { target := 407, numerator := 16671290114244499713942355968 }, { target := 408, numerator := 4538359472864629487944335360 }, { target := 409, numerator := 413622635501586484977205248 }, { target := 410, numerator := 16671290114244499713942355968 }, { target := 411, numerator := 402133117848764638172282880 }, { target := 412, numerator := 402133117848764638172282880 }, { target := 413, numerator := 344685529584655404147671040 }, { target := 414, numerator := 402133117848764638172282880 }, { target := 415, numerator := 4538359472864629487944335360 }, { target := 416, numerator := 344685529584655404147671040 }, { target := 417, numerator := 402133117848764638172282880 }, { target := 418, numerator := 356175047237477250952593408 }, { target := 438, numerator := 402133117848764638172282880 }, { target := 439, numerator := 413622635501586484977205248 }, { target := 440, numerator := 402133117848764638172282880 }, { target := 441, numerator := 356175047237477250952593408 }, { target := 442, numerator := 16671290114244499713942355968 }, { target := 443, numerator := 4538359472864629487944335360 }, { target := 444, numerator := 413622635501586484977205248 }, { target := 445, numerator := 16671290114244499713942355968 }, { target := 446, numerator := 402133117848764638172282880 }, { target := 447, numerator := 402133117848764638172282880 }, { target := 448, numerator := 344685529584655404147671040 }, { target := 449, numerator := 402133117848764638172282880 }, { target := 450, numerator := 4538359472864629487944335360 }, { target := 451, numerator := 344685529584655404147671040 }, { target := 452, numerator := 402133117848764638172282880 }, { target := 453, numerator := 356175047237477250952593408 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk14

namespace RouteChunk15

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot23.Left8.expected,
    Slot23.Left9.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 241785163922925834941235200 }, { target := 5, numerator := 4845374685015433732222353408 }, { target := 6, numerator := 8133652914367225087423152128 }, { target := 7, numerator := 7804825091432045951903072256 }, { target := 8, numerator := 241785163922925834941235200 }, { target := 9, numerator := 7804825091432045951903072256 }, { target := 10, numerator := 5212888134178281001333030912 }, { target := 11, numerator := 251456570479842868338884608 }, { target := 12, numerator := 4845374685015433732222353408 }, { target := 13, numerator := 232113757366008801543585792 }, { target := 126, numerator := 241785163922925834941235200 }, { target := 127, numerator := 4845374685015433732222353408 }, { target := 128, numerator := 8133652914367225087423152128 }, { target := 129, numerator := 7804825091432045951903072256 }, { target := 130, numerator := 241785163922925834941235200 }, { target := 131, numerator := 7804825091432045951903072256 }, { target := 132, numerator := 5212888134178281001333030912 }, { target := 133, numerator := 251456570479842868338884608 }, { target := 134, numerator := 4845374685015433732222353408 }, { target := 135, numerator := 232113757366008801543585792 }, { target := 534, numerator := 264783088694501007131934720 }, { target := 535, numerator := 272348319800058178764275712 }, { target := 536, numerator := 264783088694501007131934720 }, { target := 537, numerator := 234522164272272320602570752 }, { target := 538, numerator := 10977150334163456038526779392 }, { target := 539, numerator := 2988266286695082794774691840 }, { target := 540, numerator := 272348319800058178764275712 }, { target := 541, numerator := 10977150334163456038526779392 }, { target := 542, numerator := 264783088694501007131934720 }, { target := 543, numerator := 264783088694501007131934720 }, { target := 544, numerator := 226956933166715148970229760 }, { target := 545, numerator := 264783088694501007131934720 }, { target := 546, numerator := 2988266286695082794774691840 }, { target := 547, numerator := 226956933166715148970229760 }, { target := 548, numerator := 264783088694501007131934720 }, { target := 549, numerator := 234522164272272320602570752 }, { target := 750, numerator := 14875454421039382423142400 }, { target := 751, numerator := 15300467404497650492375040 }, { target := 752, numerator := 14875454421039382423142400 }, { target := 753, numerator := 13175402487206310146211840 }, { target := 754, numerator := 616693838997946968456560640 }, { target := 755, numerator := 167880128466015887346892800 }, { target := 756, numerator := 15300467404497650492375040 }, { target := 757, numerator := 616693838997946968456560640 }, { target := 758, numerator := 14875454421039382423142400 }, { target := 759, numerator := 14875454421039382423142400 }, { target := 760, numerator := 12750389503748042076979200 }, { target := 761, numerator := 14875454421039382423142400 }, { target := 762, numerator := 167880128466015887346892800 }, { target := 763, numerator := 12750389503748042076979200 }, { target := 764, numerator := 14875454421039382423142400 }, { target := 765, numerator := 13175402487206310146211840 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk15

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15.Parent0
