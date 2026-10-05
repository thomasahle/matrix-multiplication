import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk13Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 1,
parent 57; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 24, #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0], #[2473901162496, 2817498546176, 2199023255552, 29480655519744, 2611340115968, 2199023255552, 2611340115968, 2542620639232, 96069828476928, 2542620639232, 29480655519744, 96069828476928, 2473901162496, 2542620639232, 2542620639232, 2817498546176, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 200, numerator := 191765858136370552837767168 }, some { target := 201, numerator := 218400005099755351843012608 }, some { target := 202, numerator := 170458540565662713633570816 }, some { target := 203, numerator := 2285209809458415754650058752 }, some { target := 204, numerator := 202419516921724472439865344 }, some { target := 205, numerator := 170458540565662713633570816 }, some { target := 206, numerator := 202419516921724472439865344 }, some { target := 207, numerator := 197092687529047512638816256 }, some { target := 208, numerator := 7446907490962389801866625024 }, some { target := 209, numerator := 197092687529047512638816256 }, some { target := 210, numerator := 2285209809458415754650058752 }, some { target := 211, numerator := 7446907490962389801866625024 }, some { target := 212, numerator := 191765858136370552837767168 }, some { target := 213, numerator := 197092687529047512638816256 }, some { target := 214, numerator := 197092687529047512638816256 }, some { target := 215, numerator := 218400005099755351843012608 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 296, numerator := 142804362441978071262167040 }, some { target := 297, numerator := 162638301670030581159690240 }, some { target := 298, numerator := 126937211059536063344148480 }, some { target := 299, numerator := 1701751985766905349207490560 }, some { target := 300, numerator := 150737938133199075221176320 }, some { target := 301, numerator := 126937211059536063344148480 }, some { target := 302, numerator := 150737938133199075221176320 }, some { target := 303, numerator := 146771150287588573241671680 }, some { target := 304, numerator := 5545569408163481767347486720 }, some { target := 305, numerator := 146771150287588573241671680 }, some { target := 306, numerator := 1701751985766905349207490560 }, some { target := 307, numerator := 5545569408163481767347486720 }, some { target := 308, numerator := 142804362441978071262167040 }, some { target := 309, numerator := 146771150287588573241671680 }, some { target := 310, numerator := 146771150287588573241671680 }, some { target := 311, numerator := 162638301670030581159690240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 331, numerator := 150964611724376818191433728 }, some { target := 332, numerator := 171931918908318042940243968 }, some { target := 333, numerator := 134190765977223838392385536 }, some { target := 334, numerator := 1798994956382157083447918592 }, some { target := 335, numerator := 159351534597953308090957824 }, some { target := 336, numerator := 134190765977223838392385536 }, some { target := 337, numerator := 159351534597953308090957824 }, some { target := 338, numerator := 155158073161165063141195776 }, some { target := 339, numerator := 5862459088629966439767343104 }, some { target := 340, numerator := 155158073161165063141195776 }, some { target := 341, numerator := 1798994956382157083447918592 }, some { target := 342, numerator := 5862459088629966439767343104 }, some { target := 343, numerator := 150964611724376818191433728 }, some { target := 344, numerator := 155158073161165063141195776 }, some { target := 345, numerator := 155158073161165063141195776 }, some { target := 346, numerator := 171931918908318042940243968 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 467, numerator := 195845982777569926302400512 }, some { target := 468, numerator := 223046813718899082733289472 }, some { target := 469, numerator := 174085318024506601157689344 }, some { target := 470, numerator := 2333831294766041621770272768 }, some { target := 471, numerator := 206726315154101588874756096 }, some { target := 472, numerator := 174085318024506601157689344 }, some { target := 473, numerator := 206726315154101588874756096 }, some { target := 474, numerator := 201286148965835757588578304 }, some { target := 475, numerator := 7605352331195632138076553216 }, some { target := 476, numerator := 201286148965835757588578304 }, some { target := 477, numerator := 2333831294766041621770272768 }, some { target := 478, numerator := 7605352331195632138076553216 }, some { target := 479, numerator := 195845982777569926302400512 }, some { target := 480, numerator := 201286148965835757588578304 }, some { target := 481, numerator := 201286148965835757588578304 }, some { target := 482, numerator := 223046813718899082733289472 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 563, numerator := 2623520144291197137759240192 }, some { target := 564, numerator := 2987897942109418962448023552 }, some { target := 565, numerator := 2332017906036619678008213504 }, some { target := 566, numerator := 31263615052803432558297612288 }, some { target := 567, numerator := 2769271263418485867634753536 }, some { target := 568, numerator := 2332017906036619678008213504 }, some { target := 569, numerator := 2769271263418485867634753536 }, some { target := 570, numerator := 2696395703854841502696996864 }, some { target := 571, numerator := 101880032269974822182983827456 }, some { target := 572, numerator := 2696395703854841502696996864 }, some { target := 573, numerator := 31263615052803432558297612288 }, some { target := 574, numerator := 101880032269974822182983827456 }, some { target := 575, numerator := 2623520144291197137759240192 }, some { target := 576, numerator := 2696395703854841502696996864 }, some { target := 577, numerator := 2696395703854841502696996864 }, some { target := 578, numerator := 2987897942109418962448023552 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 598, numerator := 4745184957714871339368579072 }, some { target := 599, numerator := 5404238424064159025391992832 }, some { target := 600, numerator := 4217942184635441190549848064 }, some { target := 601, numerator := 56546787412768883460808900608 }, some { target := 602, numerator := 5008806344254586413777944576 }, some { target := 603, numerator := 4217942184635441190549848064 }, some { target := 604, numerator := 5008806344254586413777944576 }, some { target := 605, numerator := 4876995650984728876573261824 }, some { target := 606, numerator := 184271349191260837012146487296 }, some { target := 607, numerator := 4876995650984728876573261824 }, some { target := 608, numerator := 56546787412768883460808900608 }, some { target := 609, numerator := 184271349191260837012146487296 }, some { target := 610, numerator := 4745184957714871339368579072 }, some { target := 611, numerator := 4876995650984728876573261824 }, some { target := 612, numerator := 4876995650984728876573261824 }, some { target := 613, numerator := 5404238424064159025391992832 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 659, numerator := 142804362441978071262167040 }, some { target := 660, numerator := 162638301670030581159690240 }, some { target := 661, numerator := 126937211059536063344148480 }, some { target := 662, numerator := 1701751985766905349207490560 }, some { target := 663, numerator := 150737938133199075221176320 }, some { target := 664, numerator := 126937211059536063344148480 }, some { target := 665, numerator := 150737938133199075221176320 }, some { target := 666, numerator := 146771150287588573241671680 }, some { target := 667, numerator := 5545569408163481767347486720 }, some { target := 668, numerator := 146771150287588573241671680 }, some { target := 669, numerator := 1701751985766905349207490560 }, some { target := 670, numerator := 5545569408163481767347486720 }, some { target := 671, numerator := 142804362441978071262167040 }, some { target := 672, numerator := 146771150287588573241671680 }, some { target := 673, numerator := 146771150287588573241671680 }, some { target := 674, numerator := 162638301670030581159690240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 694, numerator := 2623520144291197137759240192 }, some { target := 695, numerator := 2987897942109418962448023552 }, some { target := 696, numerator := 2332017906036619678008213504 }, some { target := 697, numerator := 31263615052803432558297612288 }, some { target := 698, numerator := 2769271263418485867634753536 }, some { target := 699, numerator := 2332017906036619678008213504 }, some { target := 700, numerator := 2769271263418485867634753536 }, some { target := 701, numerator := 2696395703854841502696996864 }, some { target := 702, numerator := 101880032269974822182983827456 }, some { target := 703, numerator := 2696395703854841502696996864 }, some { target := 704, numerator := 31263615052803432558297612288 }, some { target := 705, numerator := 101880032269974822182983827456 }, some { target := 706, numerator := 2623520144291197137759240192 }, some { target := 707, numerator := 2696395703854841502696996864 }, some { target := 708, numerator := 2696395703854841502696996864 }, some { target := 709, numerator := 2987897942109418962448023552 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 720, numerator := 155044736365576191656067072 }, some { target := 721, numerator := 176578727527461773830520832 }, some { target := 722, numerator := 137817543436067725916504064 }, some { target := 723, numerator := 1847616441689782950568132608 }, some { target := 724, numerator := 163658332830330424525848576 }, some { target := 725, numerator := 137817543436067725916504064 }, some { target := 726, numerator := 163658332830330424525848576 }, some { target := 727, numerator := 159351534597953308090957824 }, some { target := 728, numerator := 6020903928863208775977271296 }, some { target := 729, numerator := 159351534597953308090957824 }, some { target := 730, numerator := 1847616441689782950568132608 }, some { target := 731, numerator := 6020903928863208775977271296 }, some { target := 732, numerator := 155044736365576191656067072 }, some { target := 733, numerator := 159351534597953308090957824 }, some { target := 734, numerator := 159351534597953308090957824 }, some { target := 735, numerator := 176578727527461773830520832 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 830, numerator := 155044736365576191656067072 }, some { target := 831, numerator := 176578727527461773830520832 }, some { target := 832, numerator := 137817543436067725916504064 }, some { target := 833, numerator := 1847616441689782950568132608 }, some { target := 834, numerator := 163658332830330424525848576 }, some { target := 835, numerator := 137817543436067725916504064 }, some { target := 836, numerator := 163658332830330424525848576 }, some { target := 837, numerator := 159351534597953308090957824 }, some { target := 838, numerator := 6020903928863208775977271296 }, some { target := 839, numerator := 159351534597953308090957824 }, some { target := 840, numerator := 1847616441689782950568132608 }, some { target := 841, numerator := 6020903928863208775977271296 }, some { target := 842, numerator := 155044736365576191656067072 }, some { target := 843, numerator := 159351534597953308090957824 }, some { target := 844, numerator := 159351534597953308090957824 }, some { target := 845, numerator := 176578727527461773830520832 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 865, numerator := 150964611724376818191433728 }, some { target := 866, numerator := 171931918908318042940243968 }, some { target := 867, numerator := 134190765977223838392385536 }, some { target := 868, numerator := 1798994956382157083447918592 }, some { target := 869, numerator := 159351534597953308090957824 }, some { target := 870, numerator := 134190765977223838392385536 }, some { target := 871, numerator := 159351534597953308090957824 }, some { target := 872, numerator := 155158073161165063141195776 }, some { target := 873, numerator := 5862459088629966439767343104 }, some { target := 874, numerator := 155158073161165063141195776 }, some { target := 875, numerator := 1798994956382157083447918592 }, some { target := 876, numerator := 5862459088629966439767343104 }, some { target := 877, numerator := 150964611724376818191433728 }, some { target := 878, numerator := 155158073161165063141195776 }, some { target := 879, numerator := 155158073161165063141195776 }, some { target := 880, numerator := 171931918908318042940243968 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 926, numerator := 150964611724376818191433728 }, some { target := 927, numerator := 171931918908318042940243968 }, some { target := 928, numerator := 134190765977223838392385536 }, some { target := 929, numerator := 1798994956382157083447918592 }, some { target := 930, numerator := 159351534597953308090957824 }, some { target := 931, numerator := 134190765977223838392385536 }, some { target := 932, numerator := 159351534597953308090957824 }, some { target := 933, numerator := 155158073161165063141195776 }, some { target := 934, numerator := 5862459088629966439767343104 }, some { target := 935, numerator := 155158073161165063141195776 }, some { target := 936, numerator := 1798994956382157083447918592 }, some { target := 937, numerator := 5862459088629966439767343104 }, some { target := 938, numerator := 150964611724376818191433728 }, some { target := 939, numerator := 155158073161165063141195776 }, some { target := 940, numerator := 155158073161165063141195776 }, some { target := 941, numerator := 171931918908318042940243968 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 961, numerator := 4745184957714871339368579072 }, some { target := 962, numerator := 5404238424064159025391992832 }, some { target := 963, numerator := 4217942184635441190549848064 }, some { target := 964, numerator := 56546787412768883460808900608 }, some { target := 965, numerator := 5008806344254586413777944576 }, some { target := 966, numerator := 4217942184635441190549848064 }, some { target := 967, numerator := 5008806344254586413777944576 }, some { target := 968, numerator := 4876995650984728876573261824 }, some { target := 969, numerator := 184271349191260837012146487296 }, some { target := 970, numerator := 4876995650984728876573261824 }, some { target := 971, numerator := 56546787412768883460808900608 }, some { target := 972, numerator := 184271349191260837012146487296 }, some { target := 973, numerator := 4745184957714871339368579072 }, some { target := 974, numerator := 4876995650984728876573261824 }, some { target := 975, numerator := 4876995650984728876573261824 }, some { target := 976, numerator := 5404238424064159025391992832 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 987, numerator := 150964611724376818191433728 }, some { target := 988, numerator := 171931918908318042940243968 }, some { target := 989, numerator := 134190765977223838392385536 }, some { target := 990, numerator := 1798994956382157083447918592 }, some { target := 991, numerator := 159351534597953308090957824 }, some { target := 992, numerator := 134190765977223838392385536 }, some { target := 993, numerator := 159351534597953308090957824 }, some { target := 994, numerator := 155158073161165063141195776 }, some { target := 995, numerator := 5862459088629966439767343104 }, some { target := 996, numerator := 155158073161165063141195776 }, some { target := 997, numerator := 1798994956382157083447918592 }, some { target := 998, numerator := 5862459088629966439767343104 }, some { target := 999, numerator := 150964611724376818191433728 }, some { target := 1000, numerator := 155158073161165063141195776 }, some { target := 1001, numerator := 155158073161165063141195776 }, some { target := 1002, numerator := 171931918908318042940243968 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1036, numerator := 191765858136370552837767168 }, some { target := 1037, numerator := 218400005099755351843012608 }, some { target := 1038, numerator := 170458540565662713633570816 }, some { target := 1039, numerator := 2285209809458415754650058752 }, some { target := 1040, numerator := 202419516921724472439865344 }, some { target := 1041, numerator := 170458540565662713633570816 }, some { target := 1042, numerator := 202419516921724472439865344 }, some { target := 1043, numerator := 197092687529047512638816256 }, some { target := 1044, numerator := 7446907490962389801866625024 }, some { target := 1045, numerator := 197092687529047512638816256 }, some { target := 1046, numerator := 2285209809458415754650058752 }, some { target := 1047, numerator := 7446907490962389801866625024 }, some { target := 1048, numerator := 191765858136370552837767168 }, some { target := 1049, numerator := 197092687529047512638816256 }, some { target := 1050, numerator := 197092687529047512638816256 }, some { target := 1051, numerator := 218400005099755351843012608 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1062, numerator := 195845982777569926302400512 }, some { target := 1063, numerator := 223046813718899082733289472 }, some { target := 1064, numerator := 174085318024506601157689344 }, some { target := 1065, numerator := 2333831294766041621770272768 }, some { target := 1066, numerator := 206726315154101588874756096 }, some { target := 1067, numerator := 174085318024506601157689344 }, some { target := 1068, numerator := 206726315154101588874756096 }, some { target := 1069, numerator := 201286148965835757588578304 }, some { target := 1070, numerator := 7605352331195632138076553216 }, some { target := 1071, numerator := 201286148965835757588578304 }, some { target := 1072, numerator := 2333831294766041621770272768 }, some { target := 1073, numerator := 7605352331195632138076553216 }, some { target := 1074, numerator := 195845982777569926302400512 }, some { target := 1075, numerator := 201286148965835757588578304 }, some { target := 1076, numerator := 201286148965835757588578304 }, some { target := 1077, numerator := 223046813718899082733289472 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected ++ Left4.expected ++ Left5.expected ++ Left6.expected ++ Left7.expected ++ Left8.expected ++ Left9.expected ++ Left10.expected ++ Left11.expected ++ Left12.expected ++ Left13.expected ++ Left14.expected ++ Left15.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq, Left4.routed_eq, Left5.routed_eq, Left6.routed_eq, Left7.routed_eq, Left8.routed_eq, Left9.routed_eq, Left10.routed_eq, Left11.routed_eq, Left12.routed_eq, Left13.routed_eq, Left14.routed_eq, Left15.routed_eq]
  rfl

end Slot0

namespace Slot1

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨1, 7, #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[49796387700736, 0, 0, 181882218086400, 0, 49796370923520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 347, numerator := 742570030231851405810860032 }, some { target := 350, numerator := 2712250635422256182643916800 }, some { target := 352, numerator := 742569780047884906125066240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 614, numerator := 18204942676651840916653342720 }, some { target := 617, numerator := 66493886545835958026108928000 }, some { target := 619, numerator := 18204936543109436408227430400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 710, numerator := 13462076031945177098893656064 }, some { target := 713, numerator := 49170479261526063698254233600 }, some { target := 715, numerator := 13462071496351977975557652480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 736, numerator := 15019077708237768756239007744 }, some { target := 739, numerator := 54857456400314665371539865600 }, some { target := 741, numerator := 15019072648065285036787630080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 881, numerator := 742570030231851405810860032 }, some { target := 884, numerator := 2712250635422256182643916800 }, some { target := 886, numerator := 742569780047884906125066240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 977, numerator := 14995123836294805807664463872 }, some { target := 980, numerator := 54769964444333302268873932800 }, some { target := 982, numerator := 14995118784192772620461015040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1003, numerator := 15258616427667398241984446464 }, some { target := 1006, numerator := 55732375960128296398199193600 }, some { target := 1008, numerator := 15258611286790409200053780480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1052, numerator := 742570030231851405810860032 }, some { target := 1055, numerator := 2712250635422256182643916800 }, some { target := 1057, numerator := 742569780047884906125066240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1078, numerator := 18204942676651840916653342720 }, some { target := 1081, numerator := 66493886545835958026108928000 }, some { target := 1083, numerator := 18204936543109436408227430400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1092, numerator := 742570030231851405810860032 }, some { target := 1095, numerator := 2712250635422256182643916800 }, some { target := 1097, numerator := 742569780047884906125066240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected ++ Left4.expected ++ Left5.expected ++ Left6.expected ++ Left7.expected ++ Left8.expected ++ Left9.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq, Left4.routed_eq, Left5.routed_eq, Left6.routed_eq, Left7.routed_eq, Left8.routed_eq, Left9.routed_eq]
  rfl

end Slot1

namespace Slot2

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨2, 1, #[70643622084608, 70437463654400, 69956427317248, 70437463654400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[140737471578112, 0, 140737505132544, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        1 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 746, numerator := 9942204755307403596944900096 }, some { target := 748, numerator := 9942207125714017068622282752 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1013, numerator := 9913190539095417010572492800 }, some { target := 1015, numerator := 9913192902584501454608793600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1088, numerator := 9845490701267448309036875776 }, some { target := 1090, numerator := 9845493048615631688577318912 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1102, numerator := 9913190539095417010572492800 }, some { target := 1104, numerator := 9913192902584501454608793600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq]
  rfl

end Slot2

namespace Slot3

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨3, 0, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13.Parent3
