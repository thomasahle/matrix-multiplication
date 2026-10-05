import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk16Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 66; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent0

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
    Slot0.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 257, numerator := 18643902874369359303671808 }, { target := 258, numerator := 372878057487387186073436160 }, { target := 259, numerator := 19309756548453979278802944 }, { target := 260, numerator := 346909764198087007043321856 }, { target := 261, numerator := 519365865786003580602286080 }, { target := 262, numerator := 18643902874369359303671808 }, { target := 263, numerator := 520031719460088200577417216 }, { target := 264, numerator := 520031719460088200577417216 }, { target := 265, numerator := 372212203813302566098305024 }, { target := 266, numerator := 19309756548453979278802944 }, { target := 353, numerator := 13883757459636756928266240 }, { target := 354, numerator := 277675149192735138565324800 }, { target := 355, numerator := 14379605940338069675704320 }, { target := 356, numerator := 258337058445383941415239680 }, { target := 357, numerator := 386761814947023943001702400 }, { target := 358, numerator := 13883757459636756928266240 }, { target := 359, numerator := 387257663427725255749140480 }, { target := 360, numerator := 387257663427725255749140480 }, { target := 361, numerator := 277179300712033825817886720 }, { target := 362, numerator := 14379605940338069675704320 }, { target := 379, numerator := 14677115028758857324167168 }, { target := 380, numerator := 293542300575177146483343360 }, { target := 381, numerator := 15201297708357387942887424 }, { target := 382, numerator := 273099176070834452353253376 }, { target := 383, numerator := 408862490086853882601799680 }, { target := 384, numerator := 14677115028758857324167168 }, { target := 385, numerator := 409386672766452413220519936 }, { target := 386, numerator := 409386672766452413220519936 }, { target := 387, numerator := 293018117895578615864623104 }, { target := 388, numerator := 15201297708357387942887424 }, { target := 524, numerator := 19040581658930409501622272 }, { target := 525, numerator := 380811633178608190032445440 }, { target := 526, numerator := 19720602432463638412394496 }, { target := 527, numerator := 354290823010812262512328704 }, { target := 528, numerator := 530416203355918550402334720 }, { target := 529, numerator := 19040581658930409501622272 }, { target := 530, numerator := 531096224129451779313106944 }, { target := 531, numerator := 531096224129451779313106944 }, { target := 532, numerator := 380131612405074961121673216 }, { target := 533, numerator := 19720602432463638412394496 }, { target := 620, numerator := 255064458472755277282148352 }, { target := 621, numerator := 5101289169455105545642967040 }, { target := 622, numerator := 264173903418210822899367936 }, { target := 623, numerator := 4746020816582339266571403264 }, { target := 624, numerator := 7105367057455325581431275520 }, { target := 625, numerator := 255064458472755277282148352 }, { target := 626, numerator := 7114476502400781127048495104 }, { target := 627, numerator := 7114476502400781127048495104 }, { target := 628, numerator := 5092179724509650000025747456 }, { target := 629, numerator := 264173903418210822899367936 }, { target := 646, numerator := 461337426444501380216389632 }, { target := 647, numerator := 9226748528890027604327792640 }, { target := 648, numerator := 477813763103233572366974976 }, { target := 649, numerator := 8584171399199472110454964224 }, { target := 650, numerator := 12851542593811109877456568320 }, { target := 651, numerator := 461337426444501380216389632 }, { target := 652, numerator := 12868018930469842069607153664 }, { target := 653, numerator := 12868018930469842069607153664 }, { target := 654, numerator := 9210272192231295412177207296 }, { target := 655, numerator := 477813763103233572366974976 }]

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
    Slot0.Left6.expected,
    Slot0.Left7.expected,
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot0.Left10.expected,
    Slot0.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 695, numerator := 13883757459636756928266240 }, { target := 696, numerator := 277675149192735138565324800 }, { target := 697, numerator := 14379605940338069675704320 }, { target := 698, numerator := 258337058445383941415239680 }, { target := 699, numerator := 386761814947023943001702400 }, { target := 700, numerator := 13883757459636756928266240 }, { target := 701, numerator := 387257663427725255749140480 }, { target := 702, numerator := 387257663427725255749140480 }, { target := 703, numerator := 277179300712033825817886720 }, { target := 704, numerator := 14379605940338069675704320 }, { target := 721, numerator := 255064458472755277282148352 }, { target := 722, numerator := 5101289169455105545642967040 }, { target := 723, numerator := 264173903418210822899367936 }, { target := 724, numerator := 4746020816582339266571403264 }, { target := 725, numerator := 7105367057455325581431275520 }, { target := 726, numerator := 255064458472755277282148352 }, { target := 727, numerator := 7114476502400781127048495104 }, { target := 728, numerator := 7114476502400781127048495104 }, { target := 729, numerator := 5092179724509650000025747456 }, { target := 730, numerator := 264173903418210822899367936 }, { target := 735, numerator := 15073793813319907522117632 }, { target := 736, numerator := 301475876266398150442352640 }, { target := 737, numerator := 15612143592367047076478976 }, { target := 738, numerator := 280480234883559707822260224 }, { target := 739, numerator := 419912827656768852401848320 }, { target := 740, numerator := 15073793813319907522117632 }, { target := 741, numerator := 420451177435815991956209664 }, { target := 742, numerator := 420451177435815991956209664 }, { target := 743, numerator := 300937526487351010887991296 }, { target := 744, numerator := 15612143592367047076478976 }, { target := 836, numerator := 15073793813319907522117632 }, { target := 837, numerator := 301475876266398150442352640 }, { target := 838, numerator := 15612143592367047076478976 }, { target := 839, numerator := 280480234883559707822260224 }, { target := 840, numerator := 419912827656768852401848320 }, { target := 841, numerator := 15073793813319907522117632 }, { target := 842, numerator := 420451177435815991956209664 }, { target := 843, numerator := 420451177435815991956209664 }, { target := 844, numerator := 300937526487351010887991296 }, { target := 845, numerator := 15612143592367047076478976 }, { target := 862, numerator := 14677115028758857324167168 }, { target := 863, numerator := 293542300575177146483343360 }, { target := 864, numerator := 15201297708357387942887424 }, { target := 865, numerator := 273099176070834452353253376 }, { target := 866, numerator := 408862490086853882601799680 }, { target := 867, numerator := 14677115028758857324167168 }, { target := 868, numerator := 409386672766452413220519936 }, { target := 869, numerator := 409386672766452413220519936 }, { target := 870, numerator := 293018117895578615864623104 }, { target := 871, numerator := 15201297708357387942887424 }, { target := 911, numerator := 14677115028758857324167168 }, { target := 912, numerator := 293542300575177146483343360 }, { target := 913, numerator := 15201297708357387942887424 }, { target := 914, numerator := 273099176070834452353253376 }, { target := 915, numerator := 408862490086853882601799680 }, { target := 916, numerator := 14677115028758857324167168 }, { target := 917, numerator := 409386672766452413220519936 }, { target := 918, numerator := 409386672766452413220519936 }, { target := 919, numerator := 293018117895578615864623104 }, { target := 920, numerator := 15201297708357387942887424 }]

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
    Slot1.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 389, numerator := 299813603264428035327131648 }, { target := 391, numerator := 299813603264428035327131648 }, { target := 656, numerator := 7350268983256945382213550080 }, { target := 658, numerator := 7350268983256945382213550080 }, { target := 731, numerator := 5435330484987372769478967296 }, { target := 733, numerator := 5435330484987372769478967296 }, { target := 745, numerator := 6063971911186979940326178816 }, { target := 747, numerator := 6063971911186979940326178816 }, { target := 872, numerator := 299813603264428035327131648 }, { target := 874, numerator := 299813603264428035327131648 }, { target := 937, numerator := 461337426444501380216389632 }, { target := 938, numerator := 9226748528890027604327792640 }, { target := 939, numerator := 477813763103233572366974976 }, { target := 940, numerator := 8584171399199472110454964224 }, { target := 941, numerator := 12851542593811109877456568320 }, { target := 942, numerator := 461337426444501380216389632 }, { target := 943, numerator := 12868018930469842069607153664 }, { target := 944, numerator := 12868018930469842069607153664 }, { target := 945, numerator := 9210272192231295412177207296 }, { target := 946, numerator := 477813763103233572366974976 }, { target := 947, numerator := 6054300504630062906928529408 }, { target := 949, numerator := 6054300504630062906928529408 }, { target := 951, numerator := 14677115028758857324167168 }, { target := 952, numerator := 293542300575177146483343360 }, { target := 953, numerator := 15201297708357387942887424 }, { target := 954, numerator := 273099176070834452353253376 }, { target := 955, numerator := 408862490086853882601799680 }, { target := 956, numerator := 14677115028758857324167168 }, { target := 957, numerator := 409386672766452413220519936 }, { target := 958, numerator := 409386672766452413220519936 }, { target := 959, numerator := 293018117895578615864623104 }, { target := 960, numerator := 15201297708357387942887424 }, { target := 961, numerator := 6160685976756150274302672896 }, { target := 963, numerator := 6160685976756150274302672896 }, { target := 982, numerator := 18643902874369359303671808 }, { target := 983, numerator := 372878057487387186073436160 }, { target := 984, numerator := 19309756548453979278802944 }, { target := 985, numerator := 346909764198087007043321856 }, { target := 986, numerator := 519365865786003580602286080 }, { target := 987, numerator := 18643902874369359303671808 }, { target := 988, numerator := 520031719460088200577417216 }, { target := 989, numerator := 520031719460088200577417216 }, { target := 990, numerator := 372212203813302566098305024 }, { target := 991, numerator := 19309756548453979278802944 }, { target := 992, numerator := 299813603264428035327131648 }, { target := 994, numerator := 299813603264428035327131648 }, { target := 996, numerator := 19040581658930409501622272 }, { target := 997, numerator := 380811633178608190032445440 }, { target := 998, numerator := 19720602432463638412394496 }, { target := 999, numerator := 354290823010812262512328704 }, { target := 1000, numerator := 530416203355918550402334720 }, { target := 1001, numerator := 19040581658930409501622272 }, { target := 1002, numerator := 531096224129451779313106944 }, { target := 1003, numerator := 531096224129451779313106944 }, { target := 1004, numerator := 380131612405074961121673216 }, { target := 1005, numerator := 19720602432463638412394496 }, { target := 1006, numerator := 7350268983256945382213550080 }, { target := 1008, numerator := 7350268983256945382213550080 }, { target := 1011, numerator := 299813603264428035327131648 }, { target := 1013, numerator := 299813603264428035327131648 }]

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
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left3.expected,
    Slot3.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 127393574284547600796352512 }, { target := 111, numerator := 145087126268512545351401472 }, { target := 112, numerator := 113238732697375645152313344 }, { target := 113, numerator := 1518106760224192242823200768 }, { target := 114, numerator := 134470995078133578618372096 }, { target := 115, numerator := 113238732697375645152313344 }, { target := 116, numerator := 134470995078133578618372096 }, { target := 117, numerator := 130932284681340589707362304 }, { target := 118, numerator := 4947117134716598497591689216 }, { target := 119, numerator := 130932284681340589707362304 }, { target := 120, numerator := 1518106760224192242823200768 }, { target := 121, numerator := 4947117134716598497591689216 }, { target := 122, numerator := 127393574284547600796352512 }, { target := 123, numerator := 130932284681340589707362304 }, { target := 124, numerator := 130932284681340589707362304 }, { target := 125, numerator := 145087126268512545351401472 }, { target := 206, numerator := 20877353296672746754214461440 }, { target := 207, numerator := 23776985698988406025633136640 }, { target := 208, numerator := 18557647374820219337079521280 }, { target := 209, numerator := 248788460118683565487722332160 }, { target := 210, numerator := 22037206257599010462781931520 }, { target := 211, numerator := 18557647374820219337079521280 }, { target := 212, numerator := 22037206257599010462781931520 }, { target := 213, numerator := 21457279777135878608498196480 }, { target := 214, numerator := 810737219687458332288661585920 }, { target := 215, numerator := 21457279777135878608498196480 }, { target := 216, numerator := 248788460118683565487722332160 }, { target := 217, numerator := 810737219687458332288661585920 }, { target := 218, numerator := 20877353296672746754214461440 }, { target := 219, numerator := 21457279777135878608498196480 }, { target := 220, numerator := 21457279777135878608498196480 }, { target := 221, numerator := 23776985698988406025633136640 }, { target := 302, numerator := 214940435662257154598727843840 }, { target := 303, numerator := 244793273948681759404106711040 }, { target := 304, numerator := 191058165033117470754424750080 }, { target := 305, numerator := 2561373524975231092301506805760 }, { target := 306, numerator := 226881570976826996520879390720 }, { target := 307, numerator := 191058165033117470754424750080 }, { target := 308, numerator := 226881570976826996520879390720 }, { target := 309, numerator := 220911003319542075559803617280 }, { target := 310, numerator := 8346853584884319503583931269120 }, { target := 311, numerator := 220911003319542075559803617280 }, { target := 312, numerator := 2561373524975231092301506805760 }, { target := 313, numerator := 8346853584884319503583931269120 }, { target := 314, numerator := 214940435662257154598727843840 }, { target := 315, numerator := 220911003319542075559803617280 }, { target := 316, numerator := 220911003319542075559803617280 }, { target := 317, numerator := 244793273948681759404106711040 }, { target := 679, numerator := 20877353296672746754214461440 }, { target := 680, numerator := 23776985698988406025633136640 }, { target := 681, numerator := 18557647374820219337079521280 }, { target := 682, numerator := 248788460118683565487722332160 }, { target := 683, numerator := 22037206257599010462781931520 }, { target := 684, numerator := 18557647374820219337079521280 }, { target := 685, numerator := 22037206257599010462781931520 }, { target := 686, numerator := 21457279777135878608498196480 }, { target := 687, numerator := 810737219687458332288661585920 }, { target := 688, numerator := 21457279777135878608498196480 }, { target := 689, numerator := 248788460118683565487722332160 }, { target := 690, numerator := 810737219687458332288661585920 }, { target := 691, numerator := 20877353296672746754214461440 }, { target := 692, numerator := 21457279777135878608498196480 }, { target := 693, numerator := 21457279777135878608498196480 }, { target := 694, numerator := 23776985698988406025633136640 }]

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
    Slot3.Left18.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left6.expected,
    Slot4.Left14.expected,
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot5.Left7.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left2.expected,
    Slot6.Left3.expected,
    Slot7.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 2699292239279411487056068608 }, { target := 57, numerator := 40489383589191172305841029120 }, { target := 58, numerator := 71081362301024502492476473344 }, { target := 59, numerator := 2699292239279411487056068608 }, { target := 60, numerator := 44988203987990191450934476800 }, { target := 61, numerator := 2699292239279411487056068608 }, { target := 62, numerator := 71081362301024502492476473344 }, { target := 63, numerator := 70631480261144600577967128576 }, { target := 64, numerator := 44988203987990191450934476800 }, { target := 65, numerator := 1090064182629002338856142372864 }, { target := 66, numerator := 69731716181384796748948439040 }, { target := 67, numerator := 40489383589191172305841029120 }, { target := 68, numerator := 71081362301024502492476473344 }, { target := 69, numerator := 2699292239279411487056068608 }, { target := 70, numerator := 69731716181384796748948439040 }, { target := 71, numerator := 2699292239279411487056068608 }, { target := 72, numerator := 71081362301024502492476473344 }, { target := 73, numerator := 71081362301024502492476473344 }, { target := 74, numerator := 2699292239279411487056068608 }, { target := 257, numerator := 4183804560690201660806397952 }, { target := 260, numerator := 15281422783345448887045324800 }, { target := 262, numerator := 4183803151098139715976560640 }, { target := 353, numerator := 829794201005507815910513049600 }, { target := 356, numerator := 3030838516663792333530071040000 }, { target := 358, numerator := 829793921434294147111452672000 }, { target := 389, numerator := 6713749849422466463697993728 }, { target := 391, numerator := 6713751450105356822601793536 }, { target := 695, numerator := 829794201005507815910513049600 }, { target := 698, numerator := 3030838516663792333530071040000 }, { target := 700, numerator := 829793921434294147111452672000 }, { target := 731, numerator := 303449279266680203868297494528 }, { target := 733, numerator := 303449351614634820571691483136 }, { target := 749, numerator := 19807040628566084398385987584 }, { target := 965, numerator := 19807040628566084398385987584 }, { target := 966, numerator := 127393574284547600796352512 }, { target := 967, numerator := 145087126268512545351401472 }, { target := 968, numerator := 113238732697375645152313344 }, { target := 969, numerator := 1518106760224192242823200768 }, { target := 970, numerator := 134470995078133578618372096 }, { target := 971, numerator := 113238732697375645152313344 }, { target := 972, numerator := 134470995078133578618372096 }, { target := 973, numerator := 130932284681340589707362304 }, { target := 974, numerator := 4947117134716598497591689216 }, { target := 975, numerator := 130932284681340589707362304 }, { target := 976, numerator := 1518106760224192242823200768 }, { target := 977, numerator := 4947117134716598497591689216 }, { target := 978, numerator := 127393574284547600796352512 }, { target := 979, numerator := 130932284681340589707362304 }, { target := 980, numerator := 130932284681340589707362304 }, { target := 981, numerator := 145087126268512545351401472 }, { target := 982, numerator := 4183804560690201660806397952 }, { target := 985, numerator := 15281422783345448887045324800 }, { target := 987, numerator := 4183803151098139715976560640 }, { target := 992, numerator := 6749583162022817085018603520 }, { target := 994, numerator := 6749584771249035937044234240 }, { target := 1010, numerator := 19807040628566084398385987584 }, { target := 1015, numerator := 19807040628566084398385987584 }]

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
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 981187604900638550812262400 }, { target := 112, numerator := 38271599516656447263237734400 }, { target := 115, numerator := 38271585478767523763375308800 }, { target := 122, numerator := 981192284196946384099737600 }, { target := 152, numerator := 105639765266225112815713124352 }, { target := 153, numerator := 1584596478993376692235696865280 }, { target := 154, numerator := 2781847152010594637480445607936 }, { target := 155, numerator := 105639765266225112815713124352 }, { target := 156, numerator := 1760662754437085213595218739200 }, { target := 157, numerator := 105639765266225112815713124352 }, { target := 158, numerator := 2781847152010594637480445607936 }, { target := 159, numerator := 2764240524466223785344493420544 }, { target := 160, numerator := 1760662754437085213595218739200 }, { target := 161, numerator := 42660858540010574725412150050816 }, { target := 162, numerator := 2729027269377482081072589045760 }, { target := 163, numerator := 1584596478993376692235696865280 }, { target := 164, numerator := 2781847152010594637480445607936 }, { target := 165, numerator := 105639765266225112815713124352 }, { target := 166, numerator := 2729027269377482081072589045760 }, { target := 167, numerator := 105639765266225112815713124352 }, { target := 168, numerator := 2781847152010594637480445607936 }, { target := 169, numerator := 2781847152010594637480445607936 }, { target := 170, numerator := 105639765266225112815713124352 }, { target := 283, numerator := 105639804011305196633412599808 }, { target := 284, numerator := 1584597060169577949501188997120 }, { target := 285, numerator := 2781848172297703511346531794944 }, { target := 286, numerator := 105639804011305196633412599808 }, { target := 287, numerator := 1760663400188419943890209996800 }, { target := 288, numerator := 105639804011305196633412599808 }, { target := 289, numerator := 2781848172297703511346531794944 }, { target := 290, numerator := 2764241538295819311907629694976 }, { target := 291, numerator := 1760663400188419943890209996800 }, { target := 292, numerator := 42660874186565415240459788222464 }, { target := 293, numerator := 2729028270292050913029825495040 }, { target := 294, numerator := 1584597060169577949501188997120 }, { target := 295, numerator := 2781848172297703511346531794944 }, { target := 296, numerator := 105639804011305196633412599808 }, { target := 297, numerator := 2729028270292050913029825495040 }, { target := 298, numerator := 105639804011305196633412599808 }, { target := 299, numerator := 2781848172297703511346531794944 }, { target := 300, numerator := 2781848172297703511346531794944 }, { target := 301, numerator := 105639804011305196633412599808 }, { target := 660, numerator := 2699330984359495304755544064 }, { target := 661, numerator := 40489964765392429571333160960 }, { target := 662, numerator := 71082382588133376358562660352 }, { target := 663, numerator := 2699330984359495304755544064 }, { target := 664, numerator := 44988849739324921745925734400 }, { target := 665, numerator := 2699330984359495304755544064 }, { target := 666, numerator := 71082382588133376358562660352 }, { target := 667, numerator := 70632494090740127141103403008 }, { target := 668, numerator := 44988849739324921745925734400 }, { target := 669, numerator := 1090079829183842853903780544512 }, { target := 670, numerator := 69732717095953628706184888320 }, { target := 671, numerator := 40489964765392429571333160960 }, { target := 672, numerator := 71082382588133376358562660352 }, { target := 673, numerator := 2699330984359495304755544064 }, { target := 674, numerator := 69732717095953628706184888320 }, { target := 675, numerator := 2699330984359495304755544064 }, { target := 676, numerator := 71082382588133376358562660352 }, { target := 677, numerator := 71082382588133376358562660352 }, { target := 678, numerator := 2699330984359495304755544064 }]

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
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left6.expected,
    Slot9.Left14.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left2.expected,
    Slot10.Left3.expected,
    Slot10.Left4.expected,
    Slot10.Left5.expected,
    Slot10.Left6.expected,
    Slot10.Left7.expected,
    Slot10.Left8.expected,
    Slot10.Left9.expected,
    Slot11.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 77336858427223859427369025536 }, { target := 15, numerator := 58002643820417894570526769152 }, { target := 16, numerator := 61225012921552222046667145216 }, { target := 17, numerator := 78948042977791023165439213568 }, { target := 18, numerator := 1056937065172059412174043348992 }, { target := 19, numerator := 1848028679500536807566505672704 }, { target := 20, numerator := 56391459269850730832456581120 }, { target := 21, numerator := 1056937065172059412174043348992 }, { target := 22, numerator := 59613828370985058308596957184 }, { target := 23, numerator := 61225012921552222046667145216 }, { target := 24, numerator := 61225012921552222046667145216 }, { target := 25, numerator := 59613828370985058308596957184 }, { target := 26, numerator := 1848028679500536807566505672704 }, { target := 27, numerator := 59613828370985058308596957184 }, { target := 28, numerator := 77336858427223859427369025536 }, { target := 29, numerator := 78948042977791023165439213568 }, { target := 206, numerator := 316061484943648894739074252800 }, { target := 208, numerator := 12328099655955203257508089036800 }, { target := 211, numerator := 12328095134051342594011142553600 }, { target := 218, numerator := 316062992244935782571389747200 }, { target := 257, numerator := 27927390179136214141916676096 }, { target := 260, numerator := 100453991971777041715521650688 }, { target := 262, numerator := 27927399495865619472269180928 }, { target := 302, numerator := 3361446805191797026223648931840 }, { target := 304, numerator := 131114524156542384207486297047040 }, { target := 307, numerator := 131114476064193237262796933038080 }, { target := 314, numerator := 3361462835974846007786770268160 }, { target := 353, numerator := 4898201858424086845357113212928 }, { target := 356, numerator := 17618686422402230283203178921984 }, { target := 358, numerator := 4898203492490893478663295074304 }, { target := 389, numerator := 7795154614129861631624085504 }, { target := 391, numerator := 7795152755620396205386760192 }, { target := 656, numerator := 188843906942307293075796393984 }, { target := 658, numerator := 188843861918416695169208287232 }, { target := 679, numerator := 316062437552974040990094458880 }, { target := 681, numerator := 12328136812847937875418053345280 }, { target := 684, numerator := 12328132290930448193548776898560 }, { target := 691, numerator := 316063944858803934946519941120 }, { target := 695, numerator := 4898202445664454806671202451456 }, { target := 698, numerator := 17618688534688370531264278560768 }, { target := 700, numerator := 4898204079731457346561174929408 }, { target := 731, numerator := 143078805659351331238519504896 }, { target := 733, numerator := 143078771546709852931131179008 }, { target := 745, numerator := 159423484688978460466118393856 }, { target := 747, numerator := 159423446679462296587587289088 }, { target := 872, numerator := 7795154614129861631624085504 }, { target := 874, numerator := 7795152755620396205386760192 }, { target := 947, numerator := 159423484688978460466118393856 }, { target := 949, numerator := 159423446679462296587587289088 }, { target := 961, numerator := 159172028088522658478001487872 }, { target := 963, numerator := 159171990138958412839026425856 }, { target := 966, numerator := 981187604900638550812262400 }, { target := 968, numerator := 38271599516656447263237734400 }, { target := 971, numerator := 38271585478767523763375308800 }, { target := 978, numerator := 981192284196946384099737600 }, { target := 982, numerator := 27926802938768252827827437568 }, { target := 985, numerator := 100451879685636793654422011904 }, { target := 987, numerator := 27926812255301751574389325824 }, { target := 992, numerator := 7795154614129861631624085504 }, { target := 994, numerator := 7795152755620396205386760192 }, { target := 1006, numerator := 188843906942307293075796393984 }, { target := 1008, numerator := 188843861918416695169208287232 }, { target := 1011, numerator := 7795154614129861631624085504 }, { target := 1013, numerator := 7795152755620396205386760192 }]

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
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 4137445239978601855749980160 }, { target := 57, numerator := 489019464001089553773530972160 }, { target := 59, numerator := 4640697233872565272181483765760 }, { target := 67, numerator := 489019799397104467732825374720 }, { target := 74, numerator := 4137445239978601855749980160 }, { target := 110, numerator := 4140348201031033781275852800 }, { target := 112, numerator := 162032361439438504642153021440 }, { target := 115, numerator := 162032361439438504642153021440 }, { target := 122, numerator := 4140348201031033781275852800 }, { target := 136, numerator := 287287156495865064258388623360 }, { target := 137, numerator := 215465367371898798193791467520 }, { target := 138, numerator := 227435665559226509204557660160 }, { target := 139, numerator := 293272305589528919763771719680 }, { target := 140, numerator := 3926257805443489211531311185920 }, { target := 141, numerator := 6864966010432442264674411479040 }, { target := 142, numerator := 209480218278234942688408371200 }, { target := 143, numerator := 3926257805443489211531311185920 }, { target := 144, numerator := 221450516465562653699174563840 }, { target := 145, numerator := 227435665559226509204557660160 }, { target := 146, numerator := 227435665559226509204557660160 }, { target := 147, numerator := 221450516465562653699174563840 }, { target := 148, numerator := 6864966010432442264674411479040 }, { target := 149, numerator := 221450516465562653699174563840 }, { target := 150, numerator := 287287156495865064258388623360 }, { target := 151, numerator := 293272305589528919763771719680 }, { target := 152, numerator := 161918754174625576680966586368 }, { target := 153, numerator := 19137757187236898291310781267968 }, { target := 155, numerator := 181613500850627085571049807413248 }, { target := 163, numerator := 19137770312946542797275168505856 }, { target := 170, numerator := 161918754174625576680966586368 }, { target := 206, numerator := 489362575359799316659883212800 }, { target := 208, numerator := 19151184836552623180482021949440 }, { target := 211, numerator := 19151184836552623180482021949440 }, { target := 218, numerator := 489362575359799316659883212800 }, { target := 267, numerator := 77320579101791834453229699072 }, { target := 268, numerator := 57990434326343875839922274304 }, { target := 269, numerator := 61212125122251868942140178432 }, { target := 270, numerator := 78931424499745831004338651136 }, { target := 271, numerator := 1056714581057821737527472553984 }, { target := 272, numerator := 1847639671453234044121968017408 }, { target := 273, numerator := 56379588928389879288813322240 }, { target := 274, numerator := 1056714581057821737527472553984 }, { target := 275, numerator := 59601279724297872391031226368 }, { target := 276, numerator := 61212125122251868942140178432 }, { target := 277, numerator := 61212125122251868942140178432 }, { target := 278, numerator := 59601279724297872391031226368 }, { target := 279, numerator := 1847639671453234044121968017408 }, { target := 280, numerator := 59601279724297872391031226368 }, { target := 281, numerator := 77320579101791834453229699072 }, { target := 282, numerator := 78931424499745831004338651136 }, { target := 283, numerator := 161918754174625576680966586368 }, { target := 284, numerator := 19137757187236898291310781267968 }, { target := 286, numerator := 181613500850627085571049807413248 }, { target := 294, numerator := 19137770312946542797275168505856 }, { target := 301, numerator := 161918754174625576680966586368 }, { target := 302, numerator := 4643953292272054881213009100800 }, { target := 304, numerator := 181740926566010791647577469091840 }, { target := 307, numerator := 181740926566010791647577469091840 }, { target := 314, numerator := 4643953292272054881213009100800 }, { target := 660, numerator := 4137445239978601855749980160 }, { target := 661, numerator := 489019464001089553773530972160 }, { target := 663, numerator := 4640697233872565272181483765760 }, { target := 671, numerator := 489019799397104467732825374720 }, { target := 678, numerator := 4137445239978601855749980160 }]

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
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left2.expected,
    Slot14.Left3.expected,
    Slot14.Left4.expected,
    Slot14.Left5.expected,
    Slot14.Left6.expected,
    Slot14.Left7.expected,
    Slot14.Left8.expected,
    Slot14.Left9.expected,
    Slot14.Left10.expected,
    Slot14.Left11.expected,
    Slot14.Left12.expected,
    Slot14.Left13.expected,
    Slot14.Left14.expected,
    Slot14.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 257, numerator := 77824275602185354339726393344 }, { target := 260, numerator := 289097789835124718024723005440 }, { target := 262, numerator := 77807893675962791393060978688 }, { target := 353, numerator := 58368206701639015754794795008 }, { target := 356, numerator := 216823342376343538518542254080 }, { target := 358, numerator := 58355920256972093544795734016 }, { target := 379, numerator := 61610884851730072185616728064 }, { target := 382, numerator := 228869083619473735102905712640 }, { target := 384, numerator := 61597915826803876519506608128 }, { target := 524, numerator := 79445614677230882555137359872 }, { target := 527, numerator := 295120660456689816316904734720 }, { target := 529, numerator := 79428891460878682880416415744 }, { target := 620, numerator := 1063598433229866509309594042368 }, { target := 623, numerator := 3951003127746704479671214407680 }, { target := 625, numerator := 1063374546904824815705166708736 }, { target := 646, numerator := 1859675919077220863076378607616 }, { target := 649, numerator := 6908232602935167741132443484160 }, { target := 651, numerator := 1859284459298527535996686303232 }, { target := 679, numerator := 489362910991138570148354457600 }, { target := 681, numerator := 19151197971471676312656522772480 }, { target := 684, numerator := 19151197971471676312656522772480 }, { target := 691, numerator := 489362910991138570148354457600 }, { target := 695, numerator := 56746867626593487539383828480 }, { target := 698, numerator := 210800471754778440226360524800 }, { target := 700, numerator := 56734922472056202057440296960 }, { target := 721, numerator := 1063598433229866509309594042368 }, { target := 724, numerator := 3951003127746704479671214407680 }, { target := 726, numerator := 1063374546904824815705166708736 }, { target := 735, numerator := 59989545776684543970205761536 }, { target := 738, numerator := 222846212997908636810723983360 }, { target := 740, numerator := 59976918041887985032151171072 }, { target := 836, numerator := 61610884851730072185616728064 }, { target := 839, numerator := 228869083619473735102905712640 }, { target := 841, numerator := 61597915826803876519506608128 }, { target := 862, numerator := 61610884851730072185616728064 }, { target := 865, numerator := 228869083619473735102905712640 }, { target := 867, numerator := 61597915826803876519506608128 }, { target := 911, numerator := 59989545776684543970205761536 }, { target := 914, numerator := 222846212997908636810723983360 }, { target := 916, numerator := 59976918041887985032151171072 }, { target := 937, numerator := 1859675919077220863076378607616 }, { target := 940, numerator := 6908232602935167741132443484160 }, { target := 942, numerator := 1859284459298527535996686303232 }, { target := 951, numerator := 59989545776684543970205761536 }, { target := 954, numerator := 222846212997908636810723983360 }, { target := 956, numerator := 59976918041887985032151171072 }, { target := 966, numerator := 4140348201031033781275852800 }, { target := 968, numerator := 162032361439438504642153021440 }, { target := 971, numerator := 162032361439438504642153021440 }, { target := 978, numerator := 4140348201031033781275852800 }, { target := 982, numerator := 77824275602185354339726393344 }, { target := 985, numerator := 289097789835124718024723005440 }, { target := 987, numerator := 77807893675962791393060978688 }, { target := 996, numerator := 79445614677230882555137359872 }, { target := 999, numerator := 295120660456689816316904734720 }, { target := 1001, numerator := 79428891460878682880416415744 }]

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
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot18.Left0.expected,
    Slot18.Left1.expected,
    Slot18.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 8094968253134856309763473408 }, { target := 5, numerator := 196107134132396035117173178368 }, { target := 6, numerator := 148581836646249459363077947392 }, { target := 7, numerator := 165555157177016093560969101312 }, { target := 8, numerator := 8094968253134856309763473408 }, { target := 9, numerator := 165555157177016093560969101312 }, { target := 10, numerator := 165294029168850453034847698944 }, { target := 11, numerator := 8094968253134856309763473408 }, { target := 12, numerator := 196107134132396035117173178368 }, { target := 13, numerator := 8094968253134856309763473408 }, { target := 14, numerator := 27445883451909727691193974784 }, { target := 15, numerator := 4813750102244361210092335398912 }, { target := 20, numerator := 4813750679359895241038940340224 }, { target := 28, numerator := 27445306336375696744589033472 }, { target := 56, numerator := 984105634952387661744046080 }, { target := 57, numerator := 317001444750172757623056629760 }, { target := 59, numerator := 3371443673013928764591600304128 }, { target := 67, numerator := 317002400192536789067388420096 }, { target := 74, numerator := 984105634952387661744046080 }, { target := 110, numerator := 2674713788252228843628134400 }, { target := 112, numerator := 104677860601240738462275993600 }, { target := 115, numerator := 104677898993526841870280294400 }, { target := 122, numerator := 2674752180538332251632435200 }, { target := 126, numerator := 8094966323144257597901635584 }, { target := 127, numerator := 196107087376817337291100913664 }, { target := 128, numerator := 148581801221583308813097762816 }, { target := 129, numerator := 165555117705595461840956030976 }, { target := 130, numerator := 8094966323144257597901635584 }, { target := 131, numerator := 165555117705595461840956030976 }, { target := 132, numerator := 165293989759687582563604365312 }, { target := 133, numerator := 8094966323144257597901635584 }, { target := 134, numerator := 196107087376817337291100913664 }, { target := 135, numerator := 8094966323144257597901635584 }, { target := 136, numerator := 98722026592953299616978173952 }, { target := 137, numerator := 17314915966843571140389331009536 }, { target := 142, numerator := 17314918042710984832449377206272 }, { target := 150, numerator := 98719950725539607556931977216 }, { target := 152, numerator := 38385418399977358630563348480 }, { target := 153, numerator := 12364763149355813527418893762560 }, { target := 155, numerator := 131504455826896413602898895699968 }, { target := 163, numerator := 12364800416752318359805913726976 }, { target := 170, numerator := 38385418399977358630563348480 }, { target := 206, numerator := 40120706823783432654422016000 }, { target := 208, numerator := 1570167909018611076934139904000 }, { target := 211, numerator := 1570168484902902628054204416000 }, { target := 218, numerator := 40121282708074983774486528000 }, { target := 241, numerator := 70434129757308692882207539200 }, { target := 243, numerator := 2756516995832672779506601164800 }, { target := 246, numerator := 2756518006829540169250714419200 }, { target := 253, numerator := 70435140754176082626320793600 }, { target := 267, numerator := 27445892608005867412402470912 }, { target := 268, numerator := 4813751708137602211789789986816 }, { target := 273, numerator := 4813752285253328771620465016832 }, { target := 281, numerator := 27445315492279307581727440896 }, { target := 283, numerator := 38385404320340066584976424960 }, { target := 284, numerator := 12364758614003911642617867141120 }, { target := 286, numerator := 131504407591521692986998559604736 }, { target := 294, numerator := 12364795881386746924235910807552 }, { target := 301, numerator := 38385404320340066584976424960 }, { target := 660, numerator := 984110328164818343606353920 }, { target := 661, numerator := 317002956534140052556732170240 }, { target := 663, numerator := 3371459751472168969891712335872 }, { target := 671, numerator := 317003911981060600924056059904 }, { target := 678, numerator := 984110328164818343606353920 }]

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
    Slot18.Left3.expected,
    Slot18.Left4.expected,
    Slot18.Left5.expected,
    Slot18.Left6.expected,
    Slot18.Left7.expected,
    Slot18.Left8.expected,
    Slot18.Left9.expected,
    Slot18.Left10.expected,
    Slot18.Left11.expected,
    Slot18.Left12.expected,
    Slot18.Left13.expected,
    Slot18.Left14.expected,
    Slot18.Left15.expected,
    Slot18.Left16.expected,
    Slot18.Left17.expected,
    Slot18.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 302, numerator := 2674713788252228843628134400 }, { target := 304, numerator := 104677860601240738462275993600 }, { target := 307, numerator := 104677898993526841870280294400 }, { target := 314, numerator := 2674752180538332251632435200 }, { target := 337, numerator := 44578563137537147393802240000 }, { target := 339, numerator := 1744631010020678974371266560000 }, { target := 342, numerator := 1744631649892114031171338240000 }, { target := 349, numerator := 44579203008972204193873920000 }, { target := 363, numerator := 2674713788252228843628134400 }, { target := 365, numerator := 104677860601240738462275993600 }, { target := 368, numerator := 104677898993526841870280294400 }, { target := 375, numerator := 2674752180538332251632435200 }, { target := 473, numerator := 70434129757308692882207539200 }, { target := 475, numerator := 2756516995832672779506601164800 }, { target := 478, numerator := 2756518006829540169250714419200 }, { target := 485, numerator := 70435140754176082626320793600 }, { target := 508, numerator := 69988344125933321408269516800 }, { target := 510, numerator := 2739070685732465989762888499200 }, { target := 513, numerator := 2739071690330619028939001036800 }, { target := 520, numerator := 69989348724086360584382054400 }, { target := 569, numerator := 44578563137537147393802240000 }, { target := 571, numerator := 1744631010020678974371266560000 }, { target := 574, numerator := 1744631649892114031171338240000 }, { target := 581, numerator := 44579203008972204193873920000 }, { target := 604, numerator := 1080138584822525081351828275200 }, { target := 606, numerator := 42272409372801051549015788748800 }, { target := 609, numerator := 42272424876885922975281525555200 }, { target := 616, numerator := 1080154088907396507617565081600 }, { target := 630, numerator := 69096772863182578460393472000 }, { target := 632, numerator := 2704178065532052410275463168000 }, { target := 635, numerator := 2704179057332776748315574272000 }, { target := 642, numerator := 69097764663906916500504576000 }, { target := 679, numerator := 40120706823783432654422016000 }, { target := 681, numerator := 1570167909018611076934139904000 }, { target := 684, numerator := 1570168484902902628054204416000 }, { target := 691, numerator := 40121282708074983774486528000 }, { target := 705, numerator := 70434129757308692882207539200 }, { target := 707, numerator := 2756516995832672779506601164800 }, { target := 710, numerator := 2756518006829540169250714419200 }, { target := 717, numerator := 70435140754176082626320793600 }, { target := 785, numerator := 2674713788252228843628134400 }, { target := 787, numerator := 104677860601240738462275993600 }, { target := 790, numerator := 104677898993526841870280294400 }, { target := 797, numerator := 2674752180538332251632435200 }, { target := 820, numerator := 69096772863182578460393472000 }, { target := 822, numerator := 2704178065532052410275463168000 }, { target := 825, numerator := 2704179057332776748315574272000 }, { target := 832, numerator := 69097764663906916500504576000 }, { target := 846, numerator := 2674713788252228843628134400 }, { target := 848, numerator := 104677860601240738462275993600 }, { target := 851, numerator := 104677898993526841870280294400 }, { target := 858, numerator := 2674752180538332251632435200 }, { target := 895, numerator := 70434129757308692882207539200 }, { target := 897, numerator := 2756516995832672779506601164800 }, { target := 900, numerator := 2756518006829540169250714419200 }, { target := 907, numerator := 70435140754176082626320793600 }, { target := 921, numerator := 70434129757308692882207539200 }, { target := 923, numerator := 2756516995832672779506601164800 }, { target := 926, numerator := 2756518006829540169250714419200 }, { target := 933, numerator := 70435140754176082626320793600 }, { target := 966, numerator := 2674713788252228843628134400 }, { target := 968, numerator := 104677860601240738462275993600 }, { target := 971, numerator := 104677898993526841870280294400 }, { target := 978, numerator := 2674752180538332251632435200 }]

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
    Slot19.Left0.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot21.Left0.expected,
    Slot21.Left3.expected,
    Slot21.Left5.expected,
    Slot22.Left0.expected,
    Slot22.Left1.expected,
    Slot22.Left2.expected,
    Slot22.Left3.expected,
    Slot22.Left4.expected,
    Slot22.Left5.expected,
    Slot22.Left6.expected,
    Slot22.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 19807040628566084398385987584 }, { target := 1, numerator := 19807040628566084398385987584 }, { target := 2, numerator := 19807040628566084398385987584 }, { target := 3, numerator := 19807040628566084398385987584 }, { target := 4, numerator := 7552968580600274771660242944 }, { target := 6, numerator := 341380439175015229351834681344 }, { target := 11, numerator := 7593281057275669220645928960 }, { target := 14, numerator := 4359594668282226940672212992 }, { target := 15, numerator := 864659503568764446831122841600 }, { target := 20, numerator := 864659503568764446831122841600 }, { target := 28, numerator := 4359594668282226940672212992 }, { target := 56, numerator := 128429294400682134136160256 }, { target := 57, numerator := 21047087876320492662785310720 }, { target := 59, numerator := 216687918879023472928798801920 }, { target := 67, numerator := 21047087876320492662785310720 }, { target := 74, numerator := 128429294400682134136160256 }, { target := 91, numerator := 146266696400776874988404736 }, { target := 92, numerator := 23970294525809449977061048320 }, { target := 94, numerator := 246783463167776733057798635520 }, { target := 102, numerator := 23970294525809449977061048320 }, { target := 109, numerator := 146266696400776874988404736 }, { target := 126, numerator := 7552970381368526425427017728 }, { target := 128, numerator := 341380520566464173143152918528 }, { target := 133, numerator := 7593282867655165429174763520 }, { target := 136, numerator := 15923499370880971949526220800 }, { target := 137, numerator := 3158184672826136549224611840000 }, { target := 142, numerator := 3158184672826136549224611840000 }, { target := 150, numerator := 15923499370880971949526220800 }, { target := 152, numerator := 114159372800606341454364672 }, { target := 153, numerator := 18708522556729326811364720640 }, { target := 155, numerator := 192611483448020864825598935040 }, { target := 163, numerator := 18708522556729326811364720640 }, { target := 170, numerator := 114159372800606341454364672 }, { target := 187, numerator := 1530449091608128765122576384 }, { target := 188, numerator := 250811130526152537564858286080 }, { target := 190, numerator := 2582197699975029719068185722880 }, { target := 198, numerator := 250811130526152537564858286080 }, { target := 205, numerator := 1530449091608128765122576384 }, { target := 222, numerator := 135564255200720030477058048 }, { target := 223, numerator := 22216370536116075588495605760 }, { target := 225, numerator := 228726136594524776980398735360 }, { target := 233, numerator := 22216370536116075588495605760 }, { target := 240, numerator := 135564255200720030477058048 }, { target := 267, numerator := 4359593199463607771269693440 }, { target := 268, numerator := 864659212250861128082522112000 }, { target := 273, numerator := 864659212250861128082522112000 }, { target := 281, numerator := 4359593199463607771269693440 }, { target := 283, numerator := 114159372800606341454364672 }, { target := 284, numerator := 18708522556729326811364720640 }, { target := 286, numerator := 192611483448020864825598935040 }, { target := 294, numerator := 18708522556729326811364720640 }, { target := 301, numerator := 114159372800606341454364672 }, { target := 318, numerator := 135564255200720030477058048 }, { target := 319, numerator := 22216370536116075588495605760 }, { target := 321, numerator := 228726136594524776980398735360 }, { target := 329, numerator := 22216370536116075588495605760 }, { target := 336, numerator := 135564255200720030477058048 }, { target := 419, numerator := 131996774800701082306609152 }, { target := 420, numerator := 21631729206218284125640458240 }, { target := 422, numerator := 222707027736774124954598768640 }, { target := 430, numerator := 21631729206218284125640458240 }, { target := 437, numerator := 131996774800701082306609152 }]

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
    Slot22.Left8.expected,
    Slot22.Left9.expected,
    Slot22.Left10.expected,
    Slot22.Left11.expected,
    Slot22.Left12.expected,
    Slot22.Left13.expected,
    Slot22.Left14.expected,
    Slot22.Left15.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 299813603264428035327131648 }, { target := 5, numerator := 7350268983256945382213550080 }, { target := 6, numerator := 5435330484987372769478967296 }, { target := 7, numerator := 6063971911186979940326178816 }, { target := 8, numerator := 299813603264428035327131648 }, { target := 9, numerator := 6054300504630062906928529408 }, { target := 10, numerator := 6160685976756150274302672896 }, { target := 11, numerator := 299813603264428035327131648 }, { target := 12, numerator := 7350268983256945382213550080 }, { target := 13, numerator := 299813603264428035327131648 }, { target := 126, numerator := 299813603264428035327131648 }, { target := 127, numerator := 7350268983256945382213550080 }, { target := 128, numerator := 5435330484987372769478967296 }, { target := 129, numerator := 6063971911186979940326178816 }, { target := 130, numerator := 299813603264428035327131648 }, { target := 131, numerator := 6054300504630062906928529408 }, { target := 132, numerator := 6160685976756150274302672896 }, { target := 133, numerator := 299813603264428035327131648 }, { target := 134, numerator := 7350268983256945382213550080 }, { target := 135, numerator := 299813603264428035327131648 }, { target := 454, numerator := 4987337599226489542287556608 }, { target := 455, numerator := 817328579197112465071496232960 }, { target := 457, numerator := 8414714183135411532068353474560 }, { target := 465, numerator := 817328579197112465071496232960 }, { target := 472, numerator := 4987337599226489542287556608 }, { target := 489, numerator := 131996774800701082306609152 }, { target := 490, numerator := 21631729206218284125640458240 }, { target := 492, numerator := 222707027736774124954598768640 }, { target := 500, numerator := 21631729206218284125640458240 }, { target := 507, numerator := 131996774800701082306609152 }, { target := 550, numerator := 1530449091608128765122576384 }, { target := 551, numerator := 250811130526152537564858286080 }, { target := 553, numerator := 2582197699975029719068185722880 }, { target := 561, numerator := 250811130526152537564858286080 }, { target := 568, numerator := 1530449091608128765122576384 }, { target := 585, numerator := 4987337599226489542287556608 }, { target := 586, numerator := 817328579197112465071496232960 }, { target := 588, numerator := 8414714183135411532068353474560 }, { target := 596, numerator := 817328579197112465071496232960 }, { target := 603, numerator := 4987337599226489542287556608 }, { target := 660, numerator := 128429294400682134136160256 }, { target := 661, numerator := 21047087876320492662785310720 }, { target := 663, numerator := 216687918879023472928798801920 }, { target := 671, numerator := 21047087876320492662785310720 }, { target := 678, numerator := 128429294400682134136160256 }, { target := 766, numerator := 131996774800701082306609152 }, { target := 767, numerator := 21631729206218284125640458240 }, { target := 769, numerator := 222707027736774124954598768640 }, { target := 777, numerator := 21631729206218284125640458240 }, { target := 784, numerator := 131996774800701082306609152 }, { target := 801, numerator := 131996774800701082306609152 }, { target := 802, numerator := 21631729206218284125640458240 }, { target := 804, numerator := 222707027736774124954598768640 }, { target := 812, numerator := 21631729206218284125640458240 }, { target := 819, numerator := 131996774800701082306609152 }, { target := 876, numerator := 146266696400776874988404736 }, { target := 877, numerator := 23970294525809449977061048320 }, { target := 879, numerator := 246783463167776733057798635520 }, { target := 887, numerator := 23970294525809449977061048320 }, { target := 894, numerator := 146266696400776874988404736 }]

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
    Slot25.Left0.expected,
    Slot25.Left1.expected,
    Slot25.Left2.expected,
    Slot25.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 18643902874369359303671808 }, { target := 15, numerator := 13883757459636756928266240 }, { target := 16, numerator := 14677115028758857324167168 }, { target := 17, numerator := 19040581658930409501622272 }, { target := 18, numerator := 255064458472755277282148352 }, { target := 19, numerator := 461337426444501380216389632 }, { target := 20, numerator := 13883757459636756928266240 }, { target := 21, numerator := 255064458472755277282148352 }, { target := 22, numerator := 15073793813319907522117632 }, { target := 23, numerator := 15073793813319907522117632 }, { target := 24, numerator := 14677115028758857324167168 }, { target := 25, numerator := 14677115028758857324167168 }, { target := 26, numerator := 461337426444501380216389632 }, { target := 27, numerator := 14677115028758857324167168 }, { target := 28, numerator := 18643902874369359303671808 }, { target := 29, numerator := 19040581658930409501622272 }, { target := 40, numerator := 372878057487387186073436160 }, { target := 41, numerator := 277675149192735138565324800 }, { target := 42, numerator := 293542300575177146483343360 }, { target := 43, numerator := 380811633178608190032445440 }, { target := 44, numerator := 5101289169455105545642967040 }, { target := 45, numerator := 9226748528890027604327792640 }, { target := 46, numerator := 277675149192735138565324800 }, { target := 47, numerator := 5101289169455105545642967040 }, { target := 48, numerator := 301475876266398150442352640 }, { target := 49, numerator := 301475876266398150442352640 }, { target := 50, numerator := 293542300575177146483343360 }, { target := 51, numerator := 293542300575177146483343360 }, { target := 52, numerator := 9226748528890027604327792640 }, { target := 53, numerator := 293542300575177146483343360 }, { target := 54, numerator := 372878057487387186073436160 }, { target := 55, numerator := 380811633178608190032445440 }, { target := 75, numerator := 19309756548453979278802944 }, { target := 76, numerator := 14379605940338069675704320 }, { target := 77, numerator := 15201297708357387942887424 }, { target := 78, numerator := 19720602432463638412394496 }, { target := 79, numerator := 264173903418210822899367936 }, { target := 80, numerator := 477813763103233572366974976 }, { target := 81, numerator := 14379605940338069675704320 }, { target := 82, numerator := 264173903418210822899367936 }, { target := 83, numerator := 15612143592367047076478976 }, { target := 84, numerator := 15612143592367047076478976 }, { target := 85, numerator := 15201297708357387942887424 }, { target := 86, numerator := 15201297708357387942887424 }, { target := 87, numerator := 477813763103233572366974976 }, { target := 88, numerator := 15201297708357387942887424 }, { target := 89, numerator := 19309756548453979278802944 }, { target := 90, numerator := 19720602432463638412394496 }, { target := 136, numerator := 346909764198087007043321856 }, { target := 137, numerator := 258337058445383941415239680 }, { target := 138, numerator := 273099176070834452353253376 }, { target := 139, numerator := 354290823010812262512328704 }, { target := 140, numerator := 4746020816582339266571403264 }, { target := 141, numerator := 8584171399199472110454964224 }, { target := 142, numerator := 258337058445383941415239680 }, { target := 143, numerator := 4746020816582339266571403264 }, { target := 144, numerator := 280480234883559707822260224 }, { target := 145, numerator := 280480234883559707822260224 }, { target := 146, numerator := 273099176070834452353253376 }, { target := 147, numerator := 273099176070834452353253376 }, { target := 148, numerator := 8584171399199472110454964224 }, { target := 149, numerator := 273099176070834452353253376 }, { target := 150, numerator := 346909764198087007043321856 }, { target := 151, numerator := 354290823010812262512328704 }]

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
    Slot25.Left4.expected,
    Slot25.Left5.expected,
    Slot25.Left6.expected,
    Slot25.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 171, numerator := 519365865786003580602286080 }, { target := 172, numerator := 386761814947023943001702400 }, { target := 173, numerator := 408862490086853882601799680 }, { target := 174, numerator := 530416203355918550402334720 }, { target := 175, numerator := 7105367057455325581431275520 }, { target := 176, numerator := 12851542593811109877456568320 }, { target := 177, numerator := 386761814947023943001702400 }, { target := 178, numerator := 7105367057455325581431275520 }, { target := 179, numerator := 419912827656768852401848320 }, { target := 180, numerator := 419912827656768852401848320 }, { target := 181, numerator := 408862490086853882601799680 }, { target := 182, numerator := 408862490086853882601799680 }, { target := 183, numerator := 12851542593811109877456568320 }, { target := 184, numerator := 408862490086853882601799680 }, { target := 185, numerator := 519365865786003580602286080 }, { target := 186, numerator := 530416203355918550402334720 }, { target := 267, numerator := 18643902874369359303671808 }, { target := 268, numerator := 13883757459636756928266240 }, { target := 269, numerator := 14677115028758857324167168 }, { target := 270, numerator := 19040581658930409501622272 }, { target := 271, numerator := 255064458472755277282148352 }, { target := 272, numerator := 461337426444501380216389632 }, { target := 273, numerator := 13883757459636756928266240 }, { target := 274, numerator := 255064458472755277282148352 }, { target := 275, numerator := 15073793813319907522117632 }, { target := 276, numerator := 15073793813319907522117632 }, { target := 277, numerator := 14677115028758857324167168 }, { target := 278, numerator := 14677115028758857324167168 }, { target := 279, numerator := 461337426444501380216389632 }, { target := 280, numerator := 14677115028758857324167168 }, { target := 281, numerator := 18643902874369359303671808 }, { target := 282, numerator := 19040581658930409501622272 }, { target := 403, numerator := 520031719460088200577417216 }, { target := 404, numerator := 387257663427725255749140480 }, { target := 405, numerator := 409386672766452413220519936 }, { target := 406, numerator := 531096224129451779313106944 }, { target := 407, numerator := 7114476502400781127048495104 }, { target := 408, numerator := 12868018930469842069607153664 }, { target := 409, numerator := 387257663427725255749140480 }, { target := 410, numerator := 7114476502400781127048495104 }, { target := 411, numerator := 420451177435815991956209664 }, { target := 412, numerator := 420451177435815991956209664 }, { target := 413, numerator := 409386672766452413220519936 }, { target := 414, numerator := 409386672766452413220519936 }, { target := 415, numerator := 12868018930469842069607153664 }, { target := 416, numerator := 409386672766452413220519936 }, { target := 417, numerator := 520031719460088200577417216 }, { target := 418, numerator := 531096224129451779313106944 }, { target := 438, numerator := 520031719460088200577417216 }, { target := 439, numerator := 387257663427725255749140480 }, { target := 440, numerator := 409386672766452413220519936 }, { target := 441, numerator := 531096224129451779313106944 }, { target := 442, numerator := 7114476502400781127048495104 }, { target := 443, numerator := 12868018930469842069607153664 }, { target := 444, numerator := 387257663427725255749140480 }, { target := 445, numerator := 7114476502400781127048495104 }, { target := 446, numerator := 420451177435815991956209664 }, { target := 447, numerator := 420451177435815991956209664 }, { target := 448, numerator := 409386672766452413220519936 }, { target := 449, numerator := 409386672766452413220519936 }, { target := 450, numerator := 12868018930469842069607153664 }, { target := 451, numerator := 409386672766452413220519936 }, { target := 452, numerator := 520031719460088200577417216 }, { target := 453, numerator := 531096224129451779313106944 }]

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
    Slot25.Left8.expected,
    Slot25.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 534, numerator := 372212203813302566098305024 }, { target := 535, numerator := 277179300712033825817886720 }, { target := 536, numerator := 293018117895578615864623104 }, { target := 537, numerator := 380131612405074961121673216 }, { target := 538, numerator := 5092179724509650000025747456 }, { target := 539, numerator := 9210272192231295412177207296 }, { target := 540, numerator := 277179300712033825817886720 }, { target := 541, numerator := 5092179724509650000025747456 }, { target := 542, numerator := 300937526487351010887991296 }, { target := 543, numerator := 300937526487351010887991296 }, { target := 544, numerator := 293018117895578615864623104 }, { target := 545, numerator := 293018117895578615864623104 }, { target := 546, numerator := 9210272192231295412177207296 }, { target := 547, numerator := 293018117895578615864623104 }, { target := 548, numerator := 372212203813302566098305024 }, { target := 549, numerator := 380131612405074961121673216 }, { target := 750, numerator := 19309756548453979278802944 }, { target := 751, numerator := 14379605940338069675704320 }, { target := 752, numerator := 15201297708357387942887424 }, { target := 753, numerator := 19720602432463638412394496 }, { target := 754, numerator := 264173903418210822899367936 }, { target := 755, numerator := 477813763103233572366974976 }, { target := 756, numerator := 14379605940338069675704320 }, { target := 757, numerator := 264173903418210822899367936 }, { target := 758, numerator := 15612143592367047076478976 }, { target := 759, numerator := 15612143592367047076478976 }, { target := 760, numerator := 15201297708357387942887424 }, { target := 761, numerator := 15201297708357387942887424 }, { target := 762, numerator := 477813763103233572366974976 }, { target := 763, numerator := 15201297708357387942887424 }, { target := 764, numerator := 19309756548453979278802944 }, { target := 765, numerator := 19720602432463638412394496 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent0
