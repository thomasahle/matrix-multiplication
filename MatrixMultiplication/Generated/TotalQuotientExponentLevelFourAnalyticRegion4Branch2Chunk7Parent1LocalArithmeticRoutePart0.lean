import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk7Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 64; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk7.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left3.expected,
    Slot4.Left11.expected,
    Slot4.Left18.expected,
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot5.Left5.expected,
    Slot5.Left12.expected,
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
    Slot13.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 458938481263847944470134784 }, { target := 37, numerator := 21147407274844984235463278592 }, { target := 40, numerator := 21147373791102201967763521536 }, { target := 47, numerator := 458894694830978825170452480 }, { target := 86, numerator := 1937599436464902154265559040 }, { target := 89, numerator := 6873883756464499885506297856 }, { target := 91, numerator := 1937184883693371954380668928 }, { target := 122, numerator := 502106192959314388605468672 }, { target := 124, numerator := 502105039622915666086985728 }, { target := 145, numerator := 1605850528276237621338832896 }, { target := 147, numerator := 73995919998826372428095029248 }, { target := 150, numerator := 73995802837402280257791197184 }, { target := 157, numerator := 1605697317183194014018437120 }, { target := 161, numerator := 69372086141208472745555263488 }, { target := 164, numerator := 246662156848490539745072381952 }, { target := 166, numerator := 69357698443241138088195391488 }, { target := 197, numerator := 16785114673604299418704543744 }, { target := 199, numerator := 16785078896992534038835101696 }, { target := 216, numerator := 459533104411951804591374336 }, { target := 218, numerator := 21174806890264841490391891968 }, { target := 221, numerator := 21174773363138884012232146944 }, { target := 228, numerator := 459489261247238179305553920 }, { target := 232, numerator := 69372157794595436917734506496 }, { target := 235, numerator := 246662410236495425052541452288 }, { target := 237, numerator := 69357770080633849658745028608 }, { target := 242, numerator := 203087593288681338207129829376 }, { target := 244, numerator := 203087166636813768690939985920 }, { target := 406, numerator := 1937600642973049877333803008 }, { target := 409, numerator := 6873890786190297668385767424 }, { target := 411, numerator := 1937186092192392187723382784 }, { target := 416, numerator := 16785275234017710665531129856 }, { target := 418, numerator := 16785239457499957927883046912 }, { target := 498, numerator := 364116504104478638503624704 }, { target := 500, numerator := 364114908852366480255221760 }]

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
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot19.Left5.expected,
    Slot19.Left12.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected,
    Slot20.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 160527212488610183242579968 }, { target := 17, numerator := 5610018300617237395243270144 }, { target := 19, numerator := 67686840092258237310448959488 }, { target := 27, numerator := 5610150526721131758351286272 }, { target := 34, numerator := 160531934849463553353580544 }, { target := 35, numerator := 4702041983732304312690278400 }, { target := 37, numerator := 166186917989439287908387258368 }, { target := 40, numerator := 166186987216003890501749047296 }, { target := 47, numerator := 4701983573045217909610119168 }, { target := 86, numerator := 3359359121213660016603561984 }, { target := 89, numerator := 12008270236287352317249847296 }, { target := 91, numerator := 3359958573311279952650305536 }, { target := 126, numerator := 160527595215765516255756288 }, { target := 127, numerator := 5610031675959101714495176704 }, { target := 129, numerator := 67687001470453001818742980608 }, { target := 137, numerator := 5610163902378248051519127552 }, { target := 144, numerator := 160532317587877885435183104 }, { target := 145, numerator := 16754461348324011524751360000 }, { target := 147, numerator := 592220323903404658305829699584 }, { target := 150, numerator := 592220567978011394632316878848 }, { target := 157, numerator := 16754252324711883365966413824 }, { target := 161, numerator := 124612142526780866042624212992 }, { target := 164, numerator := 445074371946235559156329218048 }, { target := 166, numerator := 124639714402036536079829434368 }, { target := 216, numerator := 4701629089855222930263244800 }, { target := 218, numerator := 166172547522217668922734280704 }, { target := 221, numerator := 166172616732731442444147621888 }, { target := 228, numerator := 4701570680867119486608605184 }, { target := 232, numerator := 124612109043038083774924455936 }, { target := 235, numerator := 445074254784811466986025385984 }, { target := 237, numerator := 124639680874910578601669689344 }, { target := 406, numerator := 3359264615934215893486141440 }, { target := 409, numerator := 12007935120982929031865303040 }, { target := 411, numerator := 3359864011215548830533550080 }, { target := 498, numerator := 160531934849463553353580544 }, { target := 500, numerator := 160532317587877885435183104 }]

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
    Slot21.Left0.expected,
    Slot21.Left2.expected,
    Slot24.Left0.expected,
    Slot24.Left3.expected,
    Slot24.Left5.expected,
    Slot25.Left0.expected,
    Slot25.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 341578980470704205362888704 }, { target := 17, numerator := 11175096372987062023461273600 }, { target := 19, numerator := 135400753196423100896680869888 }, { target := 27, numerator := 11175124707296578907179843584 }, { target := 34, numerator := 364116504104478638503624704 }, { target := 35, numerator := 135978092682409913708707840 }, { target := 37, numerator := 6649903403705066644328939520 }, { target := 40, numerator := 6649905830527428223146393600 }, { target := 47, numerator := 135986991031069036039372800 }, { target := 126, numerator := 341577444407150149831229440 }, { target := 127, numerator := 11175047221033432324339924992 }, { target := 129, numerator := 135400165166360766872197005312 }, { target := 137, numerator := 11175075555121709876363919360 }, { target := 144, numerator := 364114908852366480255221760 }, { target := 145, numerator := 521842116151603056665952256 }, { target := 147, numerator := 25520284892495068167476871168 }, { target := 150, numerator := 25520294205893217148458762240 }, { target := 157, numerator := 521876265278149320266219520 }, { target := 216, numerator := 135981262737477172176355328 }, { target := 218, numerator := 6650058432795163754898653184 }, { target := 221, numerator := 6650060859674101804034949120 }, { target := 228, numerator := 135990161293583352342773760 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk7.Parent1
