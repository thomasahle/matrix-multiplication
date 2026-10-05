import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk3Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 42; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk3.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left6.expected,
    Slot11.Left14.expected,
    Slot12.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 2489214940052757363556352 }, { target := 72, numerator := 84224743445136705046183936 }, { target := 74, numerator := 1026740476105176662274998272 }, { target := 82, numerator := 84225411074789540121018368 }, { target := 89, numerator := 2646544684167885966278656 }, { target := 146, numerator := 23260778683381342009294848 }, { target := 147, numerator := 812905127282612581573853184 }, { target := 149, numerator := 9807985716285661880745197568 }, { target := 157, numerator := 812924287162680085988769792 }, { target := 164, numerator := 23261462964812324309827584 }, { target := 200, numerator := 23139534932281919956582400 }, { target := 202, numerator := 815163050210335925846671360 }, { target := 205, numerator := 815163510481032592878469120 }, { target := 212, numerator := 23139288621974049762836480 }, { target := 242, numerator := 273032041343534804596948992 }, { target := 243, numerator := 9541776281082508112912449536 }, { target := 245, numerator := 115124880298995608035233103872 }, { target := 253, numerator := 9542001177301071316352237568 }, { target := 260, numerator := 273040073351340633291227136 }, { target := 296, numerator := 1070062196084019528906833920 }, { target := 298, numerator := 37707312634984670777680330752 }, { target := 301, numerator := 37707333427123773003377147904 }, { target := 308, numerator := 1070050636301635414589964288 }, { target := 640, numerator := 23260950910601241865224192 }, { target := 641, numerator := 812911146186451525237211136 }, { target := 643, numerator := 9808058336473305909477507072 }, { target := 651, numerator := 812930306208382417914298368 }, { target := 658, numerator := 23261635197098773746548736 }, { target := 659, numerator := 1069829485789932689974886400 }, { target := 661, numerator := 37699089948422757039422308352 }, { target := 664, numerator := 37699110737040607306468818944 }, { target := 671, numerator := 1069817928865645489178017792 }, { target := 1017, numerator := 750566224323572140081152 }, { target := 1018, numerator := 26230382930116484913954816 }, { target := 1020, numerator := 316478777752677215404818432 }, { target := 1028, numerator := 26231001170762531453534208 }, { target := 1035, numerator := 750588304346645230780416 }, { target := 1036, numerator := 23282793767925505746534400 }, { target := 1038, numerator := 820273425339448466719375360 }, { target := 1041, numerator := 820273885610145133751173120 }, { target := 1048, numerator := 23282544952490342827950080 }]

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
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left3.expected,
    Slot16.Left11.expected,
    Slot16.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 11978544880759502536704000 }, { target := 30, numerator := 541115420135423759666380800 }, { target := 35, numerator := 541023779553199885438156800 }, { target := 43, numerator := 11978544880759502536704000 }, { target := 71, numerator := 750470542534738886787072 }, { target := 72, numerator := 23260778683381342009294848 }, { target := 74, numerator := 273032041343534804596948992 }, { target := 82, numerator := 23260950910601241865224192 }, { target := 89, numerator := 750566224323572140081152 }, { target := 104, numerator := 417024633690779342665154560 }, { target := 105, numerator := 18838553606696452820683456512 }, { target := 110, numerator := 18835363204138083161999409152 }, { target := 118, numerator := 417024633690779342665154560 }, { target := 146, numerator := 84224743445136705046183936 }, { target := 147, numerator := 2747481431153382848257327104 }, { target := 149, numerator := 33234670959871991972496408576 }, { target := 157, numerator := 2747489100109978640943415296 }, { target := 164, numerator := 89475255047382677141323776 }, { target := 226, numerator := 417025093961476009696952320 }, { target := 227, numerator := 18838574398835555046380273664 }, { target := 232, numerator := 18835383992755933429045919744 }, { target := 240, numerator := 417025093961476009696952320 }, { target := 242, numerator := 1026740476105176662274998272 }, { target := 243, numerator := 33500880395075145740329156608 }, { target := 245, numerator := 405293459918747555392863076352 }, { target := 253, numerator := 33500973223577191350630612992 }, { target := 260, numerator := 1091043260450897179235581952 }, { target := 624, numerator := 11978493739570983977615360 }, { target := 625, numerator := 541113109897745734588956672 }, { target := 630, numerator := 541021469706772077988544512 }, { target := 638, numerator := 11978493739570983977615360 }, { target := 640, numerator := 84225411074789540121018368 }, { target := 641, numerator := 2747502241086207201694973952 }, { target := 643, numerator := 33234916064404956757505343488 }, { target := 651, numerator := 2747509910186073757526786048 }, { target := 658, numerator := 89475927231300635394572288 }, { target := 1017, numerator := 2646544684167885966278656 }, { target := 1018, numerator := 86506335082078516537196544 }, { target := 1020, numerator := 1047604556049560597121990656 }, { target := 1028, numerator := 86506561257636877687586816 }, { target := 1035, numerator := 2818179973450718454480896 }]

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
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 11160990051522417419878400 }, { target := 30, numerator := 528946775948595769240453120 }, { target := 35, numerator := 528805706236732804536729600 }, { target := 43, numerator := 11304248887166003209830400 }, { target := 104, numerator := 398138416519556583181516800 }, { target := 105, numerator := 18868759028288217956996874240 }, { target := 110, numerator := 18863726744284673877422899200 }, { target := 118, numerator := 403248791648669124054220800 }, { target := 226, numerator := 398138416519556583181516800 }, { target := 227, numerator := 18868759028288217956996874240 }, { target := 232, numerator := 18863726744284673877422899200 }, { target := 240, numerator := 403248791648669124054220800 }, { target := 624, numerator := 11160794882403065785221120 }, { target := 625, numerator := 528937526403889680001007616 }, { target := 630, numerator := 528796459158873411189473280 }, { target := 638, numerator := 11304051212919358850334720 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk3.Parent0
