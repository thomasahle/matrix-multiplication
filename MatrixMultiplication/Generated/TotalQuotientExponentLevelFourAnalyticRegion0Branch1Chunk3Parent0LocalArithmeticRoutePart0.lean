import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk3Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 44; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk3.Parent0

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
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 69166592207330725022662656 }, { target := 27, numerator := 3486451457986615820867862528 }, { target := 29, numerator := 38294032219319080072419213312 }, { target := 37, numerator := 3486475815279328814432256000 }, { target := 44, numerator := 69158473109759727167864832 }, { target := 80, numerator := 188341857772201863270105088 }, { target := 82, numerator := 6755039531503327799893032960 }, { target := 85, numerator := 6757438171811115610933297152 }, { target := 92, numerator := 190748692712778047353257984 }, { target := 131, numerator := 88426175656819920123985920 }, { target := 134, numerator := 301813478998404675145826304 }, { target := 136, numerator := 88438301514374122171269120 }, { target := 157, numerator := 223695386659845441979416576 }, { target := 158, numerator := 11275719709123369410377023488 }, { target := 160, numerator := 123848784083325989109368881152 }, { target := 168, numerator := 11275798484350506343858176000 }, { target := 175, numerator := 223669128250799797485699072 }, { target := 176, numerator := 6788889026701207759088517120 }, { target := 178, numerator := 243579569961394543845326192640 }, { target := 181, numerator := 243666794184421327521982709760 }, { target := 188, numerator := 6876407200734015820451020800 }, { target := 227, numerator := 3770213881190776974354677760 }, { target := 230, numerator := 12868377034266832978587942912 }, { target := 232, numerator := 3770730889600703256707727360 }, { target := 267, numerator := 69206581740922401177206784 }, { target := 268, numerator := 3488467193665438627965960192 }, { target := 270, numerator := 38316172394784207090449645568 }, { target := 278, numerator := 3488491565040626181341184000 }, { target := 285, numerator := 69198457949193216718798848 }, { target := 286, numerator := 6791284613143702473076113408 }, { target := 288, numerator := 243666690984848227167947980800 }, { target := 291, numerator := 243753955874530154520470618112 }, { target := 298, numerator := 6878843539057773558664003584 }, { target := 302, numerator := 36190150134109611515990507520 }, { target := 305, numerator := 123523097502722155942955188224 }, { target := 307, numerator := 36195112879610383987082526720 }, { target := 573, numerator := 190757324447213329443717120 }, { target := 575, numerator := 6842853666632374555351449600 }, { target := 578, numerator := 6845293058436367622476922880 }, { target := 585, numerator := 193204997290057220342415360 }, { target := 589, numerator := 3770245286249019008184483840 }, { target := 592, numerator := 12868484225037165074482987008 }, { target := 594, numerator := 3770762298965512434210570240 }, { target := 763, numerator := 88418324392259411666534400 }, { target := 766, numerator := 301786681305821651172065280 }, { target := 768, numerator := 88430449173171827795558400 }]

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
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left3.expected,
    Slot15.Left11.expected,
    Slot15.Left18.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected,
    Slot20.Left5.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected,
    Slot21.Left5.expected,
    Slot21.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 88426175656819920123985920 }, { target := 27, numerator := 3770213881190776974354677760 }, { target := 29, numerator := 36190150134109611515990507520 }, { target := 37, numerator := 3770245286249019008184483840 }, { target := 44, numerator := 88418324392259411666534400 }, { target := 80, numerator := 46583907063931296943177728 }, { target := 82, numerator := 1634177517243718444882329600 }, { target := 85, numerator := 1634172107453136477962108928 }, { target := 92, numerator := 46593324106796202322821120 }, { target := 131, numerator := 69166592207330725022662656 }, { target := 134, numerator := 223695386659845441979416576 }, { target := 136, numerator := 69206581740922401177206784 }, { target := 157, numerator := 301813478998404675145826304 }, { target := 158, numerator := 12868377034266832978587942912 }, { target := 160, numerator := 123523097502722155942955188224 }, { target := 168, numerator := 12868484225037165074482987008 }, { target := 175, numerator := 301786681305821651172065280 }, { target := 176, numerator := 1600328022045838485686845440 }, { target := 178, numerator := 56139989938012642143633408000 }, { target := 181, numerator := 56139804091869469997468221440 }, { target := 188, numerator := 1600651531998767777159577600 }, { target := 227, numerator := 3486451457986615820867862528 }, { target := 230, numerator := 11275719709123369410377023488 }, { target := 232, numerator := 3488467193665438627965960192 }, { target := 267, numerator := 88438301514374122171269120 }, { target := 268, numerator := 3770730889600703256707727360 }, { target := 270, numerator := 36195112879610383987082526720 }, { target := 278, numerator := 3770762298965512434210570240 }, { target := 285, numerator := 88430449173171827795558400 }, { target := 286, numerator := 1600325666120549615819292672 }, { target := 288, numerator := 56139907291442570351502950400 }, { target := 291, numerator := 56139721445572991882700521472 }, { target := 298, numerator := 1600649175597223246697594880 }, { target := 302, numerator := 38294032219319080072419213312 }, { target := 305, numerator := 123848784083325989109368881152 }, { target := 307, numerator := 38316172394784207090449645568 }, { target := 573, numerator := 46584692372360920232361984 }, { target := 575, numerator := 1634205066100409042259148800 }, { target := 578, numerator := 1634199656218629182884675584 }, { target := 585, numerator := 46594109573977712476815360 }, { target := 589, numerator := 3486475815279328814432256000 }, { target := 592, numerator := 11275798484350506343858176000 }, { target := 594, numerator := 3488491565040626181341184000 }, { target := 763, numerator := 69158473109759727167864832 }, { target := 766, numerator := 223669128250799797485699072 }, { target := 768, numerator := 69198457949193216718798848 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk3.Parent0
