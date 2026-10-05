import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk2Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 44; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk2.Parent1

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
  [{ target := 26, numerator := 59778672136535489590067200 }, { target := 27, numerator := 2233531734316152164439818240 }, { target := 29, numerator := 24728515080787999458999664640 }, { target := 37, numerator := 2226393930273198219072634880 }, { target := 44, numerator := 59778672136535489590067200 }, { target := 80, numerator := 98922628215752416223559680 }, { target := 82, numerator := 3453468420297081795976888320 }, { target := 85, numerator := 3453458971861875688011202560 }, { target := 92, numerator := 98926741270256975567912960 }, { target := 131, numerator := 66593547869548243127894016 }, { target := 134, numerator := 227611019253603123475775488 }, { target := 136, numerator := 66593676901055267013132288 }, { target := 157, numerator := 203582642900791597413171200 }, { target := 158, numerator := 7606530510351745057596375040 }, { target := 160, numerator := 84215595215304974476446269440 }, { target := 168, numerator := 7582221957491060239740436480 }, { target := 175, numerator := 203582642900791597413171200 }, { target := 176, numerator := 3775996983919150184083226624 }, { target := 178, numerator := 131321255267396815284336590848 }, { target := 181, numerator := 131320931788626809812777172992 }, { target := 188, numerator := 3776155792849452299272060928 }, { target := 227, numerator := 2225702069879644104714878976 }, { target := 230, numerator := 7607258253795701095051296768 }, { target := 232, numerator := 2225706382394916985601261568 }, { target := 267, numerator := 59837447050271431422115840 }, { target := 268, numerator := 2235727762269250296876105728 }, { target := 270, numerator := 24752828373284219917652983808 }, { target := 278, numerator := 2228582940274878319412903936 }, { target := 285, numerator := 59837447050271431422115840 }, { target := 286, numerator := 3775970617747972655868280832 }, { target := 288, numerator := 131320358411126631479864459264 }, { target := 291, numerator := 131320034933125897119655264256 }, { target := 298, numerator := 3776129425496924293802491904 }, { target := 302, numerator := 24662205114559722165664481280 }, { target := 305, numerator := 84293296013640404095247319040 }, { target := 307, numerator := 24662252899992309381243863040 }, { target := 573, numerator := 98933459123187937924087808 }, { target := 575, numerator := 3453833017291973130354425856 }, { target := 578, numerator := 3453823568823834450113593344 }, { target := 585, numerator := 98937572676747630976434176 }, { target := 589, numerator := 2225675921265261150770036736 }, { target := 592, numerator := 7607168880080646409392488448 }, { target := 594, numerator := 2225680233729868535848501248 }, { target := 763, numerator := 66553453327494380412469248 }, { target := 766, numerator := 227473979557185938798936064 }, { target := 768, numerator := 66553582281314310725566464 }]

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
  [{ target := 26, numerator := 66593547869548243127894016 }, { target := 27, numerator := 2225702069879644104714878976 }, { target := 29, numerator := 24662205114559722165664481280 }, { target := 37, numerator := 2225675921265261150770036736 }, { target := 44, numerator := 66553453327494380412469248 }, { target := 80, numerator := 24841699100783600153395200 }, { target := 82, numerator := 1141454488827023515875016704 }, { target := 85, numerator := 1141438778112047226260815872 }, { target := 92, numerator := 24849623974709693144629248 }, { target := 131, numerator := 59778672136535489590067200 }, { target := 134, numerator := 203582642900791597413171200 }, { target := 136, numerator := 59837447050271431422115840 }, { target := 157, numerator := 227611019253603123475775488 }, { target := 158, numerator := 7607258253795701095051296768 }, { target := 160, numerator := 84293296013640404095247319040 }, { target := 168, numerator := 7607168880080646409392488448 }, { target := 175, numerator := 227473979557185938798936064 }, { target := 176, numerator := 818925925204955127768678400 }, { target := 178, numerator := 37628934701673981282948743168 }, { target := 181, numerator := 37628416785739753439493095424 }, { target := 188, numerator := 819187174835494836414447616 }, { target := 227, numerator := 2233531734316152164439818240 }, { target := 230, numerator := 7606530510351745057596375040 }, { target := 232, numerator := 2235727762269250296876105728 }, { target := 267, numerator := 66593676901055267013132288 }, { target := 268, numerator := 2225706382394916985601261568 }, { target := 270, numerator := 24662252899992309381243863040 }, { target := 278, numerator := 2225680233729868535848501248 }, { target := 285, numerator := 66553582281314310725566464 }, { target := 286, numerator := 818927132225950258403737600 }, { target := 288, numerator := 37628990163239931772405809152 }, { target := 291, numerator := 37628472246542343792110862336 }, { target := 298, numerator := 819188382241547735189684224 }, { target := 302, numerator := 24728515080787999458999664640 }, { target := 305, numerator := 84215595215304974476446269440 }, { target := 307, numerator := 24752828373284219917652983808 }, { target := 573, numerator := 24842906121778730788454400 }, { target := 575, numerator := 1141509950392974005332082688 }, { target := 578, numerator := 1141494238914637578878582784 }, { target := 585, numerator := 24850831380762591919865856 }, { target := 589, numerator := 2226393930273198219072634880 }, { target := 592, numerator := 7582221957491060239740436480 }, { target := 594, numerator := 2228582940274878319412903936 }, { target := 763, numerator := 59778672136535489590067200 }, { target := 766, numerator := 203582642900791597413171200 }, { target := 768, numerator := 59837447050271431422115840 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk2.Parent1
