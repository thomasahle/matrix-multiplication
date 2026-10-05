import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk15Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 62; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15.Parent0

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
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected,
    Slot2.Left10.expected,
    Slot2.Left11.expected,
    Slot2.Left12.expected,
    Slot2.Left13.expected,
    Slot2.Left14.expected,
    Slot2.Left15.expected,
    Slot3.Left0.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot5.Left0.expected,
    Slot5.Left3.expected,
    Slot5.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 696341272098026404630757376 }, { target := 1, numerator := 793055337667196738607251456 }, { target := 2, numerator := 618970019642690137449562112 }, { target := 3, numerator := 8298066825834814655183192064 }, { target := 4, numerator := 735026898325694538221355008 }, { target := 5, numerator := 618970019642690137449562112 }, { target := 6, numerator := 735026898325694538221355008 }, { target := 7, numerator := 715684085211860471426056192 }, { target := 8, numerator := 27041252733140025379827744768 }, { target := 9, numerator := 715684085211860471426056192 }, { target := 10, numerator := 8298066825834814655183192064 }, { target := 11, numerator := 27041252733140025379827744768 }, { target := 12, numerator := 696341272098026404630757376 }, { target := 13, numerator := 715684085211860471426056192 }, { target := 14, numerator := 715684085211860471426056192 }, { target := 15, numerator := 793055337667196738607251456 }, { target := 16, numerator := 63073966807527581160856092672 }, { target := 19, numerator := 230378818949783529762639052800 }, { target := 21, numerator := 63073945556878408247452631040 }, { target := 26, numerator := 884794360256478088276180205568 }, { target := 28, numerator := 884794571152577166254700232704 }, { target := 40, numerator := 4845374685015433732222353408 }, { target := 42, numerator := 4845374685015433732222353408 }, { target := 44, numerator := 1798881619586568211962789888 }, { target := 45, numerator := 251456570479842868338884608 }, { target := 47, numerator := 251456570479842868338884608 }, { target := 49, numerator := 2030995376952577013506375680 }, { target := 50, numerator := 63073966807527581160856092672 }, { target := 53, numerator := 230378818949783529762639052800 }, { target := 55, numerator := 63073945556878408247452631040 }, { target := 60, numerator := 3227461443498324638988865896448 }, { target := 62, numerator := 3227462211742338302794157522944 }, { target := 64, numerator := 1740853180245066011576893440 }, { target := 65, numerator := 7804825091432045951903072256 }, { target := 67, numerator := 7804825091432045951903072256 }, { target := 69, numerator := 22921233539893369152429096960 }, { target := 70, numerator := 2030995376952577013506375680 }, { target := 71, numerator := 884804626681140915190743695360 }, { target := 73, numerator := 884804837577381856557525893120 }, { target := 75, numerator := 1740853180245066011576893440 }, { target := 76, numerator := 2030995376952577013506375680 }, { target := 87, numerator := 7804825091432045951903072256 }, { target := 89, numerator := 7804825091432045951903072256 }, { target := 91, numerator := 2030995376952577013506375680 }, { target := 92, numerator := 8133652914367225087423152128 }, { target := 94, numerator := 8133652914367225087423152128 }, { target := 96, numerator := 84199265484519692759935746048 }, { target := 97, numerator := 2089023816294079213892272128 }, { target := 98, numerator := 4845374685015433732222353408 }, { target := 100, numerator := 4845374685015433732222353408 }, { target := 102, numerator := 22921233539893369152429096960 }, { target := 103, numerator := 84199265484519692759935746048 }, { target := 104, numerator := 1798881619586568211962789888 }, { target := 105, numerator := 241785163922925834941235200 }, { target := 107, numerator := 241785163922925834941235200 }, { target := 109, numerator := 2030995376952577013506375680 }, { target := 110, numerator := 2089023816294079213892272128 }, { target := 111, numerator := 2030995376952577013506375680 }]

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
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot7.Left0.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot18.Left5.expected,
    Slot18.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 2124115391062629746600082145280 }, { target := 2, numerator := 83125365066656836287586669428736 }, { target := 5, numerator := 83125387209833274463353076449280 }, { target := 12, numerator := 2124138063144114003766753099776 }, { target := 16, numerator := 75082348532213393646230251241472 }, { target := 19, numerator := 274419099263791564969002928177152 }, { target := 21, numerator := 75082254018404181086994035638272 }, { target := 26, numerator := 75165934627610993332267492835328 }, { target := 28, numerator := 75165941931342448201667239215104 }, { target := 44, numerator := 2478495037064618304269235257344 }, { target := 50, numerator := 75082355856567677886089444458496 }, { target := 53, numerator := 274419126818139405082989999161344 }, { target := 55, numerator := 75082261338768947656297401024512 }, { target := 60, numerator := 274727296279474445452038922829824 }, { target := 62, numerator := 274727323761738076380200205025280 }, { target := 64, numerator := 97309355272639941312280273092608 }, { target := 71, numerator := 75165839939077684737917805658112 }, { target := 73, numerator := 75165847238812694274634921541632 }, { target := 75, numerator := 97309373571810062432155476164608 }, { target := 104, numerator := 2478517491917244349432226381824 }]

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
    Slot19.Left0.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot21.Left0.expected,
    Slot21.Left3.expected,
    Slot21.Left5.expected,
    Slot23.Left0.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 366234655931118583535034695680 }, { target := 1, numerator := 2030995376952577013506375680 }, { target := 2, numerator := 14571815493139704728927785189376 }, { target := 3, numerator := 22921233539893369152429096960 }, { target := 4, numerator := 2030995376952577013506375680 }, { target := 5, numerator := 14571811932475376645215294062592 }, { target := 6, numerator := 2030995376952577013506375680 }, { target := 7, numerator := 2030995376952577013506375680 }, { target := 8, numerator := 84199265484519692759935746048 }, { target := 9, numerator := 2089023816294079213892272128 }, { target := 10, numerator := 22921233539893369152429096960 }, { target := 11, numerator := 84199265484519692759935746048 }, { target := 12, numerator := 366234655931118583535034695680 }, { target := 13, numerator := 2030995376952577013506375680 }, { target := 14, numerator := 2089023816294079213892272128 }, { target := 15, numerator := 2030995376952577013506375680 }, { target := 16, numerator := 884794360256478088276180205568 }, { target := 17, numerator := 4845374685015433732222353408 }, { target := 18, numerator := 251456570479842868338884608 }, { target := 19, numerator := 3227461443498324638988865896448 }, { target := 20, numerator := 7804825091432045951903072256 }, { target := 21, numerator := 884804626681140915190743695360 }, { target := 22, numerator := 7804825091432045951903072256 }, { target := 23, numerator := 8133652914367225087423152128 }, { target := 24, numerator := 4845374685015433732222353408 }, { target := 25, numerator := 241785163922925834941235200 }, { target := 26, numerator := 63073966807527581160856092672 }, { target := 28, numerator := 63073966807527581160856092672 }, { target := 50, numerator := 884794571152577166254700232704 }, { target := 51, numerator := 4845374685015433732222353408 }, { target := 52, numerator := 251456570479842868338884608 }, { target := 53, numerator := 3227462211742338302794157522944 }, { target := 54, numerator := 7804825091432045951903072256 }, { target := 55, numerator := 884804837577381856557525893120 }, { target := 56, numerator := 7804825091432045951903072256 }, { target := 57, numerator := 8133652914367225087423152128 }, { target := 58, numerator := 4845374685015433732222353408 }, { target := 59, numerator := 241785163922925834941235200 }, { target := 60, numerator := 230378818949783529762639052800 }, { target := 62, numerator := 230378818949783529762639052800 }, { target := 71, numerator := 63073945556878408247452631040 }, { target := 73, numerator := 63073945556878408247452631040 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15.Parent0
