import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk11Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 47; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk11.Parent1

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
  [{ target := 0, numerator := 3133309050849941077868150784 }, { target := 2, numerator := 115708934720546565312447774720 }, { target := 5, numerator := 115708906386347668094576492544 }, { target := 12, numerator := 3133337385048838295739432960 }, { target := 16, numerator := 28136420516541487874939289600 }, { target := 19, numerator := 102338226500356371971571712000 }, { target := 21, numerator := 28136420516541487874939289600 }, { target := 26, numerator := 3817271736875101598612004536320 }, { target := 28, numerator := 3817271732729195868045782810624 }, { target := 30, numerator := 27944269352038277713842143232 }, { target := 33, numerator := 101639331294988084553229271040 }, { target := 35, numerator := 27944269352038277713842143232 }, { target := 40, numerator := 213157851335231339154007654400 }, { target := 42, numerator := 213157749693671493014378250240 }, { target := 44, numerator := 321263928259336615997334355968 }, { target := 45, numerator := 8694596567621278307597680640 }, { target := 47, numerator := 8694592421715547741375954944 }, { target := 49, numerator := 52728508548311666083984572416 }, { target := 50, numerator := 28136420516541487874939289600 }, { target := 53, numerator := 102338226500356371971571712000 }, { target := 55, numerator := 28136420516541487874939289600 }, { target := 60, numerator := 13200443220449134357211309408256 }, { target := 62, numerator := 13200443135257458538802172657664 }, { target := 64, numerator := 9400316738339927013595291844608 }, { target := 65, numerator := 175574756494545813566327357440 }, { target := 67, numerator := 175574672773997835035527348224 }, { target := 69, numerator := 1304750115780563141610086334464 }, { target := 70, numerator := 41509676942287907342711259136 }, { target := 71, numerator := 3817270506698632811069426368512 }, { target := 73, numerator := 3817270502552727080503204642816 }, { target := 75, numerator := 9400321328480148362890439557120 }, { target := 76, numerator := 42631560102890283216838590464 }, { target := 77, numerator := 28218771015614292229695209472 }, { target := 80, numerator := 102637753016942780865147043840 }, { target := 82, numerator := 28218771015614292229695209472 }, { target := 87, numerator := 175855227351565854802056314880 }, { target := 89, numerator := 175855143497278981736862056448 }, { target := 91, numerator := 42631560102890283216838590464 }, { target := 92, numerator := 157624621645263174479674081280 }, { target := 94, numerator := 157624546484004446150106021888 }, { target := 96, numerator := 721370872267327687063874043904 }, { target := 97, numerator := 39265910621083155594456596480 }, { target := 98, numerator := 213157851335231339154007654400 }, { target := 100, numerator := 213157749693671493014378250240 }, { target := 102, numerator := 1304750115780563141610086334464 }, { target := 103, numerator := 721370872267327687063874043904 }, { target := 104, numerator := 321261633189225941349760499712 }, { target := 105, numerator := 8694596567621278307597680640 }, { target := 107, numerator := 8694592421715547741375954944 }, { target := 109, numerator := 41509676942287907342711259136 }, { target := 110, numerator := 39265910621083155594456596480 }, { target := 111, numerator := 52728508548311666083984572416 }]

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
    Slot11.Left0.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot15.Left0.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot16.Left5.expected,
    Slot16.Left12.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 358491112989534736969069756416 }, { target := 2, numerator := 12674540458904794011236187504640 }, { target := 5, numerator := 12674505225328465320813248118784 }, { target := 12, numerator := 358528669970172999257454280704 }, { target := 16, numerator := 10043838547404763280364940558336 }, { target := 19, numerator := 34184421690739351122873879101440 }, { target := 21, numerator := 10043837333756577182866120638464 }, { target := 26, numerator := 6289001918541912996650982309888 }, { target := 27, numerator := 24451235683033492999611875328 }, { target := 28, numerator := 6288705111776568478530627698688 }, { target := 29, numerator := 24691424638662505700983308288 }, { target := 44, numerator := 94100707957550272315234713600 }, { target := 50, numerator := 10043541740639418762244585947136 }, { target := 53, numerator := 34183402805010799490059919687680 }, { target := 55, numerator := 10043540526991232664745766027264 }, { target := 60, numerator := 21352398408971293754128133521408 }, { target := 61, numerator := 88934414883114573984075612160 }, { target := 62, numerator := 21351379523242742121314174107648 }, { target := 63, numerator := 89808033889824933257003663360 }, { target := 64, numerator := 3431552523927212750597471076352 }, { target := 71, numerator := 6264382550589939194760410431488 }, { target := 73, numerator := 6264085743824594676640055820288 }, { target := 75, numerator := 3431512657709364365052577054720 }, { target := 104, numerator := 94140574175398657860128735232 }]

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
    Slot17.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot19.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 54778846738378077164286246912 }, { target := 1, numerator := 53637620764661867223363616768 }, { target := 2, numerator := 42225361027499767814137315328 }, { target := 3, numerator := 1327245807431952161293018857472 }, { target := 4, numerator := 42225361027499767814137315328 }, { target := 5, numerator := 42225361027499767814137315328 }, { target := 6, numerator := 43366587001215977755059945472 }, { target := 7, numerator := 43366587001215977755059945472 }, { target := 8, numerator := 733808301099522992013251182592 }, { target := 9, numerator := 39942909080067347932292055040 }, { target := 10, numerator := 1327245807431952161293018857472 }, { target := 11, numerator := 733808301099522992013251182592 }, { target := 12, numerator := 54778846738378077164286246912 }, { target := 13, numerator := 42225361027499767814137315328 }, { target := 14, numerator := 39942909080067347932292055040 }, { target := 15, numerator := 53637620764661867223363616768 }, { target := 16, numerator := 8394782892875716986646036480 }, { target := 17, numerator := 205807580599533706769386700800 }, { target := 18, numerator := 8394782892875716986646036480 }, { target := 19, numerator := 172499248476188120015920168960 }, { target := 20, numerator := 169520454546458026891626414080 }, { target := 21, numerator := 8394782892875716986646036480 }, { target := 22, numerator := 169791253994615308084744028160 }, { target := 23, numerator := 152189289864392030532099112960 }, { target := 24, numerator := 205807580599533706769386700800 }, { target := 25, numerator := 8394782892875716986646036480 }, { target := 50, numerator := 8394778889932252991673335808 }, { target := 51, numerator := 205807482462855234634572103680 }, { target := 52, numerator := 8394778889932252991673335808 }, { target := 53, numerator := 172499166222156295345029513216 }, { target := 54, numerator := 169520373712825495896371232768 }, { target := 55, numerator := 8394778889932252991673335808 }, { target := 56, numerator := 169791173031855568573521985536 }, { target := 57, numerator := 152189217294900844558723055616 }, { target := 58, numerator := 205807482462855234634572103680 }, { target := 59, numerator := 8394778889932252991673335808 }, { target := 71, numerator := 24619367951973801890571878400 }, { target := 72, numerator := 24451235683033492999611875328 }, { target := 73, numerator := 24619367951973801890571878400 }, { target := 74, numerator := 24691424638662505700983308288 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk11.Parent1
