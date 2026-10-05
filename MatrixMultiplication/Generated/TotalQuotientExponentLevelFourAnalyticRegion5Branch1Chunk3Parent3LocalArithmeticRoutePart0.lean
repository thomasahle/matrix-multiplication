import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk3Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 55; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk3.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot5.Left5.expected,
    Slot5.Left12.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 42030241133987255392665600 }, { target := 27, numerator := 1151645202552995306442588160 }, { target := 29, numerator := 12266652524683283315776552960 }, { target := 37, numerator := 1154744190407180401665638400 }, { target := 44, numerator := 38926886047764131568680960 }, { target := 80, numerator := 90814168783207857903370240 }, { target := 82, numerator := 3039685469031689571773972480 }, { target := 85, numerator := 3039690450178947679801835520 }, { target := 92, numerator := 90817842324387907743252480 }, { target := 131, numerator := 32496595796591082582573056 }, { target := 134, numerator := 115449112963271811902996480 }, { target := 136, numerator := 32453413252240422322831360 }, { target := 157, numerator := 143138468386705021442457600 }, { target := 158, numerator := 3922050551478580168475279360 }, { target := 160, numerator := 41775393317818548625772380160 }, { target := 168, numerator := 3932604485099445285185126400 }, { target := 175, numerator := 132569661691402383429468160 }, { target := 176, numerator := 3344588210350469461418442752 }, { target := 178, numerator := 112367200785439133083486912512 }, { target := 181, numerator := 112367389421693723199798247424 }, { target := 188, numerator := 3344716763241946547484622848 }, { target := 227, numerator := 1086107330851323975529660416 }, { target := 230, numerator := 3858561946443807278267105280 }, { target := 232, numerator := 1084664075739999838886952960 }, { target := 267, numerator := 42071565634995050847928320 }, { target := 268, numerator := 1152777510197431826856804352 }, { target := 270, numerator := 12278713204825530741305638912 }, { target := 278, numerator := 1155879545003603116142100480 }, { target := 285, numerator := 38965159302884963240640512 }, { target := 286, numerator := 3344569739903106488085774336 }, { target := 288, numerator := 112366562847788957681336713216 }, { target := 291, numerator := 112366751482786480551658258432 }, { target := 298, numerator := 3344698292364489809738072064 }, { target := 302, numerator := 12034765179209625935261204480 }, { target := 305, numerator := 42755338847116154097788518400 }, { target := 307, numerator := 12018772987770437788028108800 }, { target := 573, numerator := 90820828114957887323766784 }, { target := 575, numerator := 3039919650094172743783153664 }, { target := 578, numerator := 3039924631746396960029933568 }, { target := 585, numerator := 90824501743958129897373696 }, { target := 589, numerator := 1086094570741982626710552576 }, { target := 592, numerator := 3858516614209194334177198080 }, { target := 594, numerator := 1084651332586711087117762560 }, { target := 763, numerator := 32477030295601014393274368 }, { target := 766, numerator := 115379603536865297631805440 }, { target := 768, numerator := 32433873750531002943406080 }]

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
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot18.Left5.expected,
    Slot18.Left12.expected,
    Slot19.Left0.expected,
    Slot19.Left1.expected,
    Slot19.Left3.expected,
    Slot19.Left11.expected,
    Slot19.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 89480558418468399250145280 }, { target := 27, numerator := 3343293848607095707272216576 }, { target := 29, numerator := 37015230670138251835852455936 }, { target := 37, numerator := 3332609524770220725409677312 }, { target := 44, numerator := 89480558418468399250145280 }, { target := 80, numerator := 79745434210069687975280640 }, { target := 82, numerator := 2835989474294412247365058560 }, { target := 85, numerator := 2835978004082150796983009280 }, { target := 92, numerator := 79748562449777356261294080 }, { target := 131, numerator := 131510799552455654642810880 }, { target := 134, numerator := 448975321303839345884528640 }, { target := 136, numerator := 131552297430790104793743360 }, { target := 157, numerator := 305836852917134324442071040 }, { target := 158, numerator := 11427090835232966152518893568 }, { target := 160, numerator := 126514874943162454599215874048 }, { target := 168, numerator := 11390572735261621592329814016 }, { target := 175, numerator := 305836852917134324442071040 }, { target := 176, numerator := 2628870240574333986411642880 }, { target := 178, numerator := 93490597993548944086946283520 }, { target := 181, numerator := 93490219869083689245485301760 }, { target := 188, numerator := 2628973365428494397719183360 }, { target := 227, numerator := 4494939051160091013714804736 }, { target := 230, numerator := 15349141386711546320994172928 }, { target := 232, numerator := 4496077836763091245434142720 }, { target := 267, numerator := 89480731795795053945815040 }, { target := 268, numerator := 3343300326565659418577338368 }, { target := 270, numerator := 37015302390765084344580046848 }, { target := 278, numerator := 3332615982026862849599471616 }, { target := 285, numerator := 89480731795795053945815040 }, { target := 286, numerator := 2628874115285679891357368320 }, { target := 288, numerator := 93490735790034746254588641280 }, { target := 291, numerator := 93490357665012170959240560640 }, { target := 298, numerator := 2628977240291836790088663040 }, { target := 302, numerator := 49281883194821535151629008896 }, { target := 305, numerator := 168290268260981003224988254208 }, { target := 307, numerator := 49294015595590615085885685760 }, { target := 573, numerator := 79749308921415592921006080 }, { target := 575, numerator := 2836127270780214415007416320 }, { target := 578, numerator := 2836115800010632510738268160 }, { target := 585, numerator := 79752437313119748630773760 }, { target := 589, numerator := 4487353715177401127075315712 }, { target := 592, numerator := 15323177220361066877514940416 }, { target := 594, numerator := 4488495527030465965741572096 }, { target := 763, numerator := 128407444466232530818826240 }, { target := 766, numerator := 438406514608536707871539200 }, { target := 768, numerator := 128445891098680017186455552 }]

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
    Slot23.Left0.expected,
    Slot23.Left3.expected,
    Slot23.Left5.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected,
    Slot24.Left5.expected,
    Slot24.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 32496595796591082582573056 }, { target := 27, numerator := 1086107330851323975529660416 }, { target := 29, numerator := 12034765179209625935261204480 }, { target := 37, numerator := 1086094570741982626710552576 }, { target := 44, numerator := 32477030295601014393274368 }, { target := 80, numerator := 11068734573138169928089600 }, { target := 82, numerator := 508598736056057214053384192 }, { target := 85, numerator := 508591735820955691102765056 }, { target := 92, numerator := 11072265665180531062472704 }, { target := 157, numerator := 115449112963271811902996480 }, { target := 158, numerator := 3858561946443807278267105280 }, { target := 160, numerator := 42755338847116154097788518400 }, { target := 168, numerator := 3858516614209194334177198080 }, { target := 175, numerator := 115379603536865297631805440 }, { target := 176, numerator := 410815228457355585362329600 }, { target := 178, numerator := 18876602791890188996540628992 }, { target := 181, numerator := 18876342978705268435851411456 }, { target := 188, numerator := 410946284665678346063970304 }, { target := 267, numerator := 32453413252240422322831360 }, { target := 268, numerator := 1084664075739999838886952960 }, { target := 270, numerator := 12018772987770437788028108800 }, { target := 278, numerator := 1084651332586711087117762560 }, { target := 285, numerator := 32433873750531002943406080 }, { target := 286, numerator := 410816334893267788444467200 }, { target := 288, numerator := 18876653631658976945209606144 }, { target := 291, numerator := 18876393817774309592417697792 }, { target := 298, numerator := 410947391454560169941270528 }, { target := 573, numerator := 11068533402972314822246400 }, { target := 575, numerator := 508589492461732132477206528 }, { target := 578, numerator := 508582492353857298999803904 }, { target := 585, numerator := 11072064430838381266599936 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk3.Parent3
