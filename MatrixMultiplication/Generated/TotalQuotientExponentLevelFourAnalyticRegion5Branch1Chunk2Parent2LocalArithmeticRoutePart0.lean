import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk2Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 45; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk2.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left6.expected,
    Slot8.Left14.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 9049708208080285429923840 }, { target := 57, numerator := 314016327186733013797961728 }, { target := 59, numerator := 3448772074922682454594551808 }, { target := 67, numerator := 313403161595878112269172736 }, { target := 74, numerator := 8871018808259487664701440 }, { target := 110, numerator := 5311194892117164177752064 }, { target := 112, numerator := 175087669056972104860172288 }, { target := 115, numerator := 175087927119986152630648832 }, { target := 122, numerator := 5311452955131211948228608 }, { target := 152, numerator := 346970226938240197491425280 }, { target := 153, numerator := 11856086157596117998317338624 }, { target := 155, numerator := 129984565576735518300311650304 }, { target := 163, numerator := 11836133403713082507053236224 }, { target := 170, numerator := 338759604278986487451615232 }, { target := 206, numerator := 177511753662323045280251904 }, { target := 208, numerator := 5851812974342262285630701568 }, { target := 211, numerator := 5851821599372808047403466752 }, { target := 218, numerator := 177520378692868807053017088 }, { target := 257, numerator := 146288423165435844419911680 }, { target := 260, numerator := 500001248873438918203146240 }, { target := 262, numerator := 146288706613552141817610240 }, { target := 283, numerator := 111198909193656998622658560 }, { target := 284, numerator := 3046894018374919124749910016 }, { target := 286, numerator := 32453736723851111761755242496 }, { target := 294, numerator := 3055092973691192920076451840 }, { target := 301, numerator := 102988399543510213167415296 }, { target := 302, numerator := 1966943976154967678512005120 }, { target := 304, numerator := 64841837467076075711407063040 }, { target := 307, numerator := 64841933037941250142565826560 }, { target := 314, numerator := 1967039547020142109670768640 }, { target := 353, numerator := 7165310427993956214129033216 }, { target := 356, numerator := 24490414791820271253180121088 }, { target := 358, numerator := 7165324311483158939081637888 }, { target := 660, numerator := 2420849136062044349399040 }, { target := 661, numerator := 66332222191225226703929344 }, { target := 663, numerator := 706532115104610573472497664 }, { target := 671, numerator := 66510717052712095643074560 }, { target := 678, numerator := 2242102731647488165412864 }, { target := 679, numerator := 177509668169184599756242944 }, { target := 681, numerator := 5851744224439488678092341248 }, { target := 684, numerator := 5851752849368703448249270272 }, { target := 691, numerator := 177518293098399369913171968 }, { target := 695, numerator := 7165445529168268142844051456 }, { target := 698, numerator := 24490876556014720462417297408 }, { target := 700, numerator := 7165459412919242596137566208 }, { target := 966, numerator := 5307997135971547707604992 }, { target := 968, numerator := 174982252539385906634686464 }, { target := 971, numerator := 174982510447025767260880896 }, { target := 978, numerator := 5308255043611408333799424 }, { target := 982, numerator := 146320673123174820951883776 }, { target := 985, numerator := 500111476455339697182343168 }, { target := 987, numerator := 146320956633778563179347968 }]

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
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left3.expected,
    Slot14.Left11.expected,
    Slot14.Left18.expected,
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot20.Left5.expected,
    Slot20.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 146288423165435844419911680 }, { target := 15, numerator := 7165310427993956214129033216 }, { target := 20, numerator := 7165445529168268142844051456 }, { target := 28, numerator := 146320673123174820951883776 }, { target := 56, numerator := 5311194892117164177752064 }, { target := 57, numerator := 177511753662323045280251904 }, { target := 59, numerator := 1966943976154967678512005120 }, { target := 67, numerator := 177509668169184599756242944 }, { target := 74, numerator := 5307997135971547707604992 }, { target := 110, numerator := 6629631112843362136227840 }, { target := 112, numerator := 235769787207508836074127360 }, { target := 115, numerator := 235768833632212235247943680 }, { target := 122, numerator := 6629891178833344179732480 }, { target := 136, numerator := 500001248873438918203146240 }, { target := 137, numerator := 24490414791820271253180121088 }, { target := 142, numerator := 24490876556014720462417297408 }, { target := 150, numerator := 500111476455339697182343168 }, { target := 152, numerator := 175087669056972104860172288 }, { target := 153, numerator := 5851812974342262285630701568 }, { target := 155, numerator := 64841837467076075711407063040 }, { target := 163, numerator := 5851744224439488678092341248 }, { target := 170, numerator := 174982252539385906634686464 }, { target := 206, numerator := 247705259218953503797936128 }, { target := 208, numerator := 8809150201901034557996531712 }, { target := 211, numerator := 8809114573128934145818361856 }, { target := 218, numerator := 247714976156799070755618816 }, { target := 267, numerator := 146288706613552141817610240 }, { target := 268, numerator := 7165324311483158939081637888 }, { target := 273, numerator := 7165459412919242596137566208 }, { target := 281, numerator := 146320956633778563179347968 }, { target := 283, numerator := 410856760752198387878592512 }, { target := 284, numerator := 14660936172501742193221828608 }, { target := 286, numerator := 162371920735520957608100888576 }, { target := 294, numerator := 14632715714308823473868242944 }, { target := 301, numerator := 410751344079238002508824576 }, { target := 302, numerator := 2742465282259274143742558208 }, { target := 304, numerator := 97530382161027286263536812032 }, { target := 307, numerator := 97529987697579707465535062016 }, { target := 314, numerator := 2742572863199522906833944576 }, { target := 660, numerator := 11941344133964556127961088 }, { target := 661, numerator := 425235354849667877808635904 }, { target := 663, numerator := 4709612410219665016504713216 }, { target := 671, numerator := 424441634674347679584092160 }, { target := 678, numerator := 11938146222444752513531904 }, { target := 679, numerator := 246913655690985123386228736 }, { target := 681, numerator := 8780998379851651708662841344 }, { target := 684, numerator := 8780962864940120025618972672 }, { target := 691, numerator := 246923341575948309670920192 }, { target := 966, numerator := 6629631112843362136227840 }, { target := 968, numerator := 235769787207508836074127360 }, { target := 971, numerator := 235768833632212235247943680 }, { target := 978, numerator := 6629891178833344179732480 }]

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
    Slot21.Left1.expected,
    Slot21.Left3.expected,
    Slot21.Left11.expected,
    Slot21.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 2420077095236923293696000 }, { target := 112, numerator := 111200439730731361417297920 }, { target := 115, numerator := 111198909193656998622658560 }, { target := 122, numerator := 2420849136062044349399040 }, { target := 206, numerator := 66311067967779510000025600 }, { target := 208, numerator := 3046935955695083440320806912 }, { target := 211, numerator := 3046894018374919124749910016 }, { target := 218, numerator := 66332222191225226703929344 }, { target := 302, numerator := 706306792663408310851993600 }, { target := 304, numerator := 32454183415708232036774838272 }, { target := 307, numerator := 32453736723851111761755242496 }, { target := 314, numerator := 706532115104610573472497664 }, { target := 679, numerator := 66489505904892988882944000 }, { target := 681, numerator := 3055135023861430798390394880 }, { target := 684, numerator := 3055092973691192920076451840 }, { target := 691, numerator := 66510717052712095643074560 }, { target := 966, numerator := 2241387695416125528473600 }, { target := 968, numerator := 102989817071477651377487872 }, { target := 971, numerator := 102988399543510213167415296 }, { target := 978, numerator := 2242102731647488165412864 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk2.Parent2
