import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk2Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 43; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk2.Parent3

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
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left6.expected,
    Slot12.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 1797401817406231793369088 }, { target := 57, numerator := 48942211709192995665346560 }, { target := 59, numerator := 582891090760563998406475776 }, { target := 67, numerator := 48942497250638694860193792 }, { target := 74, numerator := 1796871526149933288652800 }, { target := 110, numerator := 9064922174047351241441280 }, { target := 112, numerator := 331564741884212746282598400 }, { target := 115, numerator := 331565026113422104052367360 }, { target := 122, numerator := 9030286814678468725309440 }, { target := 152, numerator := 102243390544672559128903680 }, { target := 153, numerator := 2784028377763737901832601600 }, { target := 155, numerator := 33157172125064690591449743360 }, { target := 163, numerator := 2784044620501041596722053120 }, { target := 170, numerator := 102213225461108554334208000 }, { target := 206, numerator := 207477848230614938305953792 }, { target := 208, numerator := 7588850502459522469865717760 }, { target := 211, numerator := 7588857007894828982734946304 }, { target := 218, numerator := 206685114471121298669961216 }, { target := 257, numerator := 281454470671727302268682240 }, { target := 260, numerator := 1009963630658930678691790848 }, { target := 262, numerator := 281625785945635187947732992 }, { target := 283, numerator := 102243824636789017186140160 }, { target := 284, numerator := 2784040197840951154258739200 }, { target := 286, numerator := 33157312899612041353174712320 }, { target := 294, numerator := 2784056440647216218442301440 }, { target := 301, numerator := 102213659425153897988096000 }, { target := 302, numerator := 2729738291159820834013446144 }, { target := 304, numerator := 99844759231479553372528312320 }, { target := 307, numerator := 99844844821994436256572899328 }, { target := 314, numerator := 2719308475560520821151629312 }, { target := 353, numerator := 13896651444870733431350231040 }, { target := 356, numerator := 49856882206728318132351401984 }, { target := 358, numerator := 13904956745057761787616690176 }, { target := 660, numerator := 1797017335817368942673920 }, { target := 661, numerator := 48931742497946972087910400 }, { target := 663, numerator := 582766404732910466592931840 }, { target := 671, numerator := 48932027978312601336545280 }, { target := 678, numerator := 1796487157995486052352000 }, { target := 679, numerator := 207472946744152939114266624 }, { target := 681, numerator := 7588671222366167171302686720 }, { target := 684, numerator := 7588677727647788346887897088 }, { target := 691, numerator := 206680231712315399945060352 }, { target := 695, numerator := 13894788869463239811580035072 }, { target := 698, numerator := 49850339785090262675916587008 }, { target := 700, numerator := 13903095317369552255127126016 }, { target := 966, numerator := 9065110692757428133429248 }, { target := 968, numerator := 331571637272418719304253440 }, { target := 971, numerator := 331571921507539051584946176 }, { target := 978, numerator := 9030474613094080214728704 }, { target := 982, numerator := 282101414202728654498168832 }, { target := 985, numerator := 1012193711960803274416717824 }, { target := 987, numerator := 282271646508981995322736640 }]

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
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left1.expected,
    Slot18.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 139141992794899444597260288 }, { target := 15, numerator := 6998021953705011440668114944 }, { target := 20, numerator := 6995196644889134965280735232 }, { target := 28, numerator := 140694593996036020201586688 }, { target := 56, numerator := 13283816012703259825274880 }, { target := 57, numerator := 349168949910657543029391360 }, { target := 59, numerator := 4798820088685328629288140800 }, { target := 67, numerator := 347821445196566332996321280 }, { target := 74, numerator := 12981335105949517270220800 }, { target := 110, numerator := 15081217830109491618643968 }, { target := 112, numerator := 565434433136823476598865920 }, { target := 115, numerator := 565651332954728355195781120 }, { target := 122, numerator := 14864594823703909535580160 }, { target := 136, numerator := 494077527822237995674632192 }, { target := 137, numerator := 24849186913895233068566839296 }, { target := 142, numerator := 24839154560850381506491711488 }, { target := 150, numerator := 499590639627975454508449792 }, { target := 152, numerator := 463191042592150917469962240 }, { target := 153, numerator := 12175110660615924985658081280 }, { target := 155, numerator := 167329213078884036492289638400 }, { target := 163, numerator := 12128124755901430923463229440 }, { target := 170, numerator := 452643889091266686117478400 }, { target := 206, numerator := 398111161619850538694737920 }, { target := 208, numerator := 14959139038379662887490682880 }, { target := 211, numerator := 14964840722731788658876088320 }, { target := 218, numerator := 392416800177013867077959680 }, { target := 267, numerator := 139142407122124513008943104 }, { target := 268, numerator := 6998042791921848828876029952 }, { target := 273, numerator := 6995217474692966774583853056 }, { target := 281, numerator := 140695012946487581085794304 }, { target := 283, numerator := 463407508317939338009640960 }, { target := 284, numerator := 12180800524890837504617349120 }, { target := 286, numerator := 167407411999467695666469273600 }, { target := 294, numerator := 12133792661984084521396469760 }, { target := 301, numerator := 452855425755334064052633600 }, { target := 302, numerator := 5381711179445892627694616576 }, { target := 304, numerator := 200486385203948727083739381760 }, { target := 307, numerator := 200564724899079737019643985920 }, { target := 314, numerator := 5303469649896331335161610240 }, { target := 660, numerator := 13067577487886540592906240 }, { target := 661, numerator := 343485057679066894990049280 }, { target := 663, numerator := 4720703245163420868568678400 }, { target := 671, numerator := 342159488110063512914493440 }, { target := 678, numerator := 12770020469343768700518400 }, { target := 679, numerator := 347821445196566332996321280 }, { target := 681, numerator := 12128124755901430923463229440 }, { target := 684, numerator := 12133792661984084521396469760 }, { target := 691, numerator := 342159488110063512914493440 }, { target := 966, numerator := 12981335105949517270220800 }, { target := 968, numerator := 452643889091266686117478400 }, { target := 971, numerator := 452855425755334064052633600 }, { target := 978, numerator := 12770020469343768700518400 }]

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
    Slot18.Left11.expected,
    Slot18.Left18.expected,
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
  [{ target := 14, numerator := 142312477876827857671421952 }, { target := 15, numerator := 6898629491165721990682116096 }, { target := 20, numerator := 6899592224574104846299299840 }, { target := 28, numerator := 141406820206692634296582144 }, { target := 56, numerator := 9064922174047351241441280 }, { target := 57, numerator := 207477848230614938305953792 }, { target := 59, numerator := 2729738291159820834013446144 }, { target := 67, numerator := 207472946744152939114266624 }, { target := 74, numerator := 9065110692757428133429248 }, { target := 136, numerator := 515886102836692683017158656 }, { target := 137, numerator := 25007695292833085063784562688 }, { target := 142, numerator := 25011185224239881169424875520 }, { target := 150, numerator := 512603072332827819908268032 }, { target := 152, numerator := 331564741884212746282598400 }, { target := 153, numerator := 7588850502459522469865717760 }, { target := 155, numerator := 99844759231479553372528312320 }, { target := 163, numerator := 7588671222366167171302686720 }, { target := 170, numerator := 331571637272418719304253440 }, { target := 267, numerator := 142483378823510674938789888 }, { target := 268, numerator := 6906913953135912958740660224 }, { target := 273, numerator := 6907877842676585480543272960 }, { target := 281, numerator := 141576633562494414236942336 }, { target := 283, numerator := 331565026113422104052367360 }, { target := 284, numerator := 7588857007894828982734946304 }, { target := 286, numerator := 99844844821994436256572899328 }, { target := 294, numerator := 7588677727647788346887897088 }, { target := 301, numerator := 331571921507539051584946176 }, { target := 660, numerator := 9030286814678468725309440 }, { target := 661, numerator := 206685114471121298669961216 }, { target := 663, numerator := 2719308475560520821151629312 }, { target := 671, numerator := 206680231712315399945060352 }, { target := 678, numerator := 9030474613094080214728704 }, { target := 679, numerator := 48942497250638694860193792 }, { target := 681, numerator := 2784044620501041596722053120 }, { target := 684, numerator := 2784056440647216218442301440 }, { target := 691, numerator := 48932027978312601336545280 }, { target := 966, numerator := 1796871526149933288652800 }, { target := 968, numerator := 102213225461108554334208000 }, { target := 971, numerator := 102213659425153897988096000 }, { target := 978, numerator := 1796487157995486052352000 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk2.Parent3
