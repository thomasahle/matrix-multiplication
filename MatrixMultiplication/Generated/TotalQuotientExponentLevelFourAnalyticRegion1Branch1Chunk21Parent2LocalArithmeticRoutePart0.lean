import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk21Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 88; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21.Parent2

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
    Slot0.Left6.expected,
    Slot0.Left14.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left3.expected,
    Slot1.Left11.expected,
    Slot1.Left18.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left6.expected,
    Slot2.Left14.expected,
    Slot3.Left0.expected,
    Slot3.Left2.expected,
    Slot3.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 587008093279308582601359360 }, { target := 87, numerator := 11740161865586171652027187200 }, { target := 88, numerator := 607972668039283889122836480 }, { target := 89, numerator := 10922543449947134697689579520 }, { target := 90, numerator := 16352368312780739086752153600 }, { target := 91, numerator := 587008093279308582601359360 }, { target := 92, numerator := 16373332887540714393273630720 }, { target := 93, numerator := 16373332887540714393273630720 }, { target := 94, numerator := 11719197290826196345505710080 }, { target := 95, numerator := 607972668039283889122836480 }, { target := 122, numerator := 41724321485442160609198080 }, { target := 123, numerator := 45828353106961061652725760 }, { target := 124, numerator := 41724321485442160609198080 }, { target := 125, numerator := 45828353106961061652725760 }, { target := 161, numerator := 22972538279370584774072598528 }, { target := 162, numerator := 459450765587411695481451970560 }, { target := 163, numerator := 23792986075062391373146619904 }, { target := 164, numerator := 427453301555431238117565136896 }, { target := 165, numerator := 639949280639609147277736673280 }, { target := 166, numerator := 22972538279370584774072598528 }, { target := 167, numerator := 640769728435300953876810694656 }, { target := 168, numerator := 640769728435300953876810694656 }, { target := 169, numerator := 458630317791719888882377949184 }, { target := 170, numerator := 23792986075062391373146619904 }, { target := 197, numerator := 13440295149560608988080373760 }, { target := 198, numerator := 14762291393779685281989918720 }, { target := 199, numerator := 13440295149560608988080373760 }, { target := 200, numerator := 14762291393779685281989918720 }, { target := 215, numerator := 423312931524434996955709440 }, { target := 232, numerator := 22972538279370584774072598528 }, { target := 233, numerator := 459450765587411695481451970560 }, { target := 234, numerator := 23792986075062391373146619904 }, { target := 235, numerator := 427453301555431238117565136896 }, { target := 236, numerator := 639949280639609147277736673280 }, { target := 237, numerator := 22972538279370584774072598528 }, { target := 238, numerator := 640769728435300953876810694656 }, { target := 239, numerator := 640769728435300953876810694656 }, { target := 240, numerator := 458630317791719888882377949184 }, { target := 241, numerator := 23792986075062391373146619904 }, { target := 242, numerator := 142943190940776354566350307328 }, { target := 243, numerator := 157003176934951077966319190016 }, { target := 244, numerator := 142943190940776354566350307328 }, { target := 245, numerator := 157003176934951077966319190016 }, { target := 260, numerator := 78804849582739902596588240896 }, { target := 416, numerator := 13440335658610594854255722496 }, { target := 417, numerator := 14762335887326391069428416512 }, { target := 418, numerator := 13440335658610594854255722496 }, { target := 419, numerator := 14762335887326391069428416512 }, { target := 420, numerator := 78804854305106385466233454592 }, { target := 498, numerator := 41724321485442160609198080 }, { target := 499, numerator := 45828353106961061652725760 }, { target := 500, numerator := 41724321485442160609198080 }, { target := 501, numerator := 45828353106961061652725760 }, { target := 502, numerator := 423308209157952127310495744 }]

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
    Slot3.Left12.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left3.expected,
    Slot4.Left11.expected,
    Slot4.Left18.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot5.Left4.expected,
    Slot5.Left5.expected,
    Slot5.Left6.expected,
    Slot5.Left7.expected,
    Slot5.Left8.expected,
    Slot5.Left9.expected,
    Slot5.Left10.expected,
    Slot5.Left11.expected,
    Slot5.Left12.expected,
    Slot5.Left13.expected,
    Slot5.Left14.expected,
    Slot5.Left15.expected,
    Slot6.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 46281992873124300700438757376 }, { target := 36, numerator := 52710047438836009131055251456 }, { target := 37, numerator := 41139549220554933955945562112 }, { target := 38, numerator := 551527081738064583346895192064 }, { target := 39, numerator := 48853214699408984072685355008 }, { target := 40, numerator := 41139549220554933955945562112 }, { target := 41, numerator := 48853214699408984072685355008 }, { target := 42, numerator := 47567603786266642386562056192 }, { target := 43, numerator := 1797284056572993677200371744768 }, { target := 44, numerator := 47567603786266642386562056192 }, { target := 45, numerator := 551527081738064583346895192064 }, { target := 46, numerator := 1797284056572993677200371744768 }, { target := 47, numerator := 46281992873124300700438757376 }, { target := 48, numerator := 47567603786266642386562056192 }, { target := 49, numerator := 47567603786266642386562056192 }, { target := 50, numerator := 52710047438836009131055251456 }, { target := 122, numerator := 1077719589254578952088846336 }, { target := 124, numerator := 1077719589254578952088846336 }, { target := 197, numerator := 127379536238520531532734529536 }, { target := 199, numerator := 127379536238520531532734529536 }, { target := 215, numerator := 1856910058928070412348686336 }, { target := 242, numerator := 1208806407494560091422479876096 }, { target := 244, numerator := 1208806407494560091422479876096 }, { target := 260, numerator := 1392682544196052809261514752 }, { target := 265, numerator := 1470053796651389076442710016 }, { target := 355, numerator := 1895595685155738545939283968 }, { target := 400, numerator := 25377770805350295635432046592 }, { target := 405, numerator := 44372413283135349228415483904 }, { target := 406, numerator := 587008093279308582601359360 }, { target := 407, numerator := 11740161865586171652027187200 }, { target := 408, numerator := 607972668039283889122836480 }, { target := 409, numerator := 10922543449947134697689579520 }, { target := 410, numerator := 16352368312780739086752153600 }, { target := 411, numerator := 587008093279308582601359360 }, { target := 412, numerator := 16373332887540714393273630720 }, { target := 413, numerator := 16373332887540714393273630720 }, { target := 414, numerator := 11719197290826196345505710080 }, { target := 415, numerator := 607972668039283889122836480 }, { target := 416, numerator := 127379623602300464621170982912 }, { target := 418, numerator := 127379623602300464621170982912 }, { target := 420, numerator := 1353996917968384675670917120 }, { target := 425, numerator := 25377770805350295635432046592 }, { target := 426, numerator := 1431368170423720942852112384 }, { target := 471, numerator := 1470053796651389076442710016 }, { target := 476, numerator := 1470053796651389076442710016 }, { target := 491, numerator := 1431368170423720942852112384 }, { target := 496, numerator := 44372413283135349228415483904 }, { target := 497, numerator := 1431368170423720942852112384 }, { target := 498, numerator := 1077719589254578952088846336 }, { target := 500, numerator := 1077719589254578952088846336 }, { target := 502, numerator := 1856910058928070412348686336 }, { target := 503, numerator := 1895595685155738545939283968 }]

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
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left2.expected,
    Slot8.Left3.expected,
    Slot8.Left4.expected,
    Slot8.Left5.expected,
    Slot8.Left6.expected,
    Slot8.Left7.expected,
    Slot8.Left8.expected,
    Slot8.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 99678503269155163676059107328 }, { target := 89, numerator := 364077558779599062257840947200 }, { target := 91, numerator := 99678469685840045447011368960 }, { target := 122, numerator := 6731298161180888038398492672 }, { target := 124, numerator := 6731299766047622451129483264 }, { target := 145, numerator := 166474952034292431426869526528 }, { target := 146, numerator := 189596473150166380236156960768 }, { target := 147, numerator := 147977735141593272379439579136 }, { target := 148, numerator := 1983826511741984807836861857792 }, { target := 149, numerator := 175723560480642010950584500224 }, { target := 150, numerator := 147977735141593272379439579136 }, { target := 151, numerator := 175723560480642010950584500224 }, { target := 152, numerator := 171099256257467221188727013376 }, { target := 153, numerator := 6464777303998356087076766613504 }, { target := 154, numerator := 171099256257467221188727013376 }, { target := 155, numerator := 1983826511741984807836861857792 }, { target := 156, numerator := 6464777303998356087076766613504 }, { target := 157, numerator := 166474952034292431426869526528 }, { target := 158, numerator := 171099256257467221188727013376 }, { target := 159, numerator := 171099256257467221188727013376 }, { target := 160, numerator := 189596473150166380236156960768 }, { target := 161, numerator := 3887998318041486070208075399168 }, { target := 164, numerator := 14200985064447275803841082163200 }, { target := 166, numerator := 3887997008111376652761311477760 }, { target := 197, numerator := 100969472417713320575977390080 }, { target := 199, numerator := 100969496490714336766942248960 }, { target := 211, numerator := 177257518244430051677826973696 }, { target := 213, numerator := 177257560505920724546409725952 }, { target := 216, numerator := 46282008313049090395333459968 }, { target := 217, numerator := 52710065023194797394685329408 }, { target := 218, numerator := 41139562944932524795851964416 }, { target := 219, numerator := 551527265730501660544390397952 }, { target := 220, numerator := 48853230997107373195074207744 }, { target := 221, numerator := 41139562944932524795851964416 }, { target := 222, numerator := 48853230997107373195074207744 }, { target := 223, numerator := 47567619655078231795203833856 }, { target := 224, numerator := 1797284656156739677018782695424 }, { target := 225, numerator := 47567619655078231795203833856 }, { target := 226, numerator := 551527265730501660544390397952 }, { target := 227, numerator := 1797284656156739677018782695424 }, { target := 228, numerator := 46282008313049090395333459968 }, { target := 229, numerator := 47567619655078231795203833856 }, { target := 230, numerator := 47567619655078231795203833856 }, { target := 231, numerator := 52710065023194797394685329408 }, { target := 232, numerator := 3887996891937293595398044123136 }, { target := 235, numerator := 14200979855575594017191519846400 }, { target := 237, numerator := 3887995582007664655736525291520 }, { target := 242, numerator := 6731298161180888038398492672 }, { target := 244, numerator := 6731299766047622451129483264 }, { target := 256, numerator := 112188302686348133973308211200 }, { target := 258, numerator := 112188329434127040852158054400 }, { target := 261, numerator := 6731298161180888038398492672 }, { target := 263, numerator := 6731299766047622451129483264 }, { target := 337, numerator := 177257518244430051677826973696 }, { target := 339, numerator := 177257560505920724546409725952 }, { target := 351, numerator := 176135635217566570338093891584 }, { target := 353, numerator := 176135677211579454137888145408 }, { target := 382, numerator := 112188302686348133973308211200 }, { target := 384, numerator := 112188329434127040852158054400 }, { target := 396, numerator := 2718322574090215286173257957376 }, { target := 398, numerator := 2718323222188898199847789658112 }, { target := 406, numerator := 99678978637219321946069532672 }, { target := 409, numerator := 364079295070159657807695052800 }, { target := 411, numerator := 99678945053744044455273431040 }]

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
    Slot8.Left10.expected,
    Slot8.Left11.expected,
    Slot8.Left12.expected,
    Slot8.Left13.expected,
    Slot8.Left14.expected,
    Slot8.Left15.expected,
    Slot8.Left16.expected,
    Slot8.Left17.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 6731298161180888038398492672 }, { target := 17, numerator := 100969472417713320575977390080 }, { target := 18, numerator := 177257518244430051677826973696 }, { target := 19, numerator := 6731298161180888038398492672 }, { target := 20, numerator := 112188302686348133973308211200 }, { target := 21, numerator := 6731298161180888038398492672 }, { target := 22, numerator := 177257518244430051677826973696 }, { target := 23, numerator := 176135635217566570338093891584 }, { target := 24, numerator := 112188302686348133973308211200 }, { target := 25, numerator := 2718322574090215286173257957376 }, { target := 26, numerator := 173891869163839607658627727360 }, { target := 27, numerator := 100969472417713320575977390080 }, { target := 28, numerator := 177257518244430051677826973696 }, { target := 29, numerator := 6731298161180888038398492672 }, { target := 30, numerator := 173891869163839607658627727360 }, { target := 31, numerator := 6731298161180888038398492672 }, { target := 32, numerator := 177257518244430051677826973696 }, { target := 33, numerator := 177257518244430051677826973696 }, { target := 34, numerator := 6731298161180888038398492672 }, { target := 35, numerator := 98101866134845152299812126720 }, { target := 37, numerator := 3826500980849265728148545208320 }, { target := 40, numerator := 3826499577302081570163277168640 }, { target := 47, numerator := 98102333983906538294901473280 }, { target := 126, numerator := 6731299766047622451129483264 }, { target := 127, numerator := 100969496490714336766942248960 }, { target := 128, numerator := 177257560505920724546409725952 }, { target := 129, numerator := 6731299766047622451129483264 }, { target := 130, numerator := 112188329434127040852158054400 }, { target := 131, numerator := 6731299766047622451129483264 }, { target := 132, numerator := 177257560505920724546409725952 }, { target := 133, numerator := 176135677211579454137888145408 }, { target := 134, numerator := 112188329434127040852158054400 }, { target := 135, numerator := 2718323222188898199847789658112 }, { target := 136, numerator := 173891910622896913320844984320 }, { target := 137, numerator := 100969496490714336766942248960 }, { target := 138, numerator := 177257560505920724546409725952 }, { target := 139, numerator := 6731299766047622451129483264 }, { target := 140, numerator := 173891910622896913320844984320 }, { target := 141, numerator := 6731299766047622451129483264 }, { target := 142, numerator := 177257560505920724546409725952 }, { target := 143, numerator := 177257560505920724546409725952 }, { target := 144, numerator := 6731299766047622451129483264 }, { target := 145, numerator := 358318862770782908373270528000 }, { target := 147, numerator := 13976364914043013093411258368000 }, { target := 150, numerator := 13976359787561217310416961536000 }, { target := 157, numerator := 358320571598048169371369472000 }, { target := 401, numerator := 173891869163839607658627727360 }, { target := 403, numerator := 173891910622896913320844984320 }, { target := 416, numerator := 100969472417713320575977390080 }, { target := 418, numerator := 100969496490714336766942248960 }, { target := 421, numerator := 177257518244430051677826973696 }, { target := 423, numerator := 177257560505920724546409725952 }, { target := 453, numerator := 6731298161180888038398492672 }, { target := 455, numerator := 6731299766047622451129483264 }, { target := 467, numerator := 173891869163839607658627727360 }, { target := 469, numerator := 173891910622896913320844984320 }, { target := 472, numerator := 6731298161180888038398492672 }, { target := 474, numerator := 6731299766047622451129483264 }, { target := 487, numerator := 177257518244430051677826973696 }, { target := 489, numerator := 177257560505920724546409725952 }, { target := 492, numerator := 177257518244430051677826973696 }, { target := 494, numerator := 177257560505920724546409725952 }, { target := 498, numerator := 6731298161180888038398492672 }, { target := 500, numerator := 6731299766047622451129483264 }]

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
    Slot10.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left2.expected,
    Slot11.Left3.expected,
    Slot11.Left4.expected,
    Slot11.Left5.expected,
    Slot11.Left6.expected,
    Slot11.Left7.expected,
    Slot11.Left8.expected,
    Slot11.Left9.expected,
    Slot11.Left10.expected,
    Slot11.Left11.expected,
    Slot11.Left12.expected,
    Slot11.Left13.expected,
    Slot11.Left14.expected,
    Slot11.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 86, numerator := 47028476629142434582703898624 }, { target := 89, numerator := 169160031905813277095044841472 }, { target := 91, numerator := 47028492318098269272677548032 }, { target := 112, numerator := 53560209494301106052523884544 }, { target := 115, numerator := 192654480781620676691578847232 }, { target := 117, numerator := 53560227362278584449438318592 }, { target := 161, numerator := 41803090337015497406847909888 }, { target := 164, numerator := 150364472805167357417817636864 }, { target := 166, numerator := 41803104282754017131268931584 }, { target := 187, numerator := 560422679830614012110554791936 }, { target := 190, numerator := 2015823713544274885382617694208 }, { target := 192, numerator := 560422866790671042166074114048 }, { target := 201, numerator := 49641169775205903170631892992 }, { target := 204, numerator := 178557811456136236933658443776 }, { target := 206, numerator := 49641186335770395343381856256 }, { target := 216, numerator := 98101833082724825044510310400 }, { target := 218, numerator := 3826499691638613225916229222400 }, { target := 221, numerator := 3826498288091901945891835084800 }, { target := 228, numerator := 98102300931628585052641689600 }, { target := 232, numerator := 41803090337015497406847909888 }, { target := 235, numerator := 150364472805167357417817636864 }, { target := 237, numerator := 41803104282754017131268931584 }, { target := 246, numerator := 49641169775205903170631892992 }, { target := 249, numerator := 178557811456136236933658443776 }, { target := 251, numerator := 49641186335770395343381856256 }, { target := 301, numerator := 48334823202174168876667895808 }, { target := 304, numerator := 173858921680974757014351642624 }, { target := 306, numerator := 48334839326934332308029702144 }, { target := 327, numerator := 1826272509098364542961668063232 }, { target := 330, numerator := 6569047905675748927190908010496 }, { target := 332, numerator := 1826273118352816123422311448576 }, { target := 341, numerator := 48334823202174168876667895808 }, { target := 344, numerator := 173858921680974757014351642624 }, { target := 346, numerator := 48334839326934332308029702144 }, { target := 372, numerator := 560422679830614012110554791936 }, { target := 375, numerator := 2015823713544274885382617694208 }, { target := 377, numerator := 560422866790671042166074114048 }, { target := 386, numerator := 1826272509098364542961668063232 }, { target := 389, numerator := 6569047905675748927190908010496 }, { target := 391, numerator := 1826273118352816123422311448576 }, { target := 406, numerator := 47028476629142434582703898624 }, { target := 409, numerator := 169160031905813277095044841472 }, { target := 411, numerator := 47028492318098269272677548032 }, { target := 443, numerator := 48334823202174168876667895808 }, { target := 446, numerator := 173858921680974757014351642624 }, { target := 448, numerator := 48334839326934332308029702144 }, { target := 457, numerator := 48334823202174168876667895808 }, { target := 460, numerator := 173858921680974757014351642624 }, { target := 462, numerator := 48334839326934332308029702144 }, { target := 477, numerator := 53560209494301106052523884544 }, { target := 480, numerator := 192654480781620676691578847232 }, { target := 482, numerator := 53560227362278584449438318592 }]

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
    Slot12.Left0.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left2.expected,
    Slot14.Left3.expected,
    Slot14.Left4.expected,
    Slot14.Left5.expected,
    Slot14.Left6.expected,
    Slot14.Left7.expected,
    Slot14.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1856910058928070412348686336 }, { target := 1, numerator := 1392682544196052809261514752 }, { target := 2, numerator := 1470053796651389076442710016 }, { target := 3, numerator := 1895595685155738545939283968 }, { target := 4, numerator := 25377770805350295635432046592 }, { target := 5, numerator := 44372413283135349228415483904 }, { target := 6, numerator := 1353996917968384675670917120 }, { target := 7, numerator := 25377770805350295635432046592 }, { target := 8, numerator := 1431368170423720942852112384 }, { target := 9, numerator := 1470053796651389076442710016 }, { target := 10, numerator := 1470053796651389076442710016 }, { target := 11, numerator := 1431368170423720942852112384 }, { target := 12, numerator := 44372413283135349228415483904 }, { target := 13, numerator := 1431368170423720942852112384 }, { target := 14, numerator := 1856910058928070412348686336 }, { target := 15, numerator := 1895595685155738545939283968 }, { target := 16, numerator := 1106847145720918923766923264 }, { target := 17, numerator := 130822226407129194547132760064 }, { target := 19, numerator := 1241476850940359012812276629504 }, { target := 27, numerator := 130822316132092369070391820288 }, { target := 34, numerator := 1106847145720918923766923264 }, { target := 35, numerator := 593755312742289141022064640 }, { target := 37, numerator := 23236590443501281150786076672 }, { target := 40, numerator := 23236590443501281150786076672 }, { target := 47, numerator := 593755312742289141022064640 }, { target := 70, numerator := 11875106254845782820441292800 }, { target := 72, numerator := 464731808870025623015721533440 }, { target := 75, numerator := 464731808870025623015721533440 }, { target := 82, numerator := 11875106254845782820441292800 }, { target := 96, numerator := 614960859625942324629995520 }, { target := 98, numerator := 24066468673626326906171293696 }, { target := 101, numerator := 24066468673626326906171293696 }, { target := 108, numerator := 614960859625942324629995520 }, { target := 126, numerator := 1106847145720918923766923264 }, { target := 127, numerator := 130822226407129194547132760064 }, { target := 129, numerator := 1241476850940359012812276629504 }, { target := 137, numerator := 130822316132092369070391820288 }, { target := 144, numerator := 1106847145720918923766923264 }, { target := 145, numerator := 11048089926383308659731988480 }, { target := 147, numerator := 432366557895148838555698069504 }, { target := 150, numerator := 432366557895148838555698069504 }, { target := 157, numerator := 11048089926383308659731988480 }, { target := 171, numerator := 16540326569249483214186086400 }, { target := 173, numerator := 647305019497535689200469278720 }, { target := 176, numerator := 647305019497535689200469278720 }, { target := 183, numerator := 16540326569249483214186086400 }, { target := 216, numerator := 593755312742289141022064640 }, { target := 218, numerator := 23236590443501281150786076672 }, { target := 221, numerator := 23236590443501281150786076672 }, { target := 228, numerator := 593755312742289141022064640 }, { target := 285, numerator := 16561532116133136397794017280 }, { target := 287, numerator := 648134897727660734955854495744 }, { target := 290, numerator := 648134897727660734955854495744 }, { target := 297, numerator := 16561532116133136397794017280 }, { target := 311, numerator := 16561532116133136397794017280 }, { target := 313, numerator := 648134897727660734955854495744 }, { target := 316, numerator := 648134897727660734955854495744 }, { target := 323, numerator := 16561532116133136397794017280 }, { target := 356, numerator := 11853900707962129636833361920 }, { target := 358, numerator := 463901930639900577260336316416 }, { target := 361, numerator := 463901930639900577260336316416 }, { target := 368, numerator := 11853900707962129636833361920 }]

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
    Slot14.Left9.expected,
    Slot15.Left0.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left2.expected,
    Slot16.Left3.expected,
    Slot17.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 423312931524434996955709440 }, { target := 1, numerator := 78804849582739902596588240896 }, { target := 6, numerator := 78804854305106385466233454592 }, { target := 14, numerator := 423308209157952127310495744 }, { target := 16, numerator := 41724321485442160609198080 }, { target := 17, numerator := 13440295149560608988080373760 }, { target := 19, numerator := 142943190940776354566350307328 }, { target := 27, numerator := 13440335658610594854255722496 }, { target := 34, numerator := 41724321485442160609198080 }, { target := 51, numerator := 45828353106961061652725760 }, { target := 52, numerator := 14762291393779685281989918720 }, { target := 54, numerator := 157003176934951077966319190016 }, { target := 62, numerator := 14762335887326391069428416512 }, { target := 69, numerator := 45828353106961061652725760 }, { target := 126, numerator := 41724321485442160609198080 }, { target := 127, numerator := 13440295149560608988080373760 }, { target := 129, numerator := 142943190940776354566350307328 }, { target := 137, numerator := 13440335658610594854255722496 }, { target := 144, numerator := 41724321485442160609198080 }, { target := 266, numerator := 45828353106961061652725760 }, { target := 267, numerator := 14762291393779685281989918720 }, { target := 269, numerator := 157003176934951077966319190016 }, { target := 277, numerator := 14762335887326391069428416512 }, { target := 284, numerator := 45828353106961061652725760 }, { target := 427, numerator := 614960859625942324629995520 }, { target := 429, numerator := 24066468673626326906171293696 }, { target := 432, numerator := 24066468673626326906171293696 }, { target := 439, numerator := 614960859625942324629995520 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21.Parent2
