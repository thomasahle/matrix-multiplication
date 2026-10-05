import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk5Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 24; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5.Parent2

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
    Slot0.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 17, numerator := 20641463896623219229065216 }, { target := 18, numerator := 500056109237549601323483136 }, { target := 19, numerator := 378870740554148765849616384 }, { target := 20, numerator := 422151229369649064233140224 }, { target := 21, numerator := 20641463896623219229065216 }, { target := 22, numerator := 422151229369649064233140224 }, { target := 23, numerator := 421485375695564444258009088 }, { target := 24, numerator := 20641463896623219229065216 }, { target := 25, numerator := 500056109237549601323483136 }, { target := 26, numerator := 20641463896623219229065216 }, { target := 37, numerator := 15371302901740695170580480 }, { target := 38, numerator := 372382209006685873325998080 }, { target := 39, numerator := 282137785519046953292267520 }, { target := 40, numerator := 314367936764632281875742720 }, { target := 41, numerator := 15371302901740695170580480 }, { target := 42, numerator := 314367936764632281875742720 }, { target := 43, numerator := 313872088283930969128304640 }, { target := 44, numerator := 15371302901740695170580480 }, { target := 45, numerator := 372382209006685873325998080 }, { target := 46, numerator := 15371302901740695170580480 }, { target := 51, numerator := 16249663067554449180327936 }, { target := 52, numerator := 393661192378496494658912256 }, { target := 53, numerator := 298259944691563922051825664 }, { target := 54, numerator := 332331818865468412268642304 }, { target := 55, numerator := 16249663067554449180327936 }, { target := 56, numerator := 332331818865468412268642304 }, { target := 57, numerator := 331807636185869881649922048 }, { target := 58, numerator := 16249663067554449180327936 }, { target := 59, numerator := 393661192378496494658912256 }, { target := 60, numerator := 16249663067554449180327936 }, { target := 88, numerator := 21080643979530096233938944 }, { target := 89, numerator := 510695600923454911989940224 }, { target := 90, numerator := 386931820140407250229395456 }, { target := 91, numerator := 431133170420067129429590016 }, { target := 92, numerator := 21080643979530096233938944 }, { target := 93, numerator := 431133170420067129429590016 }, { target := 94, numerator := 430453149646533900518817792 }, { target := 95, numerator := 21080643979530096233938944 }, { target := 96, numerator := 510695600923454911989940224 }, { target := 97, numerator := 21080643979530096233938944 }, { target := 108, numerator := 282392793309121914133807104 }, { target := 109, numerator := 6841193154037114758531907584 }, { target := 110, numerator := 5183274173964205456197943296 }, { target := 111, numerator := 5775388095418815921317216256 }, { target := 112, numerator := 282392793309121914133807104 }, { target := 113, numerator := 5775388095418815921317216256 }, { target := 114, numerator := 5766278650473360375699996672 }, { target := 115, numerator := 282392793309121914133807104 }, { target := 116, numerator := 6841193154037114758531907584 }, { target := 117, numerator := 282392793309121914133807104 }, { target := 122, numerator := 510766436420697956668145664 }, { target := 123, numerator := 12373728830707876305089593344 }, { target := 124, numerator := 9375035558818617333683060736 }, { target := 125, numerator := 10445997441636209823471108096 }, { target := 126, numerator := 510766436420697956668145664 }, { target := 127, numerator := 10445997441636209823471108096 }, { target := 128, numerator := 10429521104977477631320522752 }, { target := 129, numerator := 510766436420697956668145664 }, { target := 130, numerator := 12373728830707876305089593344 }, { target := 131, numerator := 510766436420697956668145664 }]

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
    Slot0.Left6.expected,
    Slot0.Left7.expected,
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot0.Left10.expected,
    Slot0.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 153, numerator := 15371302901740695170580480 }, { target := 154, numerator := 372382209006685873325998080 }, { target := 155, numerator := 282137785519046953292267520 }, { target := 156, numerator := 314367936764632281875742720 }, { target := 157, numerator := 15371302901740695170580480 }, { target := 158, numerator := 314367936764632281875742720 }, { target := 159, numerator := 313872088283930969128304640 }, { target := 160, numerator := 15371302901740695170580480 }, { target := 161, numerator := 372382209006685873325998080 }, { target := 162, numerator := 15371302901740695170580480 }, { target := 167, numerator := 282392793309121914133807104 }, { target := 168, numerator := 6841193154037114758531907584 }, { target := 169, numerator := 5183274173964205456197943296 }, { target := 170, numerator := 5775388095418815921317216256 }, { target := 171, numerator := 282392793309121914133807104 }, { target := 172, numerator := 5775388095418815921317216256 }, { target := 173, numerator := 5766278650473360375699996672 }, { target := 174, numerator := 282392793309121914133807104 }, { target := 175, numerator := 6841193154037114758531907584 }, { target := 176, numerator := 282392793309121914133807104 }, { target := 193, numerator := 16688843150461326185201664 }, { target := 194, numerator := 404300684064401805325369344 }, { target := 195, numerator := 306321024277822406431604736 }, { target := 196, numerator := 341313759915886477465092096 }, { target := 197, numerator := 16688843150461326185201664 }, { target := 198, numerator := 341313759915886477465092096 }, { target := 199, numerator := 340775410136839337910730752 }, { target := 200, numerator := 16688843150461326185201664 }, { target := 201, numerator := 404300684064401805325369344 }, { target := 202, numerator := 16688843150461326185201664 }, { target := 248, numerator := 16688843150461326185201664 }, { target := 249, numerator := 404300684064401805325369344 }, { target := 250, numerator := 306321024277822406431604736 }, { target := 251, numerator := 341313759915886477465092096 }, { target := 252, numerator := 16688843150461326185201664 }, { target := 253, numerator := 341313759915886477465092096 }, { target := 254, numerator := 340775410136839337910730752 }, { target := 255, numerator := 16688843150461326185201664 }, { target := 256, numerator := 404300684064401805325369344 }, { target := 257, numerator := 16688843150461326185201664 }, { target := 262, numerator := 16249663067554449180327936 }, { target := 263, numerator := 393661192378496494658912256 }, { target := 264, numerator := 298259944691563922051825664 }, { target := 265, numerator := 332331818865468412268642304 }, { target := 266, numerator := 16249663067554449180327936 }, { target := 267, numerator := 332331818865468412268642304 }, { target := 268, numerator := 331807636185869881649922048 }, { target := 269, numerator := 16249663067554449180327936 }, { target := 270, numerator := 393661192378496494658912256 }, { target := 271, numerator := 16249663067554449180327936 }, { target := 293, numerator := 16249663067554449180327936 }, { target := 294, numerator := 393661192378496494658912256 }, { target := 295, numerator := 298259944691563922051825664 }, { target := 296, numerator := 332331818865468412268642304 }, { target := 297, numerator := 16249663067554449180327936 }, { target := 298, numerator := 332331818865468412268642304 }, { target := 299, numerator := 331807636185869881649922048 }, { target := 300, numerator := 16249663067554449180327936 }, { target := 301, numerator := 393661192378496494658912256 }, { target := 302, numerator := 16249663067554449180327936 }]

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
    Slot0.Left12.expected,
    Slot0.Left13.expected,
    Slot0.Left14.expected,
    Slot0.Left15.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot1.Left4.expected,
    Slot1.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 61, numerator := 10198284766993334824599552 }, { target := 62, numerator := 1788683334819574877138190336 }, { target := 67, numerator := 1788683549262974734011727872 }, { target := 75, numerator := 10198070323593477951062016 }, { target := 132, numerator := 250022465255320466667601920 }, { target := 133, numerator := 43851591434286351826613698560 }, { target := 138, numerator := 43851596691608412833835909120 }, { target := 146, numerator := 250017207933259459445391360 }, { target := 177, numerator := 184885033517750134562095104 }, { target := 178, numerator := 32427097876406486482311708672 }, { target := 183, numerator := 32427101764057800016599711744 }, { target := 191, numerator := 184881145866436600274092032 }, { target := 203, numerator := 206268533835639385000771584 }, { target := 204, numerator := 36177562933286240256956301312 }, { target := 209, numerator := 36177567270576940587914625024 }, { target := 217, numerator := 206264196544939054042447872 }, { target := 272, numerator := 10198284766993334824599552 }, { target := 273, numerator := 1788683334819574877138190336 }, { target := 278, numerator := 1788683549262974734011727872 }, { target := 286, numerator := 10198070323593477951062016 }, { target := 307, numerator := 510766436420697956668145664 }, { target := 308, numerator := 12373728830707876305089593344 }, { target := 309, numerator := 9375035558818617333683060736 }, { target := 310, numerator := 10445997441636209823471108096 }, { target := 311, numerator := 510766436420697956668145664 }, { target := 312, numerator := 10445997441636209823471108096 }, { target := 313, numerator := 10429521104977477631320522752 }, { target := 314, numerator := 510766436420697956668145664 }, { target := 315, numerator := 12373728830707876305089593344 }, { target := 316, numerator := 510766436420697956668145664 }, { target := 317, numerator := 205939556907671858070945792 }, { target := 318, numerator := 36119863470872705583500230656 }, { target := 323, numerator := 36119867801245876886817472512 }, { target := 331, numerator := 205935226534500554753703936 }, { target := 333, numerator := 16249663067554449180327936 }, { target := 334, numerator := 393661192378496494658912256 }, { target := 335, numerator := 298259944691563922051825664 }, { target := 336, numerator := 332331818865468412268642304 }, { target := 337, numerator := 16249663067554449180327936 }, { target := 338, numerator := 332331818865468412268642304 }, { target := 339, numerator := 331807636185869881649922048 }, { target := 340, numerator := 16249663067554449180327936 }, { target := 341, numerator := 393661192378496494658912256 }, { target := 342, numerator := 16249663067554449180327936 }, { target := 382, numerator := 20641463896623219229065216 }, { target := 383, numerator := 500056109237549601323483136 }, { target := 384, numerator := 378870740554148765849616384 }, { target := 385, numerator := 422151229369649064233140224 }, { target := 386, numerator := 20641463896623219229065216 }, { target := 387, numerator := 422151229369649064233140224 }, { target := 388, numerator := 421485375695564444258009088 }, { target := 389, numerator := 20641463896623219229065216 }, { target := 390, numerator := 500056109237549601323483136 }, { target := 391, numerator := 20641463896623219229065216 }, { target := 408, numerator := 21080643979530096233938944 }, { target := 409, numerator := 510695600923454911989940224 }, { target := 410, numerator := 386931820140407250229395456 }, { target := 411, numerator := 431133170420067129429590016 }, { target := 412, numerator := 21080643979530096233938944 }, { target := 413, numerator := 431133170420067129429590016 }, { target := 414, numerator := 430453149646533900518817792 }, { target := 415, numerator := 21080643979530096233938944 }, { target := 416, numerator := 510695600923454911989940224 }, { target := 417, numerator := 21080643979530096233938944 }]

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
    Slot4.Left1.expected,
    Slot4.Left3.expected,
    Slot4.Left11.expected,
    Slot4.Left18.expected,
    Slot5.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 2, numerator := 49100805505637136109404160 }, { target := 3, numerator := 49100805505637136109404160 }, { target := 4, numerator := 49100805505637136109404160 }, { target := 5, numerator := 49100805505637136109404160 }, { target := 8, numerator := 8046676368485731961877299200 }, { target := 9, numerator := 8046676368485731961877299200 }, { target := 10, numerator := 8046676368485731961877299200 }, { target := 11, numerator := 8046676368485731961877299200 }, { target := 17, numerator := 33680769037486874303660032 }, { target := 19, numerator := 1522309487067364464611295232 }, { target := 24, numerator := 33860533483974897308794880 }, { target := 28, numerator := 82843648794847683795956531200 }, { target := 29, numerator := 82843648794847683795956531200 }, { target := 30, numerator := 82843648794847683795956531200 }, { target := 31, numerator := 82843648794847683795956531200 }, { target := 149, numerator := 8046676368485731961877299200 }, { target := 150, numerator := 8046676368485731961877299200 }, { target := 151, numerator := 8046676368485731961877299200 }, { target := 152, numerator := 8046676368485731961877299200 }, { target := 219, numerator := 34181263366261587857899520 }, { target := 220, numerator := 11010515015509806725663293440 }, { target := 222, numerator := 117101457423705219428444536832 }, { target := 230, numerator := 11010548201202395329146650624 }, { target := 237, numerator := 34181263366261587857899520 }, { target := 343, numerator := 209558303115314654299029504 }, { target := 344, numerator := 36754557557421586991517007872 }, { target := 349, numerator := 36754561963887577598886150144 }, { target := 357, numerator := 209553896649324046929887232 }, { target := 359, numerator := 34081512597683003457536000 }, { target := 360, numerator := 10978383162351704176852992000 }, { target := 362, numerator := 116759721653013472679139737600 }, { target := 370, numerator := 10978416251198886393361203200 }, { target := 377, numerator := 34081512597683003457536000 }, { target := 378, numerator := 49100805505637136109404160 }, { target := 379, numerator := 49100805505637136109404160 }, { target := 380, numerator := 49100805505637136109404160 }, { target := 381, numerator := 49100805505637136109404160 }, { target := 392, numerator := 10198284766993334824599552 }, { target := 393, numerator := 1788683334819574877138190336 }, { target := 398, numerator := 1788683549262974734011727872 }, { target := 406, numerator := 10198070323593477951062016 }, { target := 418, numerator := 250022465255320466667601920 }, { target := 419, numerator := 43851591434286351826613698560 }, { target := 424, numerator := 43851596691608412833835909120 }, { target := 432, numerator := 250017207933259459445391360 }, { target := 434, numerator := 33848760804332973190021120 }, { target := 435, numerator := 10903408838316131562962288640 }, { target := 437, numerator := 115962338188066063597428539392 }, { target := 445, numerator := 10903441701190698876528492544 }, { target := 452, numerator := 33848760804332973190021120 }, { target := 453, numerator := 10198284766993334824599552 }, { target := 454, numerator := 1788683334819574877138190336 }, { target := 459, numerator := 1788683549262974734011727872 }, { target := 467, numerator := 10198070323593477951062016 }, { target := 469, numerator := 34081512597683003457536000 }, { target := 470, numerator := 10978383162351704176852992000 }, { target := 472, numerator := 116759721653013472679139737600 }, { target := 480, numerator := 10978416251198886393361203200 }, { target := 487, numerator := 34081512597683003457536000 }, { target := 488, numerator := 8882941359471185954189869056 }, { target := 490, numerator := 347643662450823295736337137664 }, { target := 493, numerator := 347643789954718333216757907456 }, { target := 500, numerator := 8883068863366223434610638848 }]

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
    Slot5.Left1.expected,
    Slot5.Left6.expected,
    Slot5.Left14.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left7.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left2.expected,
    Slot7.Left3.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 8882941359471185954189869056 }, { target := 2, numerator := 34181263366261587857899520 }, { target := 3, numerator := 34081512597683003457536000 }, { target := 4, numerator := 33848760804332973190021120 }, { target := 5, numerator := 34081512597683003457536000 }, { target := 6, numerator := 347643662450823295736337137664 }, { target := 8, numerator := 11010515015509806725663293440 }, { target := 9, numerator := 10978383162351704176852992000 }, { target := 10, numerator := 10903408838316131562962288640 }, { target := 11, numerator := 10978383162351704176852992000 }, { target := 27, numerator := 347643789954718333216757907456 }, { target := 28, numerator := 117101457423705219428444536832 }, { target := 29, numerator := 116759721653013472679139737600 }, { target := 30, numerator := 115962338188066063597428539392 }, { target := 31, numerator := 116759721653013472679139737600 }, { target := 37, numerator := 6680069880726424768846233600 }, { target := 39, numerator := 301927005953590147755383193600 }, { target := 44, numerator := 6715723433151951613722624000 }, { target := 61, numerator := 33680769037486874303660032 }, { target := 62, numerator := 6680069880726424768846233600 }, { target := 67, numerator := 6680069880726424768846233600 }, { target := 75, numerator := 33680769037486874303660032 }, { target := 148, numerator := 8883068863366223434610638848 }, { target := 149, numerator := 11010548201202395329146650624 }, { target := 150, numerator := 10978416251198886393361203200 }, { target := 151, numerator := 10903441701190698876528492544 }, { target := 152, numerator := 10978416251198886393361203200 }, { target := 153, numerator := 6680069880726424768846233600 }, { target := 155, numerator := 301927005953590147755383193600 }, { target := 160, numerator := 6715723433151951613722624000 }, { target := 177, numerator := 1522309487067364464611295232 }, { target := 178, numerator := 301927005953590147755383193600 }, { target := 183, numerator := 301927005953590147755383193600 }, { target := 191, numerator := 1522309487067364464611295232 }, { target := 219, numerator := 49100805505637136109404160 }, { target := 220, numerator := 8046676368485731961877299200 }, { target := 222, numerator := 82843648794847683795956531200 }, { target := 230, numerator := 8046676368485731961877299200 }, { target := 237, numerator := 49100805505637136109404160 }, { target := 359, numerator := 49100805505637136109404160 }, { target := 360, numerator := 8046676368485731961877299200 }, { target := 362, numerator := 82843648794847683795956531200 }, { target := 370, numerator := 8046676368485731961877299200 }, { target := 377, numerator := 49100805505637136109404160 }, { target := 382, numerator := 33680769037486874303660032 }, { target := 384, numerator := 1522309487067364464611295232 }, { target := 389, numerator := 33860533483974897308794880 }, { target := 392, numerator := 33860533483974897308794880 }, { target := 393, numerator := 6715723433151951613722624000 }, { target := 398, numerator := 6715723433151951613722624000 }, { target := 406, numerator := 33860533483974897308794880 }, { target := 434, numerator := 49100805505637136109404160 }, { target := 435, numerator := 8046676368485731961877299200 }, { target := 437, numerator := 82843648794847683795956531200 }, { target := 445, numerator := 8046676368485731961877299200 }, { target := 452, numerator := 49100805505637136109404160 }, { target := 469, numerator := 49100805505637136109404160 }, { target := 470, numerator := 8046676368485731961877299200 }, { target := 472, numerator := 82843648794847683795956531200 }, { target := 480, numerator := 8046676368485731961877299200 }, { target := 487, numerator := 49100805505637136109404160 }]

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
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left6.expected,
    Slot10.Left14.expected,
    Slot11.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 17, numerator := 10198284766993334824599552 }, { target := 18, numerator := 250022465255320466667601920 }, { target := 19, numerator := 184885033517750134562095104 }, { target := 20, numerator := 206268533835639385000771584 }, { target := 21, numerator := 10198284766993334824599552 }, { target := 22, numerator := 205939556907671858070945792 }, { target := 23, numerator := 209558303115314654299029504 }, { target := 24, numerator := 10198284766993334824599552 }, { target := 25, numerator := 250022465255320466667601920 }, { target := 26, numerator := 10198284766993334824599552 }, { target := 37, numerator := 1788683334819574877138190336 }, { target := 38, numerator := 43851591434286351826613698560 }, { target := 39, numerator := 32427097876406486482311708672 }, { target := 40, numerator := 36177562933286240256956301312 }, { target := 41, numerator := 1788683334819574877138190336 }, { target := 42, numerator := 36119863470872705583500230656 }, { target := 43, numerator := 36754557557421586991517007872 }, { target := 44, numerator := 1788683334819574877138190336 }, { target := 45, numerator := 43851591434286351826613698560 }, { target := 46, numerator := 1788683334819574877138190336 }, { target := 61, numerator := 20641463896623219229065216 }, { target := 62, numerator := 15371302901740695170580480 }, { target := 63, numerator := 16249663067554449180327936 }, { target := 64, numerator := 21080643979530096233938944 }, { target := 65, numerator := 282392793309121914133807104 }, { target := 66, numerator := 510766436420697956668145664 }, { target := 67, numerator := 15371302901740695170580480 }, { target := 68, numerator := 282392793309121914133807104 }, { target := 69, numerator := 16688843150461326185201664 }, { target := 70, numerator := 16688843150461326185201664 }, { target := 71, numerator := 16249663067554449180327936 }, { target := 72, numerator := 16249663067554449180327936 }, { target := 73, numerator := 510766436420697956668145664 }, { target := 74, numerator := 16249663067554449180327936 }, { target := 75, numerator := 20641463896623219229065216 }, { target := 76, numerator := 21080643979530096233938944 }, { target := 153, numerator := 1788683549262974734011727872 }, { target := 154, numerator := 43851596691608412833835909120 }, { target := 155, numerator := 32427101764057800016599711744 }, { target := 156, numerator := 36177567270576940587914625024 }, { target := 157, numerator := 1788683549262974734011727872 }, { target := 158, numerator := 36119867801245876886817472512 }, { target := 159, numerator := 36754561963887577598886150144 }, { target := 160, numerator := 1788683549262974734011727872 }, { target := 161, numerator := 43851596691608412833835909120 }, { target := 162, numerator := 1788683549262974734011727872 }, { target := 378, numerator := 34181263366261587857899520 }, { target := 379, numerator := 34081512597683003457536000 }, { target := 380, numerator := 33848760804332973190021120 }, { target := 381, numerator := 34081512597683003457536000 }, { target := 382, numerator := 10198070323593477951062016 }, { target := 383, numerator := 250017207933259459445391360 }, { target := 384, numerator := 184881145866436600274092032 }, { target := 385, numerator := 206264196544939054042447872 }, { target := 386, numerator := 10198070323593477951062016 }, { target := 387, numerator := 205935226534500554753703936 }, { target := 388, numerator := 209553896649324046929887232 }, { target := 389, numerator := 10198070323593477951062016 }, { target := 390, numerator := 250017207933259459445391360 }, { target := 391, numerator := 10198070323593477951062016 }]

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
    Slot11.Left1.expected,
    Slot11.Left2.expected,
    Slot11.Left3.expected,
    Slot11.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 132, numerator := 500056109237549601323483136 }, { target := 133, numerator := 372382209006685873325998080 }, { target := 134, numerator := 393661192378496494658912256 }, { target := 135, numerator := 510695600923454911989940224 }, { target := 136, numerator := 6841193154037114758531907584 }, { target := 137, numerator := 12373728830707876305089593344 }, { target := 138, numerator := 372382209006685873325998080 }, { target := 139, numerator := 6841193154037114758531907584 }, { target := 140, numerator := 404300684064401805325369344 }, { target := 141, numerator := 404300684064401805325369344 }, { target := 142, numerator := 393661192378496494658912256 }, { target := 143, numerator := 393661192378496494658912256 }, { target := 144, numerator := 12373728830707876305089593344 }, { target := 145, numerator := 393661192378496494658912256 }, { target := 146, numerator := 500056109237549601323483136 }, { target := 147, numerator := 510695600923454911989940224 }, { target := 177, numerator := 378870740554148765849616384 }, { target := 178, numerator := 282137785519046953292267520 }, { target := 179, numerator := 298259944691563922051825664 }, { target := 180, numerator := 386931820140407250229395456 }, { target := 181, numerator := 5183274173964205456197943296 }, { target := 182, numerator := 9375035558818617333683060736 }, { target := 183, numerator := 282137785519046953292267520 }, { target := 184, numerator := 5183274173964205456197943296 }, { target := 185, numerator := 306321024277822406431604736 }, { target := 186, numerator := 306321024277822406431604736 }, { target := 187, numerator := 298259944691563922051825664 }, { target := 188, numerator := 298259944691563922051825664 }, { target := 189, numerator := 9375035558818617333683060736 }, { target := 190, numerator := 298259944691563922051825664 }, { target := 191, numerator := 378870740554148765849616384 }, { target := 192, numerator := 386931820140407250229395456 }, { target := 203, numerator := 422151229369649064233140224 }, { target := 204, numerator := 314367936764632281875742720 }, { target := 205, numerator := 332331818865468412268642304 }, { target := 206, numerator := 431133170420067129429590016 }, { target := 207, numerator := 5775388095418815921317216256 }, { target := 208, numerator := 10445997441636209823471108096 }, { target := 209, numerator := 314367936764632281875742720 }, { target := 210, numerator := 5775388095418815921317216256 }, { target := 211, numerator := 341313759915886477465092096 }, { target := 212, numerator := 341313759915886477465092096 }, { target := 213, numerator := 332331818865468412268642304 }, { target := 214, numerator := 332331818865468412268642304 }, { target := 215, numerator := 10445997441636209823471108096 }, { target := 216, numerator := 332331818865468412268642304 }, { target := 217, numerator := 422151229369649064233140224 }, { target := 218, numerator := 431133170420067129429590016 }, { target := 272, numerator := 20641463896623219229065216 }, { target := 273, numerator := 15371302901740695170580480 }, { target := 274, numerator := 16249663067554449180327936 }, { target := 275, numerator := 21080643979530096233938944 }, { target := 276, numerator := 282392793309121914133807104 }, { target := 277, numerator := 510766436420697956668145664 }, { target := 278, numerator := 15371302901740695170580480 }, { target := 279, numerator := 282392793309121914133807104 }, { target := 280, numerator := 16688843150461326185201664 }, { target := 281, numerator := 16688843150461326185201664 }, { target := 282, numerator := 16249663067554449180327936 }, { target := 283, numerator := 16249663067554449180327936 }, { target := 284, numerator := 510766436420697956668145664 }, { target := 285, numerator := 16249663067554449180327936 }, { target := 286, numerator := 20641463896623219229065216 }, { target := 287, numerator := 21080643979530096233938944 }]

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

namespace RouteChunk7

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot11.Left5.expected,
    Slot11.Left6.expected,
    Slot11.Left7.expected,
    Slot11.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 317, numerator := 422151229369649064233140224 }, { target := 318, numerator := 314367936764632281875742720 }, { target := 319, numerator := 332331818865468412268642304 }, { target := 320, numerator := 431133170420067129429590016 }, { target := 321, numerator := 5775388095418815921317216256 }, { target := 322, numerator := 10445997441636209823471108096 }, { target := 323, numerator := 314367936764632281875742720 }, { target := 324, numerator := 5775388095418815921317216256 }, { target := 325, numerator := 341313759915886477465092096 }, { target := 326, numerator := 341313759915886477465092096 }, { target := 327, numerator := 332331818865468412268642304 }, { target := 328, numerator := 332331818865468412268642304 }, { target := 329, numerator := 10445997441636209823471108096 }, { target := 330, numerator := 332331818865468412268642304 }, { target := 331, numerator := 422151229369649064233140224 }, { target := 332, numerator := 431133170420067129429590016 }, { target := 343, numerator := 421485375695564444258009088 }, { target := 344, numerator := 313872088283930969128304640 }, { target := 345, numerator := 331807636185869881649922048 }, { target := 346, numerator := 430453149646533900518817792 }, { target := 347, numerator := 5766278650473360375699996672 }, { target := 348, numerator := 10429521104977477631320522752 }, { target := 349, numerator := 313872088283930969128304640 }, { target := 350, numerator := 5766278650473360375699996672 }, { target := 351, numerator := 340775410136839337910730752 }, { target := 352, numerator := 340775410136839337910730752 }, { target := 353, numerator := 331807636185869881649922048 }, { target := 354, numerator := 331807636185869881649922048 }, { target := 355, numerator := 10429521104977477631320522752 }, { target := 356, numerator := 331807636185869881649922048 }, { target := 357, numerator := 421485375695564444258009088 }, { target := 358, numerator := 430453149646533900518817792 }, { target := 392, numerator := 20641463896623219229065216 }, { target := 393, numerator := 15371302901740695170580480 }, { target := 394, numerator := 16249663067554449180327936 }, { target := 395, numerator := 21080643979530096233938944 }, { target := 396, numerator := 282392793309121914133807104 }, { target := 397, numerator := 510766436420697956668145664 }, { target := 398, numerator := 15371302901740695170580480 }, { target := 399, numerator := 282392793309121914133807104 }, { target := 400, numerator := 16688843150461326185201664 }, { target := 401, numerator := 16688843150461326185201664 }, { target := 402, numerator := 16249663067554449180327936 }, { target := 403, numerator := 16249663067554449180327936 }, { target := 404, numerator := 510766436420697956668145664 }, { target := 405, numerator := 16249663067554449180327936 }, { target := 406, numerator := 20641463896623219229065216 }, { target := 407, numerator := 21080643979530096233938944 }, { target := 418, numerator := 500056109237549601323483136 }, { target := 419, numerator := 372382209006685873325998080 }, { target := 420, numerator := 393661192378496494658912256 }, { target := 421, numerator := 510695600923454911989940224 }, { target := 422, numerator := 6841193154037114758531907584 }, { target := 423, numerator := 12373728830707876305089593344 }, { target := 424, numerator := 372382209006685873325998080 }, { target := 425, numerator := 6841193154037114758531907584 }, { target := 426, numerator := 404300684064401805325369344 }, { target := 427, numerator := 404300684064401805325369344 }, { target := 428, numerator := 393661192378496494658912256 }, { target := 429, numerator := 393661192378496494658912256 }, { target := 430, numerator := 12373728830707876305089593344 }, { target := 431, numerator := 393661192378496494658912256 }, { target := 432, numerator := 500056109237549601323483136 }, { target := 433, numerator := 510695600923454911989940224 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk7

namespace RouteChunk8

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot11.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 453, numerator := 20641463896623219229065216 }, { target := 454, numerator := 15371302901740695170580480 }, { target := 455, numerator := 16249663067554449180327936 }, { target := 456, numerator := 21080643979530096233938944 }, { target := 457, numerator := 282392793309121914133807104 }, { target := 458, numerator := 510766436420697956668145664 }, { target := 459, numerator := 15371302901740695170580480 }, { target := 460, numerator := 282392793309121914133807104 }, { target := 461, numerator := 16688843150461326185201664 }, { target := 462, numerator := 16688843150461326185201664 }, { target := 463, numerator := 16249663067554449180327936 }, { target := 464, numerator := 16249663067554449180327936 }, { target := 465, numerator := 510766436420697956668145664 }, { target := 466, numerator := 16249663067554449180327936 }, { target := 467, numerator := 20641463896623219229065216 }, { target := 468, numerator := 21080643979530096233938944 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk8

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5.Parent2
