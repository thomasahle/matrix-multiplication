import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 2,
parent chunk 12, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1322725614616125821163713224245248)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5456277309, 8505, 8505, 17955, 408460507, 42826347473,
    461625220875, 21413190071, 408460507, 672021141, 202635, 24161327547,
    3188835, 95985, 193290691395, 95985, 95985, 8222715,
    95985, 3188835, 8222715, 5376098109, 95985, 95985,
    202635, 157974433757, 544755873367, 39493607027, 679831701, 7695,
    24168405867, 121095, 3645, 193347317955, 3645, 3645,
    312255, 3645, 121095, 312255, 5438582589, 3645,
    3645, 7695, 152989095889, 526826037019, 38247273029, 5195777,
    5195775, 60846014997, 7102184122661, 818058787, 285109565066135, 26968971,
    62927599, 818058787, 818058787, 26968971, 10095384811, 404534565,
    7102185225509, 818058787, 62927599, 404534565
  ]
def negativeCoefficients : Array ℕ := #[
    6290659444644478121184067584, 160654907747225330169937920, 160654907747225330169937920, 169580180399848959623823360, 1883691609211662205953507328, 197501667861547195396461166592,
    2128870576862692261333303296000, 197501818520717731400796602368, 1883691609211662205953507328, 198345632002388495673323421696, 1913833464512581115754577920, 7131165211849241406986866655232,
    15058847523401625095016284160, 1813105387432971583346442240, 7131167831987876148544159088640, 1813105387432971583346442240, 1813105387432971583346442240, 77661347428378949486672609280,
    1813105387432971583346442240, 15058847523401625095016284160, 77661347428378949486672609280, 198343011863753754116030988288, 1813105387432971583346442240, 1813105387432971583346442240,
    1913833464512581115754577920, 182132121856535117938747768832, 628060761165698638379002888192, 182132115343681538414669201408, 6270340700770816927526289408, 145354440342727679677562880,
    222914198849044703865036865536, 1143709938486199374305034240, 137704206640478854431375360, 222914280728377039538702254080, 137704206640478854431375360, 137704206640478854431375360,
    5898330184433844264810577920, 137704206640478854431375360, 1143709938486199374305034240, 5898330184433844264810577920, 6270258821438481253860900864, 137704206640478854431375360,
    137704206640478854431375360, 145354440342727679677562880, 176384418620787067257213681664, 607389067266007944019044204544, 176384414270814230375580041216, 49072726314529993198963523584,
    49072707425064061720382668800, 274026090467468811291328512, 31985393768332732656156409856, 1886315135129784298162356224, 321004832747902442437596938240, 994979411936589519909814272,
    72550582120376319160090624, 1886315135129784298162356224, 1886315135129784298162356224, 994979411936589519909814272, 23278372491766458976223363072, 1865586397381105349830901760,
    31985398735118574502453182464, 1886315135129784298162356224, 72550582120376319160090624, 1865586397381105349830901760
  ]
def negativeScales : Array ℕ := #[
    32, 13, 13, 14, 28, 35,
    38, 34, 28, 29, 17, 34,
    21, 16, 37, 16, 16, 22,
    16, 21, 22, 32, 16, 16,
    17, 37, 38, 35, 29, 12,
    34, 16, 11, 37, 11, 11,
    18, 11, 16, 18, 32, 11,
    11, 12, 37, 38, 35, 22,
    22, 35, 42, 29, 48, 24,
    25, 29, 29, 24, 33, 28,
    42, 29, 25, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32345269823522892, 13054095520550748, 13054095520550748, 14132098032552021, 28605621353732004, 35317779588341847,
    38747931091696951, 34317780688864985, 28605621353732004, 29323931378317380, 17628523858683737, 34491980674764297,
    21604598019432458, 16550521346671598, 37491981204840408, 16550521346671598, 16550521346671598, 22971183409984650,
    16550521346671598, 21604598019432458, 22971183409984650, 32323912320242120, 16550521346671598, 16550521346671598,
    17628523858683737, 37200900138388260, 38986818908977098, 35200900086798998, 29340602396367056, 12909705616407956,
    34492403265849062, 16885779775347245, 11831703100430750, 37492403795769927, 11831703100430750, 11831703100430750,
    18252365147687022, 11831703100430750, 16885779775347245, 18252365147687022, 32340583557250712, 11831703100430750,
    11831703100430750, 12909705616407956, 37154637874015734, 38938535701179469, 35154637838436149, 22308908081730818,
    22308907526397008, 35824443729180888, 42691399901122982, 29607629280348623, 48018509769108966, 24684797140914520,
    25907189567166222, 29607629280348623, 29607629280348623, 24684797140914520, 33232976852543554, 28591687736477113,
    42691400125148886, 29607629280348623, 25907189567166222, 28591687736477113
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
def positiveArgument (term : PositiveTerm) : ℕ :=
  positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ :=
  positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ :=
  positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ :=
  negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ :=
  negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ :=
  negativeScales[term.val]?.getD 0
def positiveLogLowerNumerator (term : PositiveTerm) : ℕ :=
  positiveLogLowerNumerators[term.val]?.getD 0
def negativeLogUpperNumerator (term : NegativeTerm) : ℕ :=
  negativeLogUpperNumerators[term.val]?.getD 0

noncomputable def positiveLogLower (term : PositiveTerm) : ℝ :=
  (positiveLogLowerNumerator term : ℝ) / logBoundDenominator
noncomputable def negativeLogUpper (term : NegativeTerm) : ℝ :=
  (negativeLogUpperNumerator term : ℝ) / logBoundDenominator
def positiveLogLowerRat (term : PositiveTerm) : ℚ :=
  positiveLogLowerNumerator term / logBoundDenominator
def negativeLogUpperRat (term : NegativeTerm) : ℚ :=
  negativeLogUpperNumerator term / logBoundDenominator

theorem positiveScales_valid :
    ∀ term, 2 ^ positiveScale term ≤ positiveArgument term := by decide

theorem negativeScales_valid :
    ∀ term, 2 ^ negativeScale term ≤ negativeArgument term := by decide

noncomputable def positiveExact : ℝ :=
  Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ :=
  Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 8893741999 / 1000000000000

theorem positiveLogLowerRat_le_fastRat :
    ∀ term, positiveLogLowerRat term ≤
      MatrixMultiplication.RationalDyadicLog.numeratorLogLower
        (positiveArgument term) (positiveScale term) 8 := by decide +kernel

theorem negativeFastRat_le_logUpperRat :
    ∀ term, MatrixMultiplication.RationalDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpperRat term := by decide +kernel

theorem positiveLogLower_le_fast (term : PositiveTerm) :
    positiveLogLower term ≤ MatrixMultiplication.FastDyadicLog.numeratorLogLower
      (positiveArgument term) (positiveScale term) 8 := by
  simpa [positiveLogLower, positiveLogLowerRat] using
    MatrixMultiplication.RationalDyadicLog.cast_le_fastLower
      (positiveLogLowerRat_le_fastRat term)

theorem negativeFast_le_logUpper (term : NegativeTerm) :
    MatrixMultiplication.FastDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpper term := by
  simpa [negativeLogUpper, negativeLogUpperRat] using
    MatrixMultiplication.RationalDyadicLog.fastUpper_le_cast
      (negativeFastRat_le_logUpperRat term)

theorem positiveFloor_le_rationalLower : positiveFloor ≤ positiveRationalLower := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem positiveFloor_le_exact : positiveFloor ≤ positiveExact :=
  positiveFloor_le_rationalLower.trans
    (weightedLowerWithScale_le_natLogSum 8 bits
      positiveArgument positiveCoefficient positiveScale positiveLogLower
      positiveScales_valid positiveLogLower_le_fast)

theorem negativeExact_le_ceiling : negativeExact ≤ negativeCeiling :=
  (natLogSum_le_weightedUpperWithScale 8 bits
    negativeArgument negativeCoefficient negativeScale negativeLogUpper
    negativeScales_valid negativeFast_le_logUpper).trans
      negativeRationalUpper_le_ceiling

/-- Sign-separated exact form used by the directed arithmetic checker. -/
def signedForm : Form :=
  SignedDyadicLogCertificate.Form.ofSignedFamilies constantNumerator
    positiveArgument positiveCoefficient negativeArgument negativeCoefficient

/-- Exact source-order form before this shard's bounded power-of-two normalization. -/
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 6290659444644478121184067584, coefficient := (-6290659444644478121184067584) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 169580180399848959623823360, coefficient := (-169580180399848959623823360) }, { argument := 1883691609211662205953507328, coefficient := (-1883691609211662205953507328) }, { argument := 197501667861547195396461166592, coefficient := (-197501667861547195396461166592) }, { argument := 2128870576862692261333303296000, coefficient := (-2128870576862692261333303296000) }, { argument := 197501818520717731400796602368, coefficient := (-197501818520717731400796602368) }, { argument := 1883691609211662205953507328, coefficient := (-1883691609211662205953507328) }, { argument := 198345632002388495673323421696, coefficient := (-198345632002388495673323421696) }, { argument := 1913833464512581115754577920, coefficient := (-1913833464512581115754577920) }, { argument := 7131165211849241406986866655232, coefficient := (-7131165211849241406986866655232) }, { argument := 15058847523401625095016284160, coefficient := (-15058847523401625095016284160) }, { argument := 1813105387432971583346442240, coefficient := (-1813105387432971583346442240) }, { argument := 7131167831987876148544159088640, coefficient := (-7131167831987876148544159088640) }, { argument := 1813105387432971583346442240, coefficient := (-1813105387432971583346442240) }, { argument := 1813105387432971583346442240, coefficient := (-1813105387432971583346442240) }, { argument := 77661347428378949486672609280, coefficient := (-77661347428378949486672609280) }, { argument := 1813105387432971583346442240, coefficient := (-1813105387432971583346442240) }, { argument := 15058847523401625095016284160, coefficient := (-15058847523401625095016284160) }, { argument := 77661347428378949486672609280, coefficient := (-77661347428378949486672609280) }, { argument := 198343011863753754116030988288, coefficient := (-198343011863753754116030988288) }, { argument := 1813105387432971583346442240, coefficient := (-1813105387432971583346442240) }, { argument := 1813105387432971583346442240, coefficient := (-1813105387432971583346442240) }, { argument := 1913833464512581115754577920, coefficient := (-1913833464512581115754577920) }, { argument := 182132121856535117938747768832, coefficient := (-182132121856535117938747768832) }, { argument := 628060761165698638379002888192, coefficient := (-628060761165698638379002888192) }, { argument := 182132115343681538414669201408, coefficient := (-182132115343681538414669201408) }, { argument := 6270340700770816927526289408, coefficient := (-6270340700770816927526289408) }, { argument := 145354440342727679677562880, coefficient := (-145354440342727679677562880) }, { argument := 222914198849044703865036865536, coefficient := (-222914198849044703865036865536) }, { argument := 1143709938486199374305034240, coefficient := (-1143709938486199374305034240) }, { argument := 137704206640478854431375360, coefficient := (-137704206640478854431375360) }, { argument := 222914280728377039538702254080, coefficient := (-222914280728377039538702254080) }, { argument := 137704206640478854431375360, coefficient := (-137704206640478854431375360) }, { argument := 137704206640478854431375360, coefficient := (-137704206640478854431375360) }, { argument := 5898330184433844264810577920, coefficient := (-5898330184433844264810577920) }, { argument := 137704206640478854431375360, coefficient := (-137704206640478854431375360) }, { argument := 1143709938486199374305034240, coefficient := (-1143709938486199374305034240) }, { argument := 5898330184433844264810577920, coefficient := (-5898330184433844264810577920) }, { argument := 6270258821438481253860900864, coefficient := (-6270258821438481253860900864) }, { argument := 137704206640478854431375360, coefficient := (-137704206640478854431375360) }, { argument := 137704206640478854431375360, coefficient := (-137704206640478854431375360) }, { argument := 145354440342727679677562880, coefficient := (-145354440342727679677562880) }, { argument := 176384418620787067257213681664, coefficient := (-176384418620787067257213681664) }, { argument := 607389067266007944019044204544, coefficient := (-607389067266007944019044204544) }, { argument := 176384414270814230375580041216, coefficient := (-176384414270814230375580041216) }, { argument := 49072726314529993198963523584, coefficient := (-49072726314529993198963523584) }, { argument := 49072707425064061720382668800, coefficient := (-49072707425064061720382668800) }, { argument := 274026090467468811291328512, coefficient := (-274026090467468811291328512) }, { argument := 31985393768332732656156409856, coefficient := (-31985393768332732656156409856) }, { argument := 1886315135129784298162356224, coefficient := (-1886315135129784298162356224) }, { argument := 321004832747902442437596938240, coefficient := (-321004832747902442437596938240) }, { argument := 994979411936589519909814272, coefficient := (-994979411936589519909814272) }, { argument := 72550582120376319160090624, coefficient := (-72550582120376319160090624) }, { argument := 1886315135129784298162356224, coefficient := (-1886315135129784298162356224) }, { argument := 1886315135129784298162356224, coefficient := (-1886315135129784298162356224) }, { argument := 994979411936589519909814272, coefficient := (-994979411936589519909814272) }, { argument := 23278372491766458976223363072, coefficient := (-23278372491766458976223363072) }, { argument := 1865586397381105349830901760, coefficient := (-1865586397381105349830901760) }, { argument := 31985398735118574502453182464, coefficient := (-31985398735118574502453182464) }, { argument := 1886315135129784298162356224, coefficient := (-1886315135129784298162356224) }, { argument := 72550582120376319160090624, coefficient := (-72550582120376319160090624) }, { argument := 1865586397381105349830901760, coefficient := (-1865586397381105349830901760) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := Form.normalizePowersOfTwo rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

/-- Sign separation retains this bounded shard's exact constant. -/
theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by
  rfl

/-- Sign separation only permutes this bounded shard's exact term list. -/
theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by
  decide +kernel

/-- Rational lower endpoint contributed by this shard. -/
noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

/-- Kernel-checked lower-bound certificate before restoring source term order. -/
noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

/-- Kernel-checked lower-bound certificate in the shard's exact source order. -/
noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard10


end Parent2

namespace Parent2

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 107519082096890070089677559165878272
def positiveArguments : Array ℕ := #[
    14039, 1, 1, 1, 1, 2201,
    26341, 39405, 11431, 2201, 45653, 22933,
    2201, 26341
  ]
def positiveCoefficients : Array ℕ := #[
    1112284173537757035475763518767104, 158456325028528675187087900672, 158456325028528675187087900672, 158456325028528675187087900672, 158456325028528675187087900672, 85147063327097562032905388032,
    2038036160926012613819864449024, 1524407101501262804137499688960, 1768861573633897740296486125568, 85147063327097562032905388032, 1766114894171733302811553693696, 1774354932558226615266350989312,
    85147063327097562032905388032, 2038036160926012613819864449024
  ]
def positiveScales : Array ℕ := #[
    13, 0, 0, 0, 0, 11,
    14, 15, 13, 11, 15, 14,
    11, 14
  ]
def negativeArguments : Array ℕ := #[
    62927599, 818058787, 818058787, 252581353197, 2132608074021, 17955,
    78231336599259, 282555, 8505, 625829909691321, 8505, 8505,
    728595, 8505, 282555, 728595, 17081647694919, 8505,
    8505, 17955, 147496333619405, 266781892585267, 147496333246669, 817004461,
    15903, 29123961427, 250263, 7533, 232991777003, 7533,
    7533, 645327, 7533, 250263, 645327, 6535950101,
    7533, 7533, 15903, 173237579711, 596219833909, 43309394051,
    5289985, 5289983, 28524629, 3142576853, 912788107, 5195777,
    5195775, 1
  ]
def negativeCoefficients : Array ℕ := #[
    72550582120376319160090624, 1886315135129784298162356224, 1886315135129784298162356224, 284381322034686209638268928, 19208825854976573502318968832, 169580180399848959623823360,
    704645236714237356322144124928, 1334328261567232603355873280, 160654907747225330169937920, 704621837020786104739565666304, 160654907747225330169937920, 160654907747225330169937920,
    6881385215172818308945674240, 160654907747225330169937920, 1334328261567232603355873280, 6881385215172818308945674240, 19232225548427825084897427456, 160654907747225330169937920,
    160654907747225330169937920, 169580180399848959623823360, 83033054140858339947823759360, 300369708009051037742670020608, 83033053931026626109377609728, 7535536099573008244290879488,
    150199588354151935666814976, 268621131428228913032924758016, 1181833603102406020115202048, 142294346861828149579087872, 268621230103321727819136892928, 142294346861828149579087872,
    142294346861828149579087872, 6094941190581639073637597184, 142294346861828149579087872, 1181833603102406020115202048, 6094941190581639073637597184, 7535437424480193458078744576,
    142294346861828149579087872, 142294346861828149579087872, 150199588354151935666814976, 199729331054854706721179303936, 687394667986808682374898909184, 199729327011558990064966959104,
    49962495717766360271547269120, 49962476828300428792966414336, 8418984495368217817644007424, 28985155469627281376725172224, 8418984301677405043693715456, 49072726314529993198963523584,
    49072707425064061720382668800, 633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    25, 29, 29, 37, 40, 14,
    46, 18, 13, 49, 13, 13,
    19, 13, 18, 19, 43, 13,
    13, 14, 47, 47, 47, 29,
    13, 34, 17, 12, 37, 12,
    12, 19, 12, 17, 19, 32,
    12, 12, 13, 37, 39, 35,
    22, 22, 24, 31, 29, 22,
    22, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13777152555450350, 0, 0, 0, 0, 11103943429891557,
    14685022496122336, 15266091080742150, 13480663997619289, 11103943429891557, 15478422046832620, 14485137474198596,
    11103943429891557, 14685022496122336
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    25907189567166222, 29607629280348623, 29607629280348623, 37877957182870186, 40955756004878301, 14132098032552021,
    46152811847469573, 18108172193306541, 13054095520550748, 49152763937996156, 13054095520550748, 13054095520550748,
    19474757569023584, 13054095520550748, 18108172193306541, 19474757569023584, 43957512389328265, 13054095520550748,
    13054095520550748, 14132098032552021, 47067672421644378, 47922654084059030, 47067672417998563, 29605768714887755,
    13957011337722461, 34761487552720179, 17933085494560247, 12879008816975791, 37761488082678641, 12879008816975791,
    12879008816975791, 19299670862465379, 12879008816975791, 17933085494560247, 19299670862465379, 32605749823199456,
    12879008816975791, 12879008816975791, 13957011337722461, 37333960965637631, 39117053412726780, 35333960936431892,
    22334832200839980, 22334831655395971, 24765704787032810, 31549300880761020, 29765704753841541, 22308908081730818,
    22308907526397008, 0
  ]

abbrev PositiveTerm := Fin 14
abbrev NegativeTerm := Fin 50
def positiveArgument (term : PositiveTerm) : ℕ :=
  positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ :=
  positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ :=
  positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ :=
  negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ :=
  negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ :=
  negativeScales[term.val]?.getD 0
def positiveLogLowerNumerator (term : PositiveTerm) : ℕ :=
  positiveLogLowerNumerators[term.val]?.getD 0
def negativeLogUpperNumerator (term : NegativeTerm) : ℕ :=
  negativeLogUpperNumerators[term.val]?.getD 0

noncomputable def positiveLogLower (term : PositiveTerm) : ℝ :=
  (positiveLogLowerNumerator term : ℝ) / logBoundDenominator
noncomputable def negativeLogUpper (term : NegativeTerm) : ℝ :=
  (negativeLogUpperNumerator term : ℝ) / logBoundDenominator
def positiveLogLowerRat (term : PositiveTerm) : ℚ :=
  positiveLogLowerNumerator term / logBoundDenominator
def negativeLogUpperRat (term : NegativeTerm) : ℚ :=
  negativeLogUpperNumerator term / logBoundDenominator

theorem positiveScales_valid :
    ∀ term, 2 ^ positiveScale term ≤ positiveArgument term := by decide

theorem negativeScales_valid :
    ∀ term, 2 ^ negativeScale term ≤ negativeArgument term := by decide

noncomputable def positiveExact : ℝ :=
  Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ :=
  Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 93208737849 / 500000000000
noncomputable def negativeCeiling : ℝ := 1912653207 / 1000000000000

theorem positiveLogLowerRat_le_fastRat :
    ∀ term, positiveLogLowerRat term ≤
      MatrixMultiplication.RationalDyadicLog.numeratorLogLower
        (positiveArgument term) (positiveScale term) 8 := by decide +kernel

theorem negativeFastRat_le_logUpperRat :
    ∀ term, MatrixMultiplication.RationalDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpperRat term := by decide +kernel

theorem positiveLogLower_le_fast (term : PositiveTerm) :
    positiveLogLower term ≤ MatrixMultiplication.FastDyadicLog.numeratorLogLower
      (positiveArgument term) (positiveScale term) 8 := by
  simpa [positiveLogLower, positiveLogLowerRat] using
    MatrixMultiplication.RationalDyadicLog.cast_le_fastLower
      (positiveLogLowerRat_le_fastRat term)

theorem negativeFast_le_logUpper (term : NegativeTerm) :
    MatrixMultiplication.FastDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpper term := by
  simpa [negativeLogUpper, negativeLogUpperRat] using
    MatrixMultiplication.RationalDyadicLog.fastUpper_le_cast
      (negativeFastRat_le_logUpperRat term)

theorem positiveFloor_le_rationalLower : positiveFloor ≤ positiveRationalLower := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem positiveFloor_le_exact : positiveFloor ≤ positiveExact :=
  positiveFloor_le_rationalLower.trans
    (weightedLowerWithScale_le_natLogSum 8 bits
      positiveArgument positiveCoefficient positiveScale positiveLogLower
      positiveScales_valid positiveLogLower_le_fast)

theorem negativeExact_le_ceiling : negativeExact ≤ negativeCeiling :=
  (natLogSum_le_weightedUpperWithScale 8 bits
    negativeArgument negativeCoefficient negativeScale negativeLogUpper
    negativeScales_valid negativeFast_le_logUpper).trans
      negativeRationalUpper_le_ceiling

/-- Sign-separated exact form used by the directed arithmetic checker. -/
def signedForm : Form :=
  SignedDyadicLogCertificate.Form.ofSignedFamilies constantNumerator
    positiveArgument positiveCoefficient negativeArgument negativeCoefficient

/-- Exact source-order form before this shard's bounded power-of-two normalization. -/
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 72550582120376319160090624, coefficient := (-72550582120376319160090624) }, { argument := 1886315135129784298162356224, coefficient := (-1886315135129784298162356224) }, { argument := 1886315135129784298162356224, coefficient := (-1886315135129784298162356224) }, { argument := 284381322034686209638268928, coefficient := (-284381322034686209638268928) }, { argument := 19208825854976573502318968832, coefficient := (-19208825854976573502318968832) }, { argument := 169580180399848959623823360, coefficient := (-169580180399848959623823360) }, { argument := 704645236714237356322144124928, coefficient := (-704645236714237356322144124928) }, { argument := 1334328261567232603355873280, coefficient := (-1334328261567232603355873280) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 704621837020786104739565666304, coefficient := (-704621837020786104739565666304) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 6881385215172818308945674240, coefficient := (-6881385215172818308945674240) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 1334328261567232603355873280, coefficient := (-1334328261567232603355873280) }, { argument := 6881385215172818308945674240, coefficient := (-6881385215172818308945674240) }, { argument := 19232225548427825084897427456, coefficient := (-19232225548427825084897427456) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 169580180399848959623823360, coefficient := (-169580180399848959623823360) }, { argument := 83033054140858339947823759360, coefficient := (-83033054140858339947823759360) }, { argument := 300369708009051037742670020608, coefficient := (-300369708009051037742670020608) }, { argument := 83033053931026626109377609728, coefficient := (-83033053931026626109377609728) }, { argument := 7535536099573008244290879488, coefficient := (-7535536099573008244290879488) }, { argument := 150199588354151935666814976, coefficient := (-150199588354151935666814976) }, { argument := 268621131428228913032924758016, coefficient := (-268621131428228913032924758016) }, { argument := 1181833603102406020115202048, coefficient := (-1181833603102406020115202048) }, { argument := 142294346861828149579087872, coefficient := (-142294346861828149579087872) }, { argument := 268621230103321727819136892928, coefficient := (-268621230103321727819136892928) }, { argument := 142294346861828149579087872, coefficient := (-142294346861828149579087872) }, { argument := 142294346861828149579087872, coefficient := (-142294346861828149579087872) }, { argument := 6094941190581639073637597184, coefficient := (-6094941190581639073637597184) }, { argument := 142294346861828149579087872, coefficient := (-142294346861828149579087872) }, { argument := 1181833603102406020115202048, coefficient := (-1181833603102406020115202048) }, { argument := 6094941190581639073637597184, coefficient := (-6094941190581639073637597184) }, { argument := 7535437424480193458078744576, coefficient := (-7535437424480193458078744576) }, { argument := 142294346861828149579087872, coefficient := (-142294346861828149579087872) }, { argument := 142294346861828149579087872, coefficient := (-142294346861828149579087872) }, { argument := 150199588354151935666814976, coefficient := (-150199588354151935666814976) }, { argument := 199729331054854706721179303936, coefficient := (-199729331054854706721179303936) }, { argument := 687394667986808682374898909184, coefficient := (-687394667986808682374898909184) }, { argument := 199729327011558990064966959104, coefficient := (-199729327011558990064966959104) }, { argument := 49962495717766360271547269120, coefficient := (-49962495717766360271547269120) }, { argument := 49962476828300428792966414336, coefficient := (-49962476828300428792966414336) }, { argument := 8418984495368217817644007424, coefficient := (-8418984495368217817644007424) }, { argument := 28985155469627281376725172224, coefficient := (-28985155469627281376725172224) }, { argument := 8418984301677405043693715456, coefficient := (-8418984301677405043693715456) }, { argument := 49072726314529993198963523584, coefficient := (-49072726314529993198963523584) }, { argument := 49072707425064061720382668800, coefficient := (-49072707425064061720382668800) }, { argument := 1112284173537757035475763518767104, coefficient := 1112284173537757035475763518767104 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 85147063327097562032905388032, coefficient := 85147063327097562032905388032 }, { argument := 2038036160926012613819864449024, coefficient := 2038036160926012613819864449024 }, { argument := 1524407101501262804137499688960, coefficient := 1524407101501262804137499688960 }, { argument := 1768861573633897740296486125568, coefficient := 1768861573633897740296486125568 }, { argument := 85147063327097562032905388032, coefficient := 85147063327097562032905388032 }, { argument := 1766114894171733302811553693696, coefficient := 1766114894171733302811553693696 }, { argument := 1774354932558226615266350989312, coefficient := 1774354932558226615266350989312 }, { argument := 85147063327097562032905388032, coefficient := 85147063327097562032905388032 }, { argument := 2038036160926012613819864449024, coefficient := 2038036160926012613819864449024 }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := Form.normalizePowersOfTwo rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

/-- Sign separation retains this bounded shard's exact constant. -/
theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by
  rfl

/-- Sign separation only permutes this bounded shard's exact term list. -/
theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by
  decide +kernel

/-- Rational lower endpoint contributed by this shard. -/
noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

/-- Kernel-checked lower-bound certificate before restoring source term order. -/
noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

/-- Kernel-checked lower-bound certificate in the shard's exact source order. -/
noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard11


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
