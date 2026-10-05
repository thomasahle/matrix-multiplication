import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 9, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-320151672960095885965366640246784)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    14880765, 120487309, 117308019, 120487309, 117308019, 68096118975,
    93378311, 380522035521, 48144701, 8135811, 192382423, 85508503,
    68180005055, 93378311, 8053891, 27062275, 4503208563, 4385801613,
    4503208563, 4385801613, 10497271525451, 5552700797, 55043480464309, 2473687727,
    466772113, 9880248685, 4869668525, 10498680811595, 5552700797, 466083985,
    2275, 45591, 76531, 73437, 2275, 73437,
    49049, 1183, 45591, 273, 378011487393, 21671880102751,
    26236325, 246621455, 2912232075, 204643335, 10835940443645, 2912232075,
    26236325, 204643335, 204643335, 204643335, 204643335, 204643335,
    189005351427, 246621455, 14880765, 36023767333, 35084511963, 36023767333,
    35084511963, 419228179902593, 56090537471, 2188169454198655
  ]
def negativeCoefficients : Array ℕ := #[
    70272425875459716058384957440, 4445197106505923043616882688, 4327902008573714962902417408, 4445197106505923043616882688, 4327902008573714962902417408, 153338828020593481010380800,
    430631451263064358617350144, 1713718897378638242739388416, 444056488926134161698193408, 18759902918633872605315072, 443603665170141767266205696, 394338367741756353871347712,
    153527722679908266818928640, 430631451263064358617350144, 18571008259319086796767232, 255595960820402255850949836800, 166139071744396712024123375616, 161807519826147084741919113216,
    166139071744396712024123375616, 161807519826147084741919113216, 23637754065214020858935246848, 51214625260071027002337918976, 247893798108237188550847627264, 45631484418245301195172216832,
    2152606427313908789020721152, 45564604719200085106480906240, 44914764502236841748149043200, 23640927495490509260518850560, 51214625260071027002337918976, 2149432997037420387437117440,
    171894139976455085778534400, 3444758565128159919001829376, 5782518868807949085589897216, 5548742838439970168931090432, 171894139976455085778534400, 5548742838439970168931090432,
    3706037657892371649385201664, 178769905575513289209675776, 3444758565128159919001829376, 165018374377396882347393024, 851206196882440873222078464, 48800735577583735082212917248,
    241987386354833875900825600, 284335178966929804183470080, 3357574985673320028123955200, 7550006454270816928105758720, 48800737344208509111023697920, 3357574985673320028123955200,
    241987386354833875900825600, 235937701695963029003304960, 235937701695963029003304960, 235937701695963029003304960, 7550006454270816928105758720, 235937701695963029003304960,
    851204430257666844411297792, 284335178966929804183470080, 70272425875459716058384957440, 166130304140677372408634540032, 161798753283115529364729495552, 166130304140677372408634540032,
    161798753283115529364729495552, 236004484349066136859250262016, 517343894842176395443928301568, 2463659784638141068001117470720
  ]
def negativeScales : Array ℕ := #[
    23, 26, 26, 26, 26, 35,
    26, 38, 25, 22, 27, 26,
    35, 26, 22, 24, 32, 32,
    32, 32, 43, 32, 45, 31,
    28, 33, 32, 43, 32, 28,
    11, 15, 16, 16, 11, 16,
    15, 10, 15, 8, 38, 44,
    24, 27, 31, 27, 43, 31,
    24, 27, 27, 27, 27, 27,
    37, 27, 23, 35, 35, 35,
    35, 48, 35, 50
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    23826945360672637, 26844305955182006, 26805726397028242, 26844305955182006, 26805726397028242, 35986853544619808,
    26476584157975299, 38469189044444904, 25520873682182838, 22955854745700220, 27519401752546631, 26349564553519816,
    35988629675043402, 26476584157975299, 22941254525535141, 24689779789364667, 32068306150639567, 32030193408721383,
    32068306150639567, 32030193408721383, 43255079621595673, 32370542513500652, 45645636929791102, 31204016243086596,
    28798143130452514, 33201900208761905, 32181176426373084, 43255273294176135, 32370542513500652, 28796014701324680,
    11151650829973422, 15476461433394026, 16223756630453841, 16164219503476477, 11151650829973422, 16164219503476477,
    15581936102954605, 10208234358339789, 15476461433394026, 8092757140919853, 38459639120940458, 44300889550661651,
    24645062315757021, 27877723075441849, 31439478182088377, 27608536439720275, 43300889602888338, 31439478182088377,
    24645062315757021, 27608536439720275, 27608536439720275, 27608536439720275, 27608536439720275, 27608536439720275,
    37459636126714788, 27877723075441849, 23826945360672637, 35068230013749878, 35030115243066318, 35068230013749878,
    35030115243066318, 48574729024402605, 35707038356243801, 50958645901678264
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
noncomputable def negativeCeiling : ℝ := 569118623 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 70272425875459716058384957440, coefficient := (-70272425875459716058384957440) }, { argument := 4445197106505923043616882688, coefficient := (-4445197106505923043616882688) }, { argument := 4327902008573714962902417408, coefficient := (-4327902008573714962902417408) }, { argument := 4445197106505923043616882688, coefficient := (-4445197106505923043616882688) }, { argument := 4327902008573714962902417408, coefficient := (-4327902008573714962902417408) }, { argument := 153338828020593481010380800, coefficient := (-153338828020593481010380800) }, { argument := 430631451263064358617350144, coefficient := (-430631451263064358617350144) }, { argument := 1713718897378638242739388416, coefficient := (-1713718897378638242739388416) }, { argument := 444056488926134161698193408, coefficient := (-444056488926134161698193408) }, { argument := 18759902918633872605315072, coefficient := (-18759902918633872605315072) }, { argument := 443603665170141767266205696, coefficient := (-443603665170141767266205696) }, { argument := 394338367741756353871347712, coefficient := (-394338367741756353871347712) }, { argument := 153527722679908266818928640, coefficient := (-153527722679908266818928640) }, { argument := 430631451263064358617350144, coefficient := (-430631451263064358617350144) }, { argument := 18571008259319086796767232, coefficient := (-18571008259319086796767232) }, { argument := 255595960820402255850949836800, coefficient := (-255595960820402255850949836800) }, { argument := 166139071744396712024123375616, coefficient := (-166139071744396712024123375616) }, { argument := 161807519826147084741919113216, coefficient := (-161807519826147084741919113216) }, { argument := 166139071744396712024123375616, coefficient := (-166139071744396712024123375616) }, { argument := 161807519826147084741919113216, coefficient := (-161807519826147084741919113216) }, { argument := 23637754065214020858935246848, coefficient := (-23637754065214020858935246848) }, { argument := 51214625260071027002337918976, coefficient := (-51214625260071027002337918976) }, { argument := 247893798108237188550847627264, coefficient := (-247893798108237188550847627264) }, { argument := 45631484418245301195172216832, coefficient := (-45631484418245301195172216832) }, { argument := 2152606427313908789020721152, coefficient := (-2152606427313908789020721152) }, { argument := 45564604719200085106480906240, coefficient := (-45564604719200085106480906240) }, { argument := 44914764502236841748149043200, coefficient := (-44914764502236841748149043200) }, { argument := 23640927495490509260518850560, coefficient := (-23640927495490509260518850560) }, { argument := 51214625260071027002337918976, coefficient := (-51214625260071027002337918976) }, { argument := 2149432997037420387437117440, coefficient := (-2149432997037420387437117440) }, { argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 5782518868807949085589897216, coefficient := (-5782518868807949085589897216) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 3706037657892371649385201664, coefficient := (-3706037657892371649385201664) }, { argument := 178769905575513289209675776, coefficient := (-178769905575513289209675776) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 165018374377396882347393024, coefficient := (-165018374377396882347393024) }, { argument := 851206196882440873222078464, coefficient := (-851206196882440873222078464) }, { argument := 48800735577583735082212917248, coefficient := (-48800735577583735082212917248) }, { argument := 241987386354833875900825600, coefficient := (-241987386354833875900825600) }, { argument := 284335178966929804183470080, coefficient := (-284335178966929804183470080) }, { argument := 3357574985673320028123955200, coefficient := (-3357574985673320028123955200) }, { argument := 7550006454270816928105758720, coefficient := (-7550006454270816928105758720) }, { argument := 48800737344208509111023697920, coefficient := (-48800737344208509111023697920) }, { argument := 3357574985673320028123955200, coefficient := (-3357574985673320028123955200) }, { argument := 241987386354833875900825600, coefficient := (-241987386354833875900825600) }, { argument := 235937701695963029003304960, coefficient := (-235937701695963029003304960) }, { argument := 235937701695963029003304960, coefficient := (-235937701695963029003304960) }, { argument := 235937701695963029003304960, coefficient := (-235937701695963029003304960) }, { argument := 7550006454270816928105758720, coefficient := (-7550006454270816928105758720) }, { argument := 235937701695963029003304960, coefficient := (-235937701695963029003304960) }, { argument := 851204430257666844411297792, coefficient := (-851204430257666844411297792) }, { argument := 284335178966929804183470080, coefficient := (-284335178966929804183470080) }, { argument := 70272425875459716058384957440, coefficient := (-70272425875459716058384957440) }, { argument := 166130304140677372408634540032, coefficient := (-166130304140677372408634540032) }, { argument := 161798753283115529364729495552, coefficient := (-161798753283115529364729495552) }, { argument := 166130304140677372408634540032, coefficient := (-166130304140677372408634540032) }, { argument := 161798753283115529364729495552, coefficient := (-161798753283115529364729495552) }, { argument := 236004484349066136859250262016, coefficient := (-236004484349066136859250262016) }, { argument := 517343894842176395443928301568, coefficient := (-517343894842176395443928301568) }, { argument := 2463659784638141068001117470720, coefficient := (-2463659784638141068001117470720) }] }

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

end TermShard0


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-511824258290379109906925616103424)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    24345749861, 4687010395, 97231845199, 48836067599, 419228582555777, 56090537471,
    4686961243, 75, 1503, 2523, 2421, 75,
    2421, 1617, 39, 1503, 9, 21861098386271,
    994921339841697, 2196744795, 20649401073, 243838672245, 17134609401, 497460553185795,
    243838672245, 2196744795, 17134609401, 17134609401, 17134609401, 17134609401,
    17134609401, 10930665928189, 20649401073, 175, 3507, 5887,
    5649, 175, 5649, 3773, 91, 3507,
    21, 6435325, 538824195, 269412195, 3217565, 139047817123,
    21453893852799, 2275, 856714767558813, 75, 175, 2275,
    2275, 75, 28075, 1125, 21453893852799, 2275,
    175, 1125, 175, 2275
  ]
def negativeCoefficients : Array ℕ := #[
    449099816968416890009604325376, 21615020306845328658745262080, 448402741050124442103653072896, 450433220282566150705477844992, 236004711022657314602220519424, 517343894842176395443928301568,
    21614793633254150915775004672, 90669436471097188102963200, 1817015506880787649583382528, 3050119842887709407783682048, 2926809409287017231963652096, 90669436471097188102963200,
    2926809409287017231963652096, 1954833050316855375499886592, 94296213929941075627081728, 1817015506880787649583382528, 87042659012253300578844672, 49226817273159913514318430208,
    2240363687687010612486504185856, 20261394514309276927115919360, 23807138554313400389361205248, 281126848886041217363733381120, 632155508846449440126016684032, 2240363161959067168811589304320,
    281126848886041217363733381120, 20261394514309276927115919360, 19754859651451545003938021376, 19754859651451545003938021376, 19754859651451545003938021376, 632155508846449440126016684032,
    19754859651451545003938021376, 49227343001103357189233311744, 23807138554313400389361205248, 6611313076017503299174400, 132490714043390766115454976, 222404571877228810984226816,
    213413186093845006497349632, 6611313076017503299174400, 213413186093845006497349632, 142539909918937371130200064, 6875765599058203431141376, 132490714043390766115454976,
    6346860552976803167207424, 237421586612289840506470400, 19879104051775139626604298240, 19879111246005328373329428480, 237414392382101093781340160, 156553924345455918293450752,
    24154937090277937790714904576, 171894139976455085778534400, 241143769246291957617763811328, 90669436471097188102963200, 6611313076017503299174400, 171894139976455085778534400,
    171894139976455085778534400, 90669436471097188102963200, 2121287024105044629992243200, 170005193383307227693056000, 24154937090277937790714904576, 171894139976455085778534400,
    6611313076017503299174400, 170005193383307227693056000, 6611313076017503299174400, 171894139976455085778534400
  ]
def negativeScales : Array ℕ := #[
    34, 32, 36, 35, 48, 35,
    32, 6, 10, 11, 11, 6,
    11, 10, 5, 10, 3, 44,
    49, 31, 34, 37, 33, 48,
    37, 31, 33, 33, 33, 33,
    33, 43, 34, 7, 11, 12,
    12, 7, 12, 11, 6, 11,
    4, 22, 29, 28, 21, 37,
    44, 11, 49, 6, 7, 11,
    11, 6, 14, 10, 44, 11,
    7, 10, 7, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34502950885877989, 32126020848461471, 36500709848983581, 35507227984501749, 48574730410057246, 35707038356243801,
    32126005719047944, 6228818690495881, 10553629293917849, 11300924490976301, 11241387363998937, 6228818690495881,
    11241387363998937, 10659103963500476, 5285402218862249, 10553629293917849, 3169925001442313, 44313431122954328,
    49821575797682822, 31032720129585522, 34265380886375797, 37827135997047895, 33996194275839963, 48821575459137252,
    37827135997047895, 31032720129585522, 33996194275839963, 33996194275839963, 33996194275839963, 33996194275839963,
    33996194275839963, 43313446530431163, 34265380886375797, 7451211111832378, 11776021715645854, 12523316912313329,
    12463779785335462, 7451211111832378, 12463779785335462, 11881496387932734, 6507794640199048, 11776021715645854,
    4392317422778766, 22617581579325264, 29005239393163415, 28005239915273381, 21617537862839240, 37016790140113748,
    44286304752229995, 11151650829973422, 49605808285482474, 6228818690495881, 7451211111832378, 11151650829973422,
    11151650829973422, 6228818690495881, 14776998402576533, 10135709286104400, 44286304752229995, 11151650829973422,
    7451211111832378, 10135709286104400, 7451211111832378, 11151650829973422
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
noncomputable def negativeCeiling : ℝ := 2345954059 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 449099816968416890009604325376, coefficient := (-449099816968416890009604325376) }, { argument := 21615020306845328658745262080, coefficient := (-21615020306845328658745262080) }, { argument := 448402741050124442103653072896, coefficient := (-448402741050124442103653072896) }, { argument := 450433220282566150705477844992, coefficient := (-450433220282566150705477844992) }, { argument := 236004711022657314602220519424, coefficient := (-236004711022657314602220519424) }, { argument := 517343894842176395443928301568, coefficient := (-517343894842176395443928301568) }, { argument := 21614793633254150915775004672, coefficient := (-21614793633254150915775004672) }, { argument := 90669436471097188102963200, coefficient := (-90669436471097188102963200) }, { argument := 1817015506880787649583382528, coefficient := (-1817015506880787649583382528) }, { argument := 3050119842887709407783682048, coefficient := (-3050119842887709407783682048) }, { argument := 2926809409287017231963652096, coefficient := (-2926809409287017231963652096) }, { argument := 90669436471097188102963200, coefficient := (-90669436471097188102963200) }, { argument := 2926809409287017231963652096, coefficient := (-2926809409287017231963652096) }, { argument := 1954833050316855375499886592, coefficient := (-1954833050316855375499886592) }, { argument := 94296213929941075627081728, coefficient := (-94296213929941075627081728) }, { argument := 1817015506880787649583382528, coefficient := (-1817015506880787649583382528) }, { argument := 87042659012253300578844672, coefficient := (-87042659012253300578844672) }, { argument := 49226817273159913514318430208, coefficient := (-49226817273159913514318430208) }, { argument := 2240363687687010612486504185856, coefficient := (-2240363687687010612486504185856) }, { argument := 20261394514309276927115919360, coefficient := (-20261394514309276927115919360) }, { argument := 23807138554313400389361205248, coefficient := (-23807138554313400389361205248) }, { argument := 281126848886041217363733381120, coefficient := (-281126848886041217363733381120) }, { argument := 632155508846449440126016684032, coefficient := (-632155508846449440126016684032) }, { argument := 2240363161959067168811589304320, coefficient := (-2240363161959067168811589304320) }, { argument := 281126848886041217363733381120, coefficient := (-281126848886041217363733381120) }, { argument := 20261394514309276927115919360, coefficient := (-20261394514309276927115919360) }, { argument := 19754859651451545003938021376, coefficient := (-19754859651451545003938021376) }, { argument := 19754859651451545003938021376, coefficient := (-19754859651451545003938021376) }, { argument := 19754859651451545003938021376, coefficient := (-19754859651451545003938021376) }, { argument := 632155508846449440126016684032, coefficient := (-632155508846449440126016684032) }, { argument := 19754859651451545003938021376, coefficient := (-19754859651451545003938021376) }, { argument := 49227343001103357189233311744, coefficient := (-49227343001103357189233311744) }, { argument := 23807138554313400389361205248, coefficient := (-23807138554313400389361205248) }, { argument := 6611313076017503299174400, coefficient := (-6611313076017503299174400) }, { argument := 132490714043390766115454976, coefficient := (-132490714043390766115454976) }, { argument := 222404571877228810984226816, coefficient := (-222404571877228810984226816) }, { argument := 213413186093845006497349632, coefficient := (-213413186093845006497349632) }, { argument := 6611313076017503299174400, coefficient := (-6611313076017503299174400) }, { argument := 213413186093845006497349632, coefficient := (-213413186093845006497349632) }, { argument := 142539909918937371130200064, coefficient := (-142539909918937371130200064) }, { argument := 6875765599058203431141376, coefficient := (-6875765599058203431141376) }, { argument := 132490714043390766115454976, coefficient := (-132490714043390766115454976) }, { argument := 6346860552976803167207424, coefficient := (-6346860552976803167207424) }, { argument := 237421586612289840506470400, coefficient := (-237421586612289840506470400) }, { argument := 19879104051775139626604298240, coefficient := (-19879104051775139626604298240) }, { argument := 19879111246005328373329428480, coefficient := (-19879111246005328373329428480) }, { argument := 237414392382101093781340160, coefficient := (-237414392382101093781340160) }, { argument := 156553924345455918293450752, coefficient := (-156553924345455918293450752) }, { argument := 24154937090277937790714904576, coefficient := (-24154937090277937790714904576) }, { argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }, { argument := 241143769246291957617763811328, coefficient := (-241143769246291957617763811328) }, { argument := 90669436471097188102963200, coefficient := (-90669436471097188102963200) }, { argument := 6611313076017503299174400, coefficient := (-6611313076017503299174400) }, { argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }, { argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }, { argument := 90669436471097188102963200, coefficient := (-90669436471097188102963200) }, { argument := 2121287024105044629992243200, coefficient := (-2121287024105044629992243200) }, { argument := 170005193383307227693056000, coefficient := (-170005193383307227693056000) }, { argument := 24154937090277937790714904576, coefficient := (-24154937090277937790714904576) }, { argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }, { argument := 6611313076017503299174400, coefficient := (-6611313076017503299174400) }, { argument := 170005193383307227693056000, coefficient := (-170005193383307227693056000) }, { argument := 6611313076017503299174400, coefficient := (-6611313076017503299174400) }, { argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }] }

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

end TermShard1


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9
