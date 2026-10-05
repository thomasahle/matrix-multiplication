import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 16, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1694552230721005497383117240926208)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1, 1, 1, 1, 56657791123625, 176471166773,
    1760005852369247, 74427933039, 7281312581, 74423738735, 148713259715, 7100126226367,
    176471166773, 7281312581, 96954427109255, 5094969897881721, 3319810249, 8561628355,
    7163812523, 200413689217, 1273384847778829, 7163812523, 6464978527, 3319831753,
    3319810249, 6464935519, 200413689217, 6464935519, 24238478631923, 8561628355,
    4935, 3675, 3885, 315, 67515, 122115,
    3675, 67515, 1995, 1995, 3885, 3885,
    122115, 3885, 4935, 315, 3530186102823, 770545742960115,
    7706656743, 14622131271133293, 2438815425, 292657851, 7706656743, 15315760869,
    2438815425, 236369990991, 15120655635, 1541093778909813, 7706656743, 292657851,
    15120655635, 292657851, 7706656743, 7706656743
  ]
def negativeCoefficients : Array ℕ := #[
    19807040628566084398385987584, 19807040628566084398385987584, 19807040628566084398385987584, 19807040628566084398385987584, 15947750436999559116750848000, 203457403115652980499386728448,
    495397606306252061484391596032, 171619129088203073501295280128, 8394781856399284345090605056, 171609457681646156467897630720, 171454715145606603309150371840, 15988062913674953565736534016,
    203457403115652980499386728448, 8394781856399284345090605056, 109160980450290183418538885120, 5736426133391003188250913275904, 61239690036580980903991312384, 78967083559449953574940835840,
    1057192129630532167451325497344, 1848490016926981308946722062336, 5734815525955970055459448029184, 1057192129630532167451325497344, 59628902164798378216119074816, 61240086715365541954189262848,
    61239690036580980903991312384, 59628505486013817165921124352, 1848490016926981308946722062336, 59628505486013817165921124352, 109160403334756152471933943808, 78967083559449953574940835840,
    372878057487387186073436160, 277675149192735138565324800, 293542300575177146483343360, 380811633178608190032445440, 5101289169455105545642967040, 9226748528890027604327792640,
    277675149192735138565324800, 5101289169455105545642967040, 301475876266398150442352640, 301475876266398150442352640, 293542300575177146483343360, 293542300575177146483343360,
    9226748528890027604327792640, 293542300575177146483343360, 372878057487387186073436160, 380811633178608190032445440, 7949272408611083138686255104, 867557380216773976365213941760,
    71081362301024502492476473344, 8231528118004796921188938940416, 44988203987990191450934476800, 2699292239279411487056068608, 71081362301024502492476473344, 70631480261144600577967128576,
    44988203987990191450934476800, 1090064182629002338856142372864, 69731716181384796748948439040, 867558671055152921768840134656, 71081362301024502492476473344, 2699292239279411487056068608,
    69731716181384796748948439040, 2699292239279411487056068608, 71081362301024502492476473344, 71081362301024502492476473344
  ]
def negativeScales : Array ℕ := #[
    0, 0, 0, 0, 45, 37,
    50, 36, 32, 36, 37, 42,
    37, 32, 46, 52, 31, 32,
    32, 37, 50, 32, 32, 31,
    31, 32, 37, 32, 44, 32,
    12, 11, 11, 8, 16, 16,
    11, 16, 10, 10, 11, 11,
    16, 11, 12, 8, 41, 49,
    32, 53, 31, 28, 32, 33,
    31, 37, 33, 50, 32, 28,
    33, 28, 32, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0, 0, 0, 45687339591092270, 37360641527814463,
    50644501649447233, 36115125119854132, 32761551398573747, 36115043816076885, 37113742331852174, 42690981811850182,
    37360641527814463, 32761551398573747, 46462372009358779, 52177995045991014, 31628453637543540, 32995238088005346,
    32738080436642565, 37544190098657377, 50177589925875230, 32738080436642565, 32589998432217552, 31628462982539599,
    31628453637543540, 32589988834717041, 37544190098657377, 32589988834717041, 44462364382055355, 32995238088005346,
    12268834369343761, 11843528536141147, 11923698889934521, 8299208018387279, 16042920444994070, 16897880903343928,
    11843528536141147, 16042920444994070, 10962173043893966, 10962173043893966, 11923698889934521, 11923698889934521,
    16897880903343928, 11923698889934521, 12268834369343761, 8299208018387279, 41682881379570462, 49452873932382984,
    32843457989798378, 53699003127110135, 31183533429868019, 28124639740814450, 32843457989798378, 33834297990264550,
    31183533429868019, 37782255929992595, 33815801646256098, 50452876078966927, 32843457989798378, 28124639740814450,
    33815801646256098, 28124639740814450, 32843457989798378, 32843457989798378
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
noncomputable def negativeCeiling : ℝ := 17759845537 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 19807040628566084398385987584, coefficient := (-19807040628566084398385987584) }, { argument := 19807040628566084398385987584, coefficient := (-19807040628566084398385987584) }, { argument := 19807040628566084398385987584, coefficient := (-19807040628566084398385987584) }, { argument := 19807040628566084398385987584, coefficient := (-19807040628566084398385987584) }, { argument := 15947750436999559116750848000, coefficient := (-15947750436999559116750848000) }, { argument := 203457403115652980499386728448, coefficient := (-203457403115652980499386728448) }, { argument := 495397606306252061484391596032, coefficient := (-495397606306252061484391596032) }, { argument := 171619129088203073501295280128, coefficient := (-171619129088203073501295280128) }, { argument := 8394781856399284345090605056, coefficient := (-8394781856399284345090605056) }, { argument := 171609457681646156467897630720, coefficient := (-171609457681646156467897630720) }, { argument := 171454715145606603309150371840, coefficient := (-171454715145606603309150371840) }, { argument := 15988062913674953565736534016, coefficient := (-15988062913674953565736534016) }, { argument := 203457403115652980499386728448, coefficient := (-203457403115652980499386728448) }, { argument := 8394781856399284345090605056, coefficient := (-8394781856399284345090605056) }, { argument := 109160980450290183418538885120, coefficient := (-109160980450290183418538885120) }, { argument := 5736426133391003188250913275904, coefficient := (-5736426133391003188250913275904) }, { argument := 61239690036580980903991312384, coefficient := (-61239690036580980903991312384) }, { argument := 78967083559449953574940835840, coefficient := (-78967083559449953574940835840) }, { argument := 1057192129630532167451325497344, coefficient := (-1057192129630532167451325497344) }, { argument := 1848490016926981308946722062336, coefficient := (-1848490016926981308946722062336) }, { argument := 5734815525955970055459448029184, coefficient := (-5734815525955970055459448029184) }, { argument := 1057192129630532167451325497344, coefficient := (-1057192129630532167451325497344) }, { argument := 59628902164798378216119074816, coefficient := (-59628902164798378216119074816) }, { argument := 61240086715365541954189262848, coefficient := (-61240086715365541954189262848) }, { argument := 61239690036580980903991312384, coefficient := (-61239690036580980903991312384) }, { argument := 59628505486013817165921124352, coefficient := (-59628505486013817165921124352) }, { argument := 1848490016926981308946722062336, coefficient := (-1848490016926981308946722062336) }, { argument := 59628505486013817165921124352, coefficient := (-59628505486013817165921124352) }, { argument := 109160403334756152471933943808, coefficient := (-109160403334756152471933943808) }, { argument := 78967083559449953574940835840, coefficient := (-78967083559449953574940835840) }, { argument := 372878057487387186073436160, coefficient := (-372878057487387186073436160) }, { argument := 277675149192735138565324800, coefficient := (-277675149192735138565324800) }, { argument := 293542300575177146483343360, coefficient := (-293542300575177146483343360) }, { argument := 380811633178608190032445440, coefficient := (-380811633178608190032445440) }, { argument := 5101289169455105545642967040, coefficient := (-5101289169455105545642967040) }, { argument := 9226748528890027604327792640, coefficient := (-9226748528890027604327792640) }, { argument := 277675149192735138565324800, coefficient := (-277675149192735138565324800) }, { argument := 5101289169455105545642967040, coefficient := (-5101289169455105545642967040) }, { argument := 301475876266398150442352640, coefficient := (-301475876266398150442352640) }, { argument := 301475876266398150442352640, coefficient := (-301475876266398150442352640) }, { argument := 293542300575177146483343360, coefficient := (-293542300575177146483343360) }, { argument := 293542300575177146483343360, coefficient := (-293542300575177146483343360) }, { argument := 9226748528890027604327792640, coefficient := (-9226748528890027604327792640) }, { argument := 293542300575177146483343360, coefficient := (-293542300575177146483343360) }, { argument := 372878057487387186073436160, coefficient := (-372878057487387186073436160) }, { argument := 380811633178608190032445440, coefficient := (-380811633178608190032445440) }, { argument := 7949272408611083138686255104, coefficient := (-7949272408611083138686255104) }, { argument := 867557380216773976365213941760, coefficient := (-867557380216773976365213941760) }, { argument := 71081362301024502492476473344, coefficient := (-71081362301024502492476473344) }, { argument := 8231528118004796921188938940416, coefficient := (-8231528118004796921188938940416) }, { argument := 44988203987990191450934476800, coefficient := (-44988203987990191450934476800) }, { argument := 2699292239279411487056068608, coefficient := (-2699292239279411487056068608) }, { argument := 71081362301024502492476473344, coefficient := (-71081362301024502492476473344) }, { argument := 70631480261144600577967128576, coefficient := (-70631480261144600577967128576) }, { argument := 44988203987990191450934476800, coefficient := (-44988203987990191450934476800) }, { argument := 1090064182629002338856142372864, coefficient := (-1090064182629002338856142372864) }, { argument := 69731716181384796748948439040, coefficient := (-69731716181384796748948439040) }, { argument := 867558671055152921768840134656, coefficient := (-867558671055152921768840134656) }, { argument := 71081362301024502492476473344, coefficient := (-71081362301024502492476473344) }, { argument := 2699292239279411487056068608, coefficient := (-2699292239279411487056068608) }, { argument := 69731716181384796748948439040, coefficient := (-69731716181384796748948439040) }, { argument := 2699292239279411487056068608, coefficient := (-2699292239279411487056068608) }, { argument := 71081362301024502492476473344, coefficient := (-71081362301024502492476473344) }, { argument := 71081362301024502492476473344, coefficient := (-71081362301024502492476473344) }] }

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


end Parent0

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3822105767228704830414409112223744)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3530186102823, 4089, 3045, 3219, 261, 55941,
    101181, 3045, 55941, 1653, 1653, 3219,
    3219, 101181, 3219, 4089, 261, 15858267,
    649716135, 13378158345, 649716135, 15858267, 3518804433819, 62921511,
    67744712126679, 658373859, 29158749, 135489435068883, 29158749, 56782827,
    1072735029, 56782827, 658373859, 1072735029, 879705890361, 56782827,
    56782827, 62921511, 56657790664535, 176471126219, 1760006015676065, 74427915921,
    7281310907, 74423721617, 148713225533, 7100126173249, 176471126219, 7281310907,
    44662006562379, 2296920913924533, 12344116871, 31835059373, 26637518053, 745231803983,
    18370053274873223, 26637518053, 24040122833, 12344516999, 12344116871, 24039322577,
    745231803983, 24039322577, 357294208758393, 31835059373
  ]
def negativeCoefficients : Array ℕ := #[
    7949272408611083138686255104, 19309756548453979278802944, 14379605940338069675704320, 15201297708357387942887424, 19720602432463638412394496, 264173903418210822899367936,
    477813763103233572366974976, 14379605940338069675704320, 264173903418210822899367936, 15612143592367047076478976, 15612143592367047076478976, 15201297708357387942887424,
    15201297708357387942887424, 477813763103233572366974976, 15201297708357387942887424, 19309756548453979278802944, 19720602432463638412394496, 146266696400776874988404736,
    23970294525809449977061048320, 246783463167776733057798635520, 23970294525809449977061048320, 146266696400776874988404736, 7923643168468448776512602112, 145087126268512545351401472,
    305095060290033066012819062784, 1518106760224192242823200768, 134470995078133578618372096, 305095084644430245920960937984, 134470995078133578618372096, 130932284681340589707362304,
    4947117134716598497591689216, 130932284681340589707362304, 1518106760224192242823200768, 4947117134716598497591689216, 7923686240050860017804378112, 130932284681340589707362304,
    130932284681340589707362304, 145087126268512545351401472, 15947750307777212058655784960, 203457356360074282673314463744, 495397652273034854725729648640, 171619089616782441781282209792,
    8394779926408685633228767232, 171609418210225524747884560384, 171454675736443732837907038208, 15988062794063851062403530752, 203457356360074282673314463744, 8394779926408685633228767232,
    402279592223897422831936339968, 20688824344100051871749149556736, 227708764735297343656910913536, 293626596412539732026284048384, 3931003826260071550797882589184, 6873550181831641736784866443264,
    20682841270873801708303812657152, 3931003826260071550797882589184, 221730996700446213406996824064, 227716145794110068912379920384, 227708764735297343656910913536, 221723615641633488151527817216,
    6873550181831641736784866443264, 221723615641633488151527817216, 402277516356483730771890143232, 293626596412539732026284048384
  ]
def negativeScales : Array ℕ := #[
    41, 11, 11, 11, 8, 15,
    16, 11, 15, 10, 10, 11,
    11, 16, 11, 11, 8, 23,
    29, 33, 29, 23, 41, 25,
    45, 29, 24, 46, 24, 25,
    29, 25, 29, 29, 39, 25,
    25, 25, 45, 37, 50, 36,
    32, 36, 37, 42, 37, 32,
    45, 51, 33, 34, 34, 39,
    54, 34, 34, 33, 33, 34,
    39, 34, 48, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    41682881379570462, 11997532370288072, 11572226512796267, 11652396861500322, 8027905996569885, 15771618423534793,
    16626578877333553, 11572226512796267, 15771618423534793, 10690871009350625, 10690871009350625, 11652396861500322,
    11652396861500322, 16626578877333553, 11652396861500322, 11997532370288072, 8027905996569885, 23918731791459990,
    29275234292504625, 33639160475227385, 29275234292504625, 23918731791459990, 41678222473694032, 25907049985278198,
    45945173583167680, 29294331813206299, 24797425489763281, 46945173698331696, 24797425489763281, 25758951341608834,
    29998646644252779, 25758951341608834, 29294331813206299, 29998646644252779, 39678230315918651, 25758951341608834,
    25758951341608834, 25907049985278198, 45687339579402318, 37360641196275535, 50644501783311518, 36115124788042464,
    32761551066892918, 36115043484246517, 37113742000246185, 42690981801056983, 37360641196275535, 32761551066892918,
    45344113303159214, 51028622606951342, 33523104575034658, 34889897407391915, 34632740614650849, 39438898288718862,
    54028205328603726, 34632740614650849, 34484725216391570, 33523151338471179, 33523104575034658, 34484677190656127,
    39438898288718862, 34484677190656127, 48344105858458045, 34889897407391915
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
noncomputable def negativeCeiling : ℝ := 38423865261 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7949272408611083138686255104, coefficient := (-7949272408611083138686255104) }, { argument := 19309756548453979278802944, coefficient := (-19309756548453979278802944) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 15201297708357387942887424, coefficient := (-15201297708357387942887424) }, { argument := 19720602432463638412394496, coefficient := (-19720602432463638412394496) }, { argument := 264173903418210822899367936, coefficient := (-264173903418210822899367936) }, { argument := 477813763103233572366974976, coefficient := (-477813763103233572366974976) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 264173903418210822899367936, coefficient := (-264173903418210822899367936) }, { argument := 15612143592367047076478976, coefficient := (-15612143592367047076478976) }, { argument := 15612143592367047076478976, coefficient := (-15612143592367047076478976) }, { argument := 15201297708357387942887424, coefficient := (-15201297708357387942887424) }, { argument := 15201297708357387942887424, coefficient := (-15201297708357387942887424) }, { argument := 477813763103233572366974976, coefficient := (-477813763103233572366974976) }, { argument := 15201297708357387942887424, coefficient := (-15201297708357387942887424) }, { argument := 19309756548453979278802944, coefficient := (-19309756548453979278802944) }, { argument := 19720602432463638412394496, coefficient := (-19720602432463638412394496) }, { argument := 146266696400776874988404736, coefficient := (-146266696400776874988404736) }, { argument := 23970294525809449977061048320, coefficient := (-23970294525809449977061048320) }, { argument := 246783463167776733057798635520, coefficient := (-246783463167776733057798635520) }, { argument := 23970294525809449977061048320, coefficient := (-23970294525809449977061048320) }, { argument := 146266696400776874988404736, coefficient := (-146266696400776874988404736) }, { argument := 7923643168468448776512602112, coefficient := (-7923643168468448776512602112) }, { argument := 145087126268512545351401472, coefficient := (-145087126268512545351401472) }, { argument := 305095060290033066012819062784, coefficient := (-305095060290033066012819062784) }, { argument := 1518106760224192242823200768, coefficient := (-1518106760224192242823200768) }, { argument := 134470995078133578618372096, coefficient := (-134470995078133578618372096) }, { argument := 305095084644430245920960937984, coefficient := (-305095084644430245920960937984) }, { argument := 134470995078133578618372096, coefficient := (-134470995078133578618372096) }, { argument := 130932284681340589707362304, coefficient := (-130932284681340589707362304) }, { argument := 4947117134716598497591689216, coefficient := (-4947117134716598497591689216) }, { argument := 130932284681340589707362304, coefficient := (-130932284681340589707362304) }, { argument := 1518106760224192242823200768, coefficient := (-1518106760224192242823200768) }, { argument := 4947117134716598497591689216, coefficient := (-4947117134716598497591689216) }, { argument := 7923686240050860017804378112, coefficient := (-7923686240050860017804378112) }, { argument := 130932284681340589707362304, coefficient := (-130932284681340589707362304) }, { argument := 130932284681340589707362304, coefficient := (-130932284681340589707362304) }, { argument := 145087126268512545351401472, coefficient := (-145087126268512545351401472) }, { argument := 15947750307777212058655784960, coefficient := (-15947750307777212058655784960) }, { argument := 203457356360074282673314463744, coefficient := (-203457356360074282673314463744) }, { argument := 495397652273034854725729648640, coefficient := (-495397652273034854725729648640) }, { argument := 171619089616782441781282209792, coefficient := (-171619089616782441781282209792) }, { argument := 8394779926408685633228767232, coefficient := (-8394779926408685633228767232) }, { argument := 171609418210225524747884560384, coefficient := (-171609418210225524747884560384) }, { argument := 171454675736443732837907038208, coefficient := (-171454675736443732837907038208) }, { argument := 15988062794063851062403530752, coefficient := (-15988062794063851062403530752) }, { argument := 203457356360074282673314463744, coefficient := (-203457356360074282673314463744) }, { argument := 8394779926408685633228767232, coefficient := (-8394779926408685633228767232) }, { argument := 402279592223897422831936339968, coefficient := (-402279592223897422831936339968) }, { argument := 20688824344100051871749149556736, coefficient := (-20688824344100051871749149556736) }, { argument := 227708764735297343656910913536, coefficient := (-227708764735297343656910913536) }, { argument := 293626596412539732026284048384, coefficient := (-293626596412539732026284048384) }, { argument := 3931003826260071550797882589184, coefficient := (-3931003826260071550797882589184) }, { argument := 6873550181831641736784866443264, coefficient := (-6873550181831641736784866443264) }, { argument := 20682841270873801708303812657152, coefficient := (-20682841270873801708303812657152) }, { argument := 3931003826260071550797882589184, coefficient := (-3931003826260071550797882589184) }, { argument := 221730996700446213406996824064, coefficient := (-221730996700446213406996824064) }, { argument := 227716145794110068912379920384, coefficient := (-227716145794110068912379920384) }, { argument := 227708764735297343656910913536, coefficient := (-227708764735297343656910913536) }, { argument := 221723615641633488151527817216, coefficient := (-221723615641633488151527817216) }, { argument := 6873550181831641736784866443264, coefficient := (-6873550181831641736784866443264) }, { argument := 221723615641633488151527817216, coefficient := (-221723615641633488151527817216) }, { argument := 402277516356483730771890143232, coefficient := (-402277516356483730771890143232) }, { argument := 293626596412539732026284048384, coefficient := (-293626596412539732026284048384) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16
