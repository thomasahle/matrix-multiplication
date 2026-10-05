import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 10, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 127392313621362035399391088056729600
def positiveArguments : Array ℕ := #[
    17027, 1, 2445, 2675, 2445, 2675,
    291, 48597, 1261, 52283, 78279, 2425,
    78279, 81577, 48597, 2425, 9021, 10185,
    4365, 114945
  ]
def positiveCoefficients : Array ℕ := #[
    1349017923130378876205272842371072, 158456325028528675187087900672, 189172712253297173258022420480, 206968100318024514709697331200, 189172712253297173258022420480, 206968100318024514709697331200,
    45030068929005707499455643648, 940002688892994144051136561152, 48782574673089516457743613952, 1011300298030586514258607996928, 1514136067737816914669196017664, 46906321801047611978599628800,
    1514136067737816914669196017664, 1577928665387241666960091512832, 940002688892994144051136561152, 46906321801047611978599628800, 348983034199794233120781238272, 394013103128799940620236881920,
    337725516967542806245917327360, 4446719306739313615571244810240
  ]
def positiveScales : Array ℕ := #[
    14, 0, 11, 11, 11, 11,
    8, 15, 10, 15, 16, 11,
    16, 16, 15, 11, 13, 13,
    12, 16
  ]
def negativeArguments : Array ℕ := #[
    85437962295, 123526161577, 444319929781, 61763101393, 3542014652769, 3542013808287,
    5777, 21969766971, 21969761733, 24157, 73586928597, 264689993841,
    36793476573, 964228661505, 964228431615, 3625, 3542014652769, 3542013808287,
    370073, 23705, 1599285652975789, 70114425, 1599286219771731, 70114425,
    110987803, 5777, 3672002425, 13208083525, 1836001825, 85437982665,
    85437962295, 189, 21969766971, 21969761733, 23705, 189,
    85437982665, 85437962295, 5777, 12079, 1485549, 1,
    5, 97
  ]
def negativeCoefficients : Array ℕ := #[
    98503264039694460734322769920, 142415968063663329417889841152, 512266001969919116388132192256, 142416015574405612761446875136, 4083664862809934125556557676544, 4083663889188476072157209690112,
    446973725434477615505765040128, 101317667168268524135104118784, 101317643012257159612446277632, 467264336390889551574033498112, 84839952437449854980217372672, 305166785953542779203869474816,
    84839980740519871573703786496, 1111679959207390750926836858880, 1111679694162266056858785546240, 280470790150593968531832832000, 4083664862809934125556557676544, 4083663889188476072157209690112,
    7158252877475914601136618733568, 458521384863436553382558433280, 1800635567700185929428905230336, 1293382853850302828563660800, 1800636205855684226006221062144, 1293382853850302828563660800,
    2096500323578156230630338199552, 446973725434477615505765040128, 4233530560750990767475916800, 15227883530615907145901670400, 4233531973079833910863462400, 98503287524705509575795671040,
    98503264039694460734322769920, 14623166714058554497245904896, 101317667168268524135104118784, 101317643012257159612446277632, 458521384863436553382558433280, 14623166714058554497245904896,
    98503287524705509575795671040, 98503264039694460734322769920, 446973725434477615505765040128, 467283679204003385640828796928, 28061227225042074310243516416, 158456325028528675187087900672,
    792281625142643375935439503360, 7685131763883640746573763182592
  ]
def negativeScales : Array ℕ := #[
    36, 36, 38, 35, 41, 41,
    12, 34, 34, 14, 36, 37,
    35, 39, 39, 11, 41, 41,
    18, 14, 50, 26, 50, 26,
    26, 12, 31, 33, 30, 36,
    36, 7, 34, 34, 14, 7,
    36, 36, 12, 13, 20, 0,
    2, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14055536647426470, 0, 11255618749839595, 11385323176175871, 11255618749839595, 11385323176175871,
    8184875342908283, 15568579635382191, 10300352560328219, 15674054304937220, 16256337705464907, 11243769031961852,
    16256337705464907, 16315874832442271, 15568579635382191, 11243769031961852, 13139071653295158, 13314158359853249,
    12091765938516802, 16810584185923169
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    36314158187870590, 36846025667583563, 38692807898092232, 35846026148874417, 41687707319011731, 41687706975046429,
    12496104779340364, 34354800516333238, 34354800172367937, 14560153680494924, 36098730468918357, 37945512710632682,
    35098730950209197, 39810584358755788, 39810584014790481, 11823765280830443, 41687707319011731, 41687706975046429,
    18497450356935398, 14532903772614544, 50506349069024144, 26063207952028804, 50506349580323391, 26063207952028804,
    26725825899605059, 12496104779340364, 31773919865873865, 33620702097560676, 30773920347164709, 36314158531835892,
    36314158187870590, 7562242424222992, 34354800516333238, 34354800172367937, 14532903772614544, 7562242424222992,
    36314158531835892, 36314158187870590, 12496104779340364, 13560213400873323, 20502564761768832, 0,
    2321928094887363, 6599912842192769
  ]

abbrev PositiveTerm := Fin 20
abbrev NegativeTerm := Fin 44
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
noncomputable def positiveFloor : ℝ := 230880831051 / 1000000000000
noncomputable def negativeCeiling : ℝ := 3972645891 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 98503264039694460734322769920, coefficient := (-98503264039694460734322769920) }, { argument := 142415968063663329417889841152, coefficient := (-142415968063663329417889841152) }, { argument := 512266001969919116388132192256, coefficient := (-512266001969919116388132192256) }, { argument := 142416015574405612761446875136, coefficient := (-142416015574405612761446875136) }, { argument := 4083664862809934125556557676544, coefficient := (-4083664862809934125556557676544) }, { argument := 4083663889188476072157209690112, coefficient := (-4083663889188476072157209690112) }, { argument := 446973725434477615505765040128, coefficient := (-446973725434477615505765040128) }, { argument := 101317667168268524135104118784, coefficient := (-101317667168268524135104118784) }, { argument := 101317643012257159612446277632, coefficient := (-101317643012257159612446277632) }, { argument := 467264336390889551574033498112, coefficient := (-467264336390889551574033498112) }, { argument := 84839952437449854980217372672, coefficient := (-84839952437449854980217372672) }, { argument := 305166785953542779203869474816, coefficient := (-305166785953542779203869474816) }, { argument := 84839980740519871573703786496, coefficient := (-84839980740519871573703786496) }, { argument := 1111679959207390750926836858880, coefficient := (-1111679959207390750926836858880) }, { argument := 1111679694162266056858785546240, coefficient := (-1111679694162266056858785546240) }, { argument := 280470790150593968531832832000, coefficient := (-280470790150593968531832832000) }, { argument := 4083664862809934125556557676544, coefficient := (-4083664862809934125556557676544) }, { argument := 4083663889188476072157209690112, coefficient := (-4083663889188476072157209690112) }, { argument := 7158252877475914601136618733568, coefficient := (-7158252877475914601136618733568) }, { argument := 458521384863436553382558433280, coefficient := (-458521384863436553382558433280) }, { argument := 1800635567700185929428905230336, coefficient := (-1800635567700185929428905230336) }, { argument := 1293382853850302828563660800, coefficient := (-1293382853850302828563660800) }, { argument := 1800636205855684226006221062144, coefficient := (-1800636205855684226006221062144) }, { argument := 1293382853850302828563660800, coefficient := (-1293382853850302828563660800) }, { argument := 2096500323578156230630338199552, coefficient := (-2096500323578156230630338199552) }, { argument := 446973725434477615505765040128, coefficient := (-446973725434477615505765040128) }, { argument := 4233530560750990767475916800, coefficient := (-4233530560750990767475916800) }, { argument := 15227883530615907145901670400, coefficient := (-15227883530615907145901670400) }, { argument := 4233531973079833910863462400, coefficient := (-4233531973079833910863462400) }, { argument := 98503287524705509575795671040, coefficient := (-98503287524705509575795671040) }, { argument := 98503264039694460734322769920, coefficient := (-98503264039694460734322769920) }, { argument := 14623166714058554497245904896, coefficient := (-14623166714058554497245904896) }, { argument := 101317667168268524135104118784, coefficient := (-101317667168268524135104118784) }, { argument := 101317643012257159612446277632, coefficient := (-101317643012257159612446277632) }, { argument := 458521384863436553382558433280, coefficient := (-458521384863436553382558433280) }, { argument := 14623166714058554497245904896, coefficient := (-14623166714058554497245904896) }, { argument := 98503287524705509575795671040, coefficient := (-98503287524705509575795671040) }, { argument := 98503264039694460734322769920, coefficient := (-98503264039694460734322769920) }, { argument := 446973725434477615505765040128, coefficient := (-446973725434477615505765040128) }, { argument := 467283679204003385640828796928, coefficient := (-467283679204003385640828796928) }, { argument := 28061227225042074310243516416, coefficient := (-28061227225042074310243516416) }, { argument := 1349017923130378876205272842371072, coefficient := 1349017923130378876205272842371072 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 189172712253297173258022420480, coefficient := 189172712253297173258022420480 }, { argument := 206968100318024514709697331200, coefficient := 206968100318024514709697331200 }, { argument := 189172712253297173258022420480, coefficient := 189172712253297173258022420480 }, { argument := 206968100318024514709697331200, coefficient := 206968100318024514709697331200 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 45030068929005707499455643648, coefficient := 45030068929005707499455643648 }, { argument := 940002688892994144051136561152, coefficient := 940002688892994144051136561152 }, { argument := 48782574673089516457743613952, coefficient := 48782574673089516457743613952 }, { argument := 1011300298030586514258607996928, coefficient := 1011300298030586514258607996928 }, { argument := 1514136067737816914669196017664, coefficient := 1514136067737816914669196017664 }, { argument := 46906321801047611978599628800, coefficient := 46906321801047611978599628800 }, { argument := 1514136067737816914669196017664, coefficient := 1514136067737816914669196017664 }, { argument := 1577928665387241666960091512832, coefficient := 1577928665387241666960091512832 }, { argument := 940002688892994144051136561152, coefficient := 940002688892994144051136561152 }, { argument := 46906321801047611978599628800, coefficient := 46906321801047611978599628800 }, { argument := 7685131763883640746573763182592, coefficient := (-7685131763883640746573763182592) }, { argument := 348983034199794233120781238272, coefficient := 348983034199794233120781238272 }, { argument := 394013103128799940620236881920, coefficient := 394013103128799940620236881920 }, { argument := 337725516967542806245917327360, coefficient := 337725516967542806245917327360 }, { argument := 4446719306739313615571244810240, coefficient := 4446719306739313615571244810240 }] }

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

end TermShard2


end Parent0

namespace Parent0

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-27397882326474260787666379845140480)
def positiveArguments : Array ℕ := #[
    10185, 4365, 10185, 10185, 422241, 2619,
    114945, 422241, 9021, 10185, 2619, 10185,
    459, 13311, 11781, 765, 459, 765,
    23409, 765, 459, 375003, 24021, 13311,
    23409, 765, 24021, 765, 23409, 765,
    459, 3, 45, 79, 3, 25,
    3, 79, 157, 25, 2423, 155,
    45, 79, 3, 155, 3, 79,
    79, 3, 435, 64105731569, 64105753103, 50499822661,
    182678687791, 12626858723, 1457773511, 14462420739
  ]
def positiveCoefficients : Array ℕ := #[
    394013103128799940620236881920, 337725516967542806245917327360, 394013103128799940620236881920, 394013103128799940620236881920, 16334657503996820395427534733312, 405270620361051367495100792832,
    4446719306739313615571244810240, 16334657503996820395427534733312, 348983034199794233120781238272, 394013103128799940620236881920, 405270620361051367495100792832, 394013103128799940620236881920,
    35513404876999346636168626176, 514944370716490526224445079552, 911510725176316563661661405184, 29594504064166122196807188480, 568214478031989546178698018816, 29594504064166122196807188480,
    905591824363483339222299967488, 947024130053315910297830031360, 568214478031989546178698018816, 14507225892254233100874883792896, 929267427614816236979745718272, 514944370716490526224445079552,
    905591824363483339222299967488, 29594504064166122196807188480, 929267427614816236979745718272, 29594504064166122196807188480, 905591824363483339222299967488, 947024130053315910297830031360,
    35513404876999346636168626176, 232113757366008801543585792, 3481706360490132023153786880, 6112328943971565107314425856, 232113757366008801543585792, 3868562622766813359059763200,
    232113757366008801543585792, 6112328943971565107314425856, 6073643317743896973723828224, 3868562622766813359059763200, 93735272349639887690018062336, 5996272065288560706542632960,
    3481706360490132023153786880, 6112328943971565107314425856, 232113757366008801543585792, 5996272065288560706542632960, 232113757366008801543585792, 6112328943971565107314425856,
    6112328943971565107314425856, 232113757366008801543585792, 68928501387409973706383236792320, 302730758121284112887461418369024, 302730859812723955002401450098688, 238478669925167377671635448365056,
    862675712358826667743709061185536, 238514617669701638953890146680832, 6884140767961604058493963206656, 273187403836049780688516468965376
  ]
def positiveScales : Array ℕ := #[
    13, 12, 13, 13, 18, 11,
    16, 18, 13, 13, 11, 13,
    8, 13, 13, 9, 8, 9,
    14, 9, 8, 18, 14, 13,
    14, 9, 14, 9, 14, 9,
    8, 1, 5, 6, 1, 4,
    1, 6, 7, 4, 11, 7,
    5, 6, 1, 7, 1, 6,
    6, 1, 8, 35, 35, 35,
    37, 33, 30, 33
  ]
def negativeArguments : Array ℕ := #[
    291, 153, 1, 435, 3821, 16909
  ]
def negativeCoefficients : Array ℕ := #[
    46110790583301844479442579095552, 24243817729364887303624448802816, 158456325028528675187087900672, 68928501387409973706383236792320, 605461617934008067889862868467712, 1339668999953695684369234656231424
  ]
def negativeScales : Array ℕ := #[
    8, 7, 0, 8, 11, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13314158359853249, 12091765938516802, 13314158359853249, 13314158359853249, 18687707146971670, 11354800344350595,
    16810584185923169, 18687707146971670, 13139071653295158, 13314158359853249, 11354800344350595, 13314158359853249,
    8842350343321225, 13700331338536850, 13524174383387515, 9579315937579817, 8842350343321225, 9579315937579817,
    14514775685385275, 9579315937579817, 8842350343321225, 18516542611559461, 14552008591584190, 13700331338536850,
    14514775685385275, 9579315937579817, 14552008591584190, 9579315937579817, 14514775685385275, 9579315937579817,
    8842350343321225, 1584962500720924, 5491853096329661, 6303780748177102, 1584962500720924, 4643856189773592,
    1584962500720924, 6303780748177102, 7294620748891626, 4643856189773592, 11242578689451346, 7276124405274237,
    5491853096329661, 6303780748177102, 1584962500720924, 7276124405274237, 1584962500720924, 6303780748177102,
    6303780748177102, 1584962500720924, 8764871590716857, 35899734299778256, 35899734784399349, 35555559270469738,
    37410517375527615, 33555776722724172, 30441119444749093, 33751590001553055
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    8184875342908284, 7257387842692652, 0, 8764871591046276, 11899734546704385, 14045503720687020
  ]

abbrev PositiveTerm := Fin 58
abbrev NegativeTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 19656132227 / 20000000000
noncomputable def negativeCeiling : ℝ := 327151289209 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 394013103128799940620236881920, coefficient := 394013103128799940620236881920 }, { argument := 337725516967542806245917327360, coefficient := 337725516967542806245917327360 }, { argument := 394013103128799940620236881920, coefficient := 394013103128799940620236881920 }, { argument := 394013103128799940620236881920, coefficient := 394013103128799940620236881920 }, { argument := 16334657503996820395427534733312, coefficient := 16334657503996820395427534733312 }, { argument := 405270620361051367495100792832, coefficient := 405270620361051367495100792832 }, { argument := 4446719306739313615571244810240, coefficient := 4446719306739313615571244810240 }, { argument := 16334657503996820395427534733312, coefficient := 16334657503996820395427534733312 }, { argument := 348983034199794233120781238272, coefficient := 348983034199794233120781238272 }, { argument := 394013103128799940620236881920, coefficient := 394013103128799940620236881920 }, { argument := 405270620361051367495100792832, coefficient := 405270620361051367495100792832 }, { argument := 394013103128799940620236881920, coefficient := 394013103128799940620236881920 }, { argument := 46110790583301844479442579095552, coefficient := (-46110790583301844479442579095552) }, { argument := 35513404876999346636168626176, coefficient := 35513404876999346636168626176 }, { argument := 514944370716490526224445079552, coefficient := 514944370716490526224445079552 }, { argument := 911510725176316563661661405184, coefficient := 911510725176316563661661405184 }, { argument := 29594504064166122196807188480, coefficient := 29594504064166122196807188480 }, { argument := 568214478031989546178698018816, coefficient := 568214478031989546178698018816 }, { argument := 29594504064166122196807188480, coefficient := 29594504064166122196807188480 }, { argument := 905591824363483339222299967488, coefficient := 905591824363483339222299967488 }, { argument := 947024130053315910297830031360, coefficient := 947024130053315910297830031360 }, { argument := 568214478031989546178698018816, coefficient := 568214478031989546178698018816 }, { argument := 14507225892254233100874883792896, coefficient := 14507225892254233100874883792896 }, { argument := 929267427614816236979745718272, coefficient := 929267427614816236979745718272 }, { argument := 514944370716490526224445079552, coefficient := 514944370716490526224445079552 }, { argument := 905591824363483339222299967488, coefficient := 905591824363483339222299967488 }, { argument := 29594504064166122196807188480, coefficient := 29594504064166122196807188480 }, { argument := 929267427614816236979745718272, coefficient := 929267427614816236979745718272 }, { argument := 29594504064166122196807188480, coefficient := 29594504064166122196807188480 }, { argument := 905591824363483339222299967488, coefficient := 905591824363483339222299967488 }, { argument := 947024130053315910297830031360, coefficient := 947024130053315910297830031360 }, { argument := 35513404876999346636168626176, coefficient := 35513404876999346636168626176 }, { argument := 24243817729364887303624448802816, coefficient := (-24243817729364887303624448802816) }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 3868562622766813359059763200, coefficient := 3868562622766813359059763200 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 3868562622766813359059763200, coefficient := 3868562622766813359059763200 }, { argument := 93735272349639887690018062336, coefficient := 93735272349639887690018062336 }, { argument := 5996272065288560706542632960, coefficient := 5996272065288560706542632960 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 5996272065288560706542632960, coefficient := 5996272065288560706542632960 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 68928501387409973706383236792320, coefficient := 68928501387409973706383236792320 }, { argument := 68928501387409973706383236792320, coefficient := (-68928501387409973706383236792320) }, { argument := 302730758121284112887461418369024, coefficient := 302730758121284112887461418369024 }, { argument := 302730859812723955002401450098688, coefficient := 302730859812723955002401450098688 }, { argument := 605461617934008067889862868467712, coefficient := (-605461617934008067889862868467712) }, { argument := 238478669925167377671635448365056, coefficient := 238478669925167377671635448365056 }, { argument := 862675712358826667743709061185536, coefficient := 862675712358826667743709061185536 }, { argument := 238514617669701638953890146680832, coefficient := 238514617669701638953890146680832 }, { argument := 1339668999953695684369234656231424, coefficient := (-1339668999953695684369234656231424) }, { argument := 6884140767961604058493963206656, coefficient := 6884140767961604058493963206656 }, { argument := 273187403836049780688516468965376, coefficient := 273187403836049780688516468965376 }] }

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

end TermShard3


end Parent0

namespace Parent0

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-34926992536027118618623856848404480)
def positiveArguments : Array ℕ := #[
    28924840203, 1457780247, 2191729, 191665907, 990031915, 95832995,
    2191729
  ]
def positiveCoefficients : Array ℕ := #[
    273187391794015249370921174040576, 6884172577822232668424122662912, 20700295138266809269137440768, 3620466620502442050605010649088, 37402348258937996370288280862720, 3620468188328114363327221596160,
    20700295138266809269137440768
  ]
def positiveScales : Array ℕ := #[
    34, 30, 21, 27, 29, 26,
    21
  ]
def negativeArguments : Array ℕ := #[
    3535, 141
  ]
def negativeCoefficients : Array ℕ := #[
    560143108975848866786355728875520, 44684683658045086402758787989504
  ]
def negativeScales : Array ℕ := #[
    11, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    34751589937959406, 30441126111059922, 21063637994207387, 27514018496332964, 29882899792042598, 26514019121084984,
    21063637994207387
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    11787494500196317, 7139551352398794
  ]

abbrev PositiveTerm := Fin 7
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 132617460803 / 1000000000000
noncomputable def negativeCeiling : ℝ := 83317082481 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 273187391794015249370921174040576, coefficient := 273187391794015249370921174040576 }, { argument := 6884172577822232668424122662912, coefficient := 6884172577822232668424122662912 }, { argument := 560143108975848866786355728875520, coefficient := (-560143108975848866786355728875520) }, { argument := 20700295138266809269137440768, coefficient := 20700295138266809269137440768 }, { argument := 3620466620502442050605010649088, coefficient := 3620466620502442050605010649088 }, { argument := 37402348258937996370288280862720, coefficient := 37402348258937996370288280862720 }, { argument := 3620468188328114363327221596160, coefficient := 3620468188328114363327221596160 }, { argument := 20700295138266809269137440768, coefficient := 20700295138266809269137440768 }, { argument := 44684683658045086402758787989504, coefficient := (-44684683658045086402758787989504) }] }

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

end TermShard4


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10
