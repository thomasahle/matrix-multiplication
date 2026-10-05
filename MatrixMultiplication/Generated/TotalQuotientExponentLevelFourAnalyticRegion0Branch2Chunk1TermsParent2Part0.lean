import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 1, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk1

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
def constantNumerator : ℤ := 1079689110144616574956674744320
def positiveArguments : Array ℕ := #[
    3, 2268853, 32180909, 9075327, 568185, 24597633,
    12301701, 140607, 136529, 1630993, 43539681, 203615,
    33903
  ]
def positiveCoefficients : Array ℕ := #[
    950737950171172051122527404032, 85714842894065945216238485504, 303940092099756222968473059328, 85714040091763857376552157184, 10732711200277157462975447040, 464636150548513279226803126272,
    464745123877471979159754375168, 10623964544909635272994455552, 1289479947079419582761402368, 30808586707980045024086720512, 411220660458472634375001341952, 30769428845104089925974753280,
    1280819126949836653439483904
  ]
def positiveScales : Array ℕ := #[
    1, 21, 24, 23, 19, 24,
    23, 17, 17, 20, 25, 17,
    15
  ]
def negativeArguments : Array ℕ := #[
    51622156179, 4933870554765, 16464256737989, 4927588460117, 102549557471, 101677588047,
    4664602512063, 2332721615541, 12604892721, 51622156179, 1464625315847, 412973957985,
    1464625315847, 17495825474509, 467047765982423, 8736805142215, 363699638299, 4664602512063,
    201675249257535, 100861401203265, 36071466825, 4933870554765, 17495825474509, 2466912913107,
    412973957985, 2466912913107, 131712812821761, 4927543942173, 51274379139, 2332721615541,
    100861401203265, 6305323623615, 1154497023885, 16464256737989, 467047765982423, 131712812821761,
    12604892721, 36071466825, 1154497023885, 25000262385, 4927588460117, 8736805142215,
    4927543942173, 102549557471, 363699638299, 51274379139, 3, 3,
    3
  ]
def negativeCoefficients : Array ℕ := #[
    116242761665902973804347392, 2777522198991739547214151680, 37074210255069719197250486272, 2773985694102259673809813504, 115460537203351216040443904, 57239393455049999766257664,
    2625937766894800796601286656, 2626411049627387257719619584, 56767390161340677400559616, 116242761665902973804347392, 412255376667871513130565632, 116241835205935304445788160,
    412255376667871513130565632, 9849274135942245470393335808, 131462259052666427528852799488, 9836768095722026827943772160, 409489388879540143916056576, 2625937766894800796601286656,
    113533072175760815761045585920, 113559842218772587720589967360, 2599223112828435335164723200, 2777522198991739547214151680, 9849274135942245470393335808, 2777497019056037494435872768,
    116241835205935304445788160, 2777497019056037494435872768, 37073860921500170461397385216, 2773960632727758461233790976, 115459637392026966763241472, 2626411049627387257719619584,
    113559842218772587720589967360, 113586612487051598291439452160, 2599696183284416310128148480, 37074210255069719197250486272, 131462259052666427528852799488, 37073860921500170461397385216,
    56767390161340677400559616, 2599223112828435335164723200, 2599696183284416310128148480, 56295586180625313803796480, 2773985694102259673809813504, 9836768095722026827943772160,
    2773960632727758461233790976, 115460537203351216040443904, 409489388879540143916056576, 115459637392026966763241472, 475368975085586025561263702016, 950737950171172051122527404032,
    475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    35, 42, 43, 42, 36, 36,
    42, 41, 33, 35, 40, 38,
    40, 43, 48, 42, 38, 42,
    47, 46, 35, 42, 43, 41,
    38, 41, 46, 42, 35, 41,
    46, 42, 40, 43, 48, 46,
    33, 35, 40, 34, 42, 42,
    42, 36, 38, 35, 1, 1,
    1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 21113531708505813, 24939701741481158, 23113518196209870, 19116001219531209, 24552016157684078,
    23552354480149408, 17101308893981686, 17058847899665960, 20637319159535517, 25375827501654881, 17635484320861715,
    15049125319389704
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    35587271350746989, 42165857004175244, 43904402622674040, 42164018909425294, 36577530309976959, 36565210756619222,
    42084891287612224, 41085151286586755, 33553264788488450, 35587271350746989, 40413668776601953, 38587259852357684,
    40413668776601953, 43992075988695698, 48730563433583345, 42990242973161900, 38403956534788237, 42084891287612224,
    47519027367434175, 46519367501414840, 35070139039537952, 42165857004175244, 43992075988695698, 41165843925203978,
    38587259852357684, 41165843925203978, 46904389028743871, 42164005875441697, 35577519066668854, 41085151286586755,
    46519367501414840, 42519707558084612, 40070401592720199, 43904402622674040, 48730563433583345, 46904389028743871,
    33553264788488450, 35070139039537952, 40070401592720199, 34541224185344077, 42164018909425294, 42990242973161900,
    42164005875441697, 36577530309976959, 38403956534788237, 35577519066668854, 1584962500724866, 1584962500724866,
    1584962500724866
  ]

abbrev PositiveTerm := Fin 13
abbrev NegativeTerm := Fin 49
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
noncomputable def positiveFloor : ℝ := 35564387 / 62500000000
noncomputable def negativeCeiling : ℝ := 564860347 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 116242761665902973804347392, coefficient := (-116242761665902973804347392) }, { argument := 2777522198991739547214151680, coefficient := (-2777522198991739547214151680) }, { argument := 37074210255069719197250486272, coefficient := (-37074210255069719197250486272) }, { argument := 2773985694102259673809813504, coefficient := (-2773985694102259673809813504) }, { argument := 115460537203351216040443904, coefficient := (-115460537203351216040443904) }, { argument := 57239393455049999766257664, coefficient := (-57239393455049999766257664) }, { argument := 2625937766894800796601286656, coefficient := (-2625937766894800796601286656) }, { argument := 2626411049627387257719619584, coefficient := (-2626411049627387257719619584) }, { argument := 56767390161340677400559616, coefficient := (-56767390161340677400559616) }, { argument := 116242761665902973804347392, coefficient := (-116242761665902973804347392) }, { argument := 412255376667871513130565632, coefficient := (-412255376667871513130565632) }, { argument := 116241835205935304445788160, coefficient := (-116241835205935304445788160) }, { argument := 412255376667871513130565632, coefficient := (-412255376667871513130565632) }, { argument := 9849274135942245470393335808, coefficient := (-9849274135942245470393335808) }, { argument := 131462259052666427528852799488, coefficient := (-131462259052666427528852799488) }, { argument := 9836768095722026827943772160, coefficient := (-9836768095722026827943772160) }, { argument := 409489388879540143916056576, coefficient := (-409489388879540143916056576) }, { argument := 2625937766894800796601286656, coefficient := (-2625937766894800796601286656) }, { argument := 113533072175760815761045585920, coefficient := (-113533072175760815761045585920) }, { argument := 113559842218772587720589967360, coefficient := (-113559842218772587720589967360) }, { argument := 2599223112828435335164723200, coefficient := (-2599223112828435335164723200) }, { argument := 2777522198991739547214151680, coefficient := (-2777522198991739547214151680) }, { argument := 9849274135942245470393335808, coefficient := (-9849274135942245470393335808) }, { argument := 2777497019056037494435872768, coefficient := (-2777497019056037494435872768) }, { argument := 116241835205935304445788160, coefficient := (-116241835205935304445788160) }, { argument := 2777497019056037494435872768, coefficient := (-2777497019056037494435872768) }, { argument := 37073860921500170461397385216, coefficient := (-37073860921500170461397385216) }, { argument := 2773960632727758461233790976, coefficient := (-2773960632727758461233790976) }, { argument := 115459637392026966763241472, coefficient := (-115459637392026966763241472) }, { argument := 2626411049627387257719619584, coefficient := (-2626411049627387257719619584) }, { argument := 113559842218772587720589967360, coefficient := (-113559842218772587720589967360) }, { argument := 113586612487051598291439452160, coefficient := (-113586612487051598291439452160) }, { argument := 2599696183284416310128148480, coefficient := (-2599696183284416310128148480) }, { argument := 37074210255069719197250486272, coefficient := (-37074210255069719197250486272) }, { argument := 131462259052666427528852799488, coefficient := (-131462259052666427528852799488) }, { argument := 37073860921500170461397385216, coefficient := (-37073860921500170461397385216) }, { argument := 56767390161340677400559616, coefficient := (-56767390161340677400559616) }, { argument := 2599223112828435335164723200, coefficient := (-2599223112828435335164723200) }, { argument := 2599696183284416310128148480, coefficient := (-2599696183284416310128148480) }, { argument := 56295586180625313803796480, coefficient := (-56295586180625313803796480) }, { argument := 2773985694102259673809813504, coefficient := (-2773985694102259673809813504) }, { argument := 9836768095722026827943772160, coefficient := (-9836768095722026827943772160) }, { argument := 2773960632727758461233790976, coefficient := (-2773960632727758461233790976) }, { argument := 115460537203351216040443904, coefficient := (-115460537203351216040443904) }, { argument := 409489388879540143916056576, coefficient := (-409489388879540143916056576) }, { argument := 115459637392026966763241472, coefficient := (-115459637392026966763241472) }, { argument := 950737950171172051122527404032, coefficient := 950737950171172051122527404032 }, { argument := 85714842894065945216238485504, coefficient := 85714842894065945216238485504 }, { argument := 303940092099756222968473059328, coefficient := 303940092099756222968473059328 }, { argument := 85714040091763857376552157184, coefficient := 85714040091763857376552157184 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 10732711200277157462975447040, coefficient := 10732711200277157462975447040 }, { argument := 464636150548513279226803126272, coefficient := 464636150548513279226803126272 }, { argument := 464745123877471979159754375168, coefficient := 464745123877471979159754375168 }, { argument := 10623964544909635272994455552, coefficient := 10623964544909635272994455552 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 1289479947079419582761402368, coefficient := 1289479947079419582761402368 }, { argument := 30808586707980045024086720512, coefficient := 30808586707980045024086720512 }, { argument := 411220660458472634375001341952, coefficient := 411220660458472634375001341952 }, { argument := 30769428845104089925974753280, coefficient := 30769428845104089925974753280 }, { argument := 1280819126949836653439483904, coefficient := 1280819126949836653439483904 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk1
