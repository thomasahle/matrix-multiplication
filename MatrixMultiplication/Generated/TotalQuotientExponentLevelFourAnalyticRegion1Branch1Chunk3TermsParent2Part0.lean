import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 3, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk3

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
def constantNumerator : ℤ := (-376149769426598805128113387732992)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    48137, 105, 106720681, 1185, 105, 26680175,
    105, 105, 4353, 27, 1185, 4353,
    3080795, 105, 27, 105, 9964533783, 29418837735,
    763363055, 315531953497, 47387229645, 79781857715, 47387229645, 49383717635,
    29418837735, 1468005875, 9964533783, 1607218645, 9964533909, 1607218645,
    1607218645, 5760906215, 401921425, 29418837735, 29418858777, 48137,
    763363055, 763363601, 105, 9964533909, 29418858777, 763363601,
    315531976135, 47387263539, 79781858765, 47387263539, 49383752957, 29418858777,
    1468006925, 315531953497, 5760906215, 315531976135, 5760906215, 106720681,
    47387229645, 47387263539, 1185, 105, 79781857715, 401921425,
    79781858765, 401921425, 26680175, 105
  ]
def negativeCoefficients : Array ℕ := #[
    14548515544697351145707798528, 2030995376952577013506375680, 503974166983423371434027646976, 22921233539893369152429096960, 2030995376952577013506375680, 503974256708386545957286707200,
    2030995376952577013506375680, 2030995376952577013506375680, 84199265484519692759935746048, 2089023816294079213892272128, 22921233539893369152429096960, 84199265484519692759935746048,
    14548643048592388626128568320, 2030995376952577013506375680, 2089023816294079213892272128, 2030995376952577013506375680, 91906602254416934603707121664, 33917610665220886156919439360,
    1760195363863758563033743360, 363783574577298911299027075072, 54633756101463583091085803520, 91982219437107182454010019840, 54633756101463583091085803520, 56935550038823882750437621760,
    33917610665220886156919439360, 1692495542176690925993984000, 91906602254416934603707121664, 29647951014809245671825080320, 91906603416561811247408873472, 29647951014809245671825080320,
    29647951014809245671825080320, 106269962580747774009477693440, 29656566658862592086455091200, 33917610665220886156919439360, 33917634924995186094193508352, 14548515544697351145707798528,
    1760195363863758563033743360, 1760196622854041593710641152, 2030995376952577013506375680, 91906603416561811247408873472, 33917634924995186094193508352, 1760196622854041593710641152,
    363783600677135932588828917760, 54633795178585060235557208064, 91982220647674762291199344640, 54633795178585060235557208064, 56935590762317268473486508032, 33917634924995186094193508352,
    1692496752744270763183308800, 363783574577298911299027075072, 106269962580747774009477693440, 363783600677135932588828917760, 106269962580747774009477693440, 503974166983423371434027646976,
    54633756101463583091085803520, 54633795178585060235557208064, 22921233539893369152429096960, 2030995376952577013506375680, 91982219437107182454010019840, 29656566658862592086455091200,
    91982220647674762291199344640, 29656566658862592086455091200, 503974256708386545957286707200, 2030995376952577013506375680
  ]
def negativeScales : Array ℕ := #[
    15, 6, 26, 10, 6, 24,
    6, 6, 12, 4, 10, 12,
    21, 6, 4, 6, 33, 34,
    29, 38, 35, 36, 35, 35,
    34, 30, 33, 30, 33, 30,
    30, 32, 28, 34, 34, 15,
    29, 29, 6, 33, 34, 29,
    38, 35, 36, 35, 35, 34,
    30, 38, 32, 38, 32, 26,
    35, 35, 10, 6, 36, 28,
    36, 28, 24, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15554858612348285, 6714245517766967, 26669264536842286, 10210671343785622, 6714245517766967, 24669264793692252,
    6714245517766967, 6714245517766967, 12087794304787901, 4754887502413606, 10210671343785622, 12087794304787901,
    21554871256142110, 6714245517766967, 4754887502413606, 6714245517766967, 33214155160336242, 34776021199697805,
    29507794124251003, 38198995156155443, 35463779269387417, 36215341665743354, 35463779269387417, 35523316396365284,
    34776021199697805, 30451210595884333, 33214155160336242, 30581919059667415, 33214155178578900, 30581919059667415,
    30581919059667415, 32423648625558717, 28582338243484300, 34776021199697805, 34776022231593719, 15554858612348285,
    29507794124251003, 29507795156146908, 6714245517766967, 33214155178578900, 34776022231593719, 29507795156146908,
    38198995259662327, 35463780301283322, 36215341684730500, 35463780301283322, 35523317428261189, 34776022231593719,
    30451211627780238, 38198995156155443, 32423648625558717, 38198995259662327, 32423648625558717, 26669264536842286,
    35463779269387417, 35463780301283322, 10210671343785622, 6714245517766967, 36215341665743354, 28582338243484300,
    36215341684730500, 28582338243484300, 24669264793692252, 6714245517766967
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
noncomputable def negativeCeiling : ℝ := 210854401 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 14548515544697351145707798528, coefficient := (-14548515544697351145707798528) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 503974166983423371434027646976, coefficient := (-503974166983423371434027646976) }, { argument := 22921233539893369152429096960, coefficient := (-22921233539893369152429096960) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 503974256708386545957286707200, coefficient := (-503974256708386545957286707200) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 84199265484519692759935746048, coefficient := (-84199265484519692759935746048) }, { argument := 2089023816294079213892272128, coefficient := (-2089023816294079213892272128) }, { argument := 22921233539893369152429096960, coefficient := (-22921233539893369152429096960) }, { argument := 84199265484519692759935746048, coefficient := (-84199265484519692759935746048) }, { argument := 14548643048592388626128568320, coefficient := (-14548643048592388626128568320) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 2089023816294079213892272128, coefficient := (-2089023816294079213892272128) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 91906602254416934603707121664, coefficient := (-91906602254416934603707121664) }, { argument := 33917610665220886156919439360, coefficient := (-33917610665220886156919439360) }, { argument := 1760195363863758563033743360, coefficient := (-1760195363863758563033743360) }, { argument := 363783574577298911299027075072, coefficient := (-363783574577298911299027075072) }, { argument := 54633756101463583091085803520, coefficient := (-54633756101463583091085803520) }, { argument := 91982219437107182454010019840, coefficient := (-91982219437107182454010019840) }, { argument := 54633756101463583091085803520, coefficient := (-54633756101463583091085803520) }, { argument := 56935550038823882750437621760, coefficient := (-56935550038823882750437621760) }, { argument := 33917610665220886156919439360, coefficient := (-33917610665220886156919439360) }, { argument := 1692495542176690925993984000, coefficient := (-1692495542176690925993984000) }, { argument := 91906602254416934603707121664, coefficient := (-91906602254416934603707121664) }, { argument := 29647951014809245671825080320, coefficient := (-29647951014809245671825080320) }, { argument := 91906603416561811247408873472, coefficient := (-91906603416561811247408873472) }, { argument := 29647951014809245671825080320, coefficient := (-29647951014809245671825080320) }, { argument := 29647951014809245671825080320, coefficient := (-29647951014809245671825080320) }, { argument := 106269962580747774009477693440, coefficient := (-106269962580747774009477693440) }, { argument := 29656566658862592086455091200, coefficient := (-29656566658862592086455091200) }, { argument := 33917610665220886156919439360, coefficient := (-33917610665220886156919439360) }, { argument := 33917634924995186094193508352, coefficient := (-33917634924995186094193508352) }, { argument := 14548515544697351145707798528, coefficient := (-14548515544697351145707798528) }, { argument := 1760195363863758563033743360, coefficient := (-1760195363863758563033743360) }, { argument := 1760196622854041593710641152, coefficient := (-1760196622854041593710641152) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 91906603416561811247408873472, coefficient := (-91906603416561811247408873472) }, { argument := 33917634924995186094193508352, coefficient := (-33917634924995186094193508352) }, { argument := 1760196622854041593710641152, coefficient := (-1760196622854041593710641152) }, { argument := 363783600677135932588828917760, coefficient := (-363783600677135932588828917760) }, { argument := 54633795178585060235557208064, coefficient := (-54633795178585060235557208064) }, { argument := 91982220647674762291199344640, coefficient := (-91982220647674762291199344640) }, { argument := 54633795178585060235557208064, coefficient := (-54633795178585060235557208064) }, { argument := 56935590762317268473486508032, coefficient := (-56935590762317268473486508032) }, { argument := 33917634924995186094193508352, coefficient := (-33917634924995186094193508352) }, { argument := 1692496752744270763183308800, coefficient := (-1692496752744270763183308800) }, { argument := 363783574577298911299027075072, coefficient := (-363783574577298911299027075072) }, { argument := 106269962580747774009477693440, coefficient := (-106269962580747774009477693440) }, { argument := 363783600677135932588828917760, coefficient := (-363783600677135932588828917760) }, { argument := 106269962580747774009477693440, coefficient := (-106269962580747774009477693440) }, { argument := 503974166983423371434027646976, coefficient := (-503974166983423371434027646976) }, { argument := 54633756101463583091085803520, coefficient := (-54633756101463583091085803520) }, { argument := 54633795178585060235557208064, coefficient := (-54633795178585060235557208064) }, { argument := 22921233539893369152429096960, coefficient := (-22921233539893369152429096960) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 91982219437107182454010019840, coefficient := (-91982219437107182454010019840) }, { argument := 29656566658862592086455091200, coefficient := (-29656566658862592086455091200) }, { argument := 91982220647674762291199344640, coefficient := (-91982220647674762291199344640) }, { argument := 29656566658862592086455091200, coefficient := (-29656566658862592086455091200) }, { argument := 503974256708386545957286707200, coefficient := (-503974256708386545957286707200) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }] }

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
def constantNumerator : ℤ := 683438839637103598223816986198016
def positiveArguments : Array ℕ := #[
    5, 9, 489, 535, 489, 535,
    21, 3507, 91, 3773, 5649, 175,
    5649, 5887, 3507, 175, 93, 105,
    45, 1185, 105, 45, 105, 105,
    4353, 27, 1185, 4353, 93, 105,
    27, 105, 7, 134217707, 134217749, 12698057,
    91810607, 25399615
  ]
def positiveCoefficients : Array ℕ := #[
    6338253001141147007483516026880, 1426106925256758076683791106048, 302676339605275477212835872768, 331148960508839223535515729920, 302676339605275477212835872768, 331148960508839223535515729920,
    6499185206248246443220402176, 135670491180432144502225895424, 7040783973435600313488769024, 145960867756991868037324865536, 218535102560097286653286023168, 6769984589841923378354585600,
    218535102560097286653286023168, 227742281602282302447848259584, 135670491180432144502225895424, 6769984589841923378354585600, 3597763239173136423925579776, 4061990753905154027012751360,
    3481706360490132023153786880, 45842467079786738304858193920, 4061990753905154027012751360, 3481706360490132023153786880, 4061990753905154027012751360, 4061990753905154027012751360,
    168398530969039385519871492096, 4178047632588158427784544256, 45842467079786738304858193920, 168398530969039385519871492096, 3597763239173136423925579776, 4061990753905154027012751360,
    4178047632588158427784544256, 4061990753905154027012751360, 1109194275199700726309615304704, 1267650401888837120971604230144, 1267650798567621682021802180608, 479719030194946227946311909376,
    1734253333074868915776297893888, 479785162215172334457884508160
  ]
def positiveScales : Array ℕ := #[
    2, 3, 8, 9, 8, 9,
    4, 11, 6, 11, 12, 7,
    12, 12, 11, 7, 6, 6,
    5, 10, 6, 5, 6, 6,
    12, 4, 10, 12, 6, 6,
    4, 6, 2, 26, 27, 23,
    26, 24
  ]
def negativeArguments : Array ℕ := #[
    1607218645, 5760906215, 401921425, 47387229645, 47387263539, 105,
    49383717635, 49383752957, 4353, 27, 29418837735, 29418858777,
    1185, 4353, 3080795, 1468005875, 1468006925, 105,
    27, 105, 9, 1, 7, 3,
    7, 1
  ]
def negativeCoefficients : Array ℕ := #[
    29647951014809245671825080320, 106269962580747774009477693440, 29656566658862592086455091200, 54633756101463583091085803520, 54633795178585060235557208064, 2030995376952577013506375680,
    56935550038823882750437621760, 56935590762317268473486508032, 84199265484519692759935746048, 2089023816294079213892272128, 33917610665220886156919439360, 33917634924995186094193508352,
    22921233539893369152429096960, 84199265484519692759935746048, 14548643048592388626128568320, 1692495542176690925993984000, 1692496752744270763183308800, 2030995376952577013506375680,
    2089023816294079213892272128, 2030995376952577013506375680, 1426106925256758076683791106048, 1267650600228229401496703205376, 1109194275199700726309615304704, 475368975085586025561263702016,
    1109194275199700726309615304704, 2535301200456458802993406410752
  ]
def negativeScales : Array ℕ := #[
    30, 32, 28, 35, 35, 6,
    35, 35, 12, 4, 34, 34,
    10, 12, 21, 30, 30, 6,
    4, 6, 3, 0, 2, 1,
    2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 3169925001442312, 8933690654464738, 9063395081288509, 8933690654464738, 9063395081288509,
    4392317422778759, 11776021715228447, 6507794640198673, 11881496384617007, 12463779785335379, 7451211111832325,
    12463779785335379, 12523316912312711, 11776021715228447, 7451211111832325, 6539158811107971, 6714245517659862,
    5491853096329661, 10210671343785621, 6714245517659862, 5491853096329661, 6714245517659862, 6714245517659862,
    12087794304787900, 4754887502147955, 10210671343785621, 12087794304787900, 6539158811107971, 6714245517659862,
    4754887502147955, 6714245517659862, 2807354922011143, 26999999772813176, 27000000225727211, 23598104423341182,
    26452157503932272, 24598303293421228
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    30581919059667415, 32423648625558717, 28582338243484300, 35463779269387417, 35463780301283322, 6714245517766967,
    35523316396365284, 35523317428261189, 12087794304787901, 4754887502413606, 34776021199697805, 34776022231593719,
    10210671343785622, 12087794304787901, 21554871256142110, 30451210595884333, 30451211627780238, 6714245517766967,
    4754887502413606, 6714245517766967, 3169925001442313, 0, 2807354922807594, 1584962500724866,
    2807354922807594, 0
  ]

abbrev PositiveTerm := Fin 38
abbrev NegativeTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 2285992959 / 1000000000000
noncomputable def negativeCeiling : ℝ := 357839221 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 29647951014809245671825080320, coefficient := (-29647951014809245671825080320) }, { argument := 106269962580747774009477693440, coefficient := (-106269962580747774009477693440) }, { argument := 29656566658862592086455091200, coefficient := (-29656566658862592086455091200) }, { argument := 54633756101463583091085803520, coefficient := (-54633756101463583091085803520) }, { argument := 54633795178585060235557208064, coefficient := (-54633795178585060235557208064) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 56935550038823882750437621760, coefficient := (-56935550038823882750437621760) }, { argument := 56935590762317268473486508032, coefficient := (-56935590762317268473486508032) }, { argument := 84199265484519692759935746048, coefficient := (-84199265484519692759935746048) }, { argument := 2089023816294079213892272128, coefficient := (-2089023816294079213892272128) }, { argument := 33917610665220886156919439360, coefficient := (-33917610665220886156919439360) }, { argument := 33917634924995186094193508352, coefficient := (-33917634924995186094193508352) }, { argument := 22921233539893369152429096960, coefficient := (-22921233539893369152429096960) }, { argument := 84199265484519692759935746048, coefficient := (-84199265484519692759935746048) }, { argument := 14548643048592388626128568320, coefficient := (-14548643048592388626128568320) }, { argument := 1692495542176690925993984000, coefficient := (-1692495542176690925993984000) }, { argument := 1692496752744270763183308800, coefficient := (-1692496752744270763183308800) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 2089023816294079213892272128, coefficient := (-2089023816294079213892272128) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 6338253001141147007483516026880, coefficient := 6338253001141147007483516026880 }, { argument := 1426106925256758076683791106048, coefficient := 1426106925256758076683791106048 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 302676339605275477212835872768, coefficient := 302676339605275477212835872768 }, { argument := 331148960508839223535515729920, coefficient := 331148960508839223535515729920 }, { argument := 302676339605275477212835872768, coefficient := 302676339605275477212835872768 }, { argument := 331148960508839223535515729920, coefficient := 331148960508839223535515729920 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 6499185206248246443220402176, coefficient := 6499185206248246443220402176 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 145960867756991868037324865536, coefficient := 145960867756991868037324865536 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 6769984589841923378354585600, coefficient := 6769984589841923378354585600 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 227742281602282302447848259584, coefficient := 227742281602282302447848259584 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 6769984589841923378354585600, coefficient := 6769984589841923378354585600 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 45842467079786738304858193920, coefficient := 45842467079786738304858193920 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 168398530969039385519871492096, coefficient := 168398530969039385519871492096 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 45842467079786738304858193920, coefficient := 45842467079786738304858193920 }, { argument := 168398530969039385519871492096, coefficient := 168398530969039385519871492096 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 1109194275199700726309615304704, coefficient := 1109194275199700726309615304704 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 1267650401888837120971604230144, coefficient := 1267650401888837120971604230144 }, { argument := 1267650798567621682021802180608, coefficient := 1267650798567621682021802180608 }, { argument := 2535301200456458802993406410752, coefficient := (-2535301200456458802993406410752) }, { argument := 479719030194946227946311909376, coefficient := 479719030194946227946311909376 }, { argument := 1734253333074868915776297893888, coefficient := 1734253333074868915776297893888 }, { argument := 479785162215172334457884508160, coefficient := 479785162215172334457884508160 }] }

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

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-308570924159730836726891593859072)
def positiveArguments : Array ℕ := #[
    42185, 106352041, 26588015, 2699867
  ]
def positiveCoefficients : Array ℕ := #[
    25499267850221565867490017280, 1004466627606356610844901507072, 1004466807056282959891419627520, 25499522858011640828331556864
  ]
def positiveScales : Array ℕ := #[
    15, 26, 24, 21
  ]
def negativeArguments : Array ℕ := #[
    17, 13
  ]
def negativeCoefficients : Array ℕ := #[
    2693757525484987478180494311424, 2059932225370872777432142708736
  ]
def negativeScales : Array ℕ := #[
    4, 3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    15364442481027592, 26664272479394402, 24664272737134668, 21364456908760839
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    4087462841250340, 3700439718214233
  ]

abbrev PositiveTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 315939061 / 500000000000
noncomputable def negativeCeiling : ℝ := 28036257 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2693757525484987478180494311424, coefficient := (-2693757525484987478180494311424) }, { argument := 25499267850221565867490017280, coefficient := 25499267850221565867490017280 }, { argument := 1004466627606356610844901507072, coefficient := 1004466627606356610844901507072 }, { argument := 1004466807056282959891419627520, coefficient := 1004466807056282959891419627520 }, { argument := 25499522858011640828331556864, coefficient := 25499522858011640828331556864 }, { argument := 2059932225370872777432142708736, coefficient := (-2059932225370872777432142708736) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk3
