import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 7, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk7

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
def constantNumerator : ℤ := 191375552184181287862460181643264
def positiveArguments : Array ℕ := #[
    49, 8388619
  ]
def positiveCoefficients : Array ℕ := #[
    3882179963198952542083653566464, 79228266406326960725738651648
  ]
def positiveScales : Array ℕ := #[
    5, 23
  ]
def negativeArguments : Array ℕ := #[
    762064093055, 68850538356447, 68838878176037, 762064093055, 1156757613965, 19565536926165,
    237110333566235, 9782883835405, 1205064535135, 1202210914875, 22439097651195, 44878188095955,
    300544097535, 1156757613965, 2072304221209, 1156637366849, 762062094465, 68850357788961,
    68838697639131, 762062094465, 2072304221209, 140139914934107, 1697851028837213, 8758848478063,
    2157465649939, 22439097651195, 1668261428984765, 1668261268419975, 22438485768035, 19565536926165,
    140139914934107, 39127058027771, 762064093055, 762062094465, 1156637366849, 39127058027771,
    474171438174829, 9781879878711, 1204933094779, 44878188095955, 1668261268419975, 1668261107854015,
    44876964328935, 237110333566235, 1697851028837213, 474171438174829, 68850538356447, 68850357788961,
    300544097535, 22438485768035, 44876964328935, 1202141865815, 9782883835405, 8758848478063,
    9781879878711, 68838878176037, 68838697639131, 1205064535135, 2157465649939, 1204933094779,
    762064093055, 762062094465
  ]
def negativeCoefficients : Array ℕ := #[
    429003945689366623588188160, 19379703680397046956511199232, 19376421631387700159181750272, 429003945689366623588188160, 325598322450672378749911040, 11014418101247546713681428480,
    133481251236823744492412600320, 11014547998934701680854302720, 339195511961961624040898560, 338392289265737067921408000, 12632088977556496753455267840, 12632086949125372961598996480,
    338382571416757001351331840, 325598322450672378749911040, 1166603564804394789223006208, 325564475896496755199442944, 429002820583219215288238080, 19379652855168130404807868416,
    19376370814766288395290279936, 429002820583219215288238080, 1166603564804394789223006208, 39445879292311080793844744192, 477902578800117857831226441728, 39446346741999162808229429248,
    1214545187141240670774099968, 12632088977556496753455267840, 469573846870772426817237155840, 469573801675801901015865753600, 12631744517960075468257361920, 11014418101247546713681428480,
    39445879292311080793844744192, 11013287747123328108279627776, 429003945689366623588188160, 429002820583219215288238080, 325564475896496755199442944, 11013287747123328108279627776,
    133467394517118254146675277824, 11013417644186453052084977664, 339158514790817683707265024, 12632086949125372961598996480, 469573801675801901015865753600, 469573756480502049491742883840,
    12631742489331919192703631360, 133481251236823744492412600320, 477902578800117857831226441728, 133467394517118254146675277824, 19379703680397046956511199232, 19379652855168130404807868416,
    338382571416757001351331840, 12631744517960075468257361920, 12631742489331919192703631360, 338372853683181675232624640, 11014547998934701680854302720, 39446346741999162808229429248,
    11013417644186453052084977664, 19376421631387700159181750272, 19376370814766288395290279936, 339195511961961624040898560, 1214545187141240670774099968, 339158514790817683707265024,
    429003945689366623588188160, 429002820583219215288238080
  ]
def negativeScales : Array ℕ := #[
    39, 45, 45, 39, 40, 44,
    47, 43, 40, 40, 44, 45,
    38, 40, 40, 40, 39, 45,
    45, 39, 40, 46, 50, 42,
    40, 44, 50, 50, 44, 44,
    46, 45, 39, 39, 40, 45,
    48, 43, 40, 45, 50, 50,
    45, 47, 50, 48, 45, 45,
    38, 44, 45, 40, 43, 42,
    43, 45, 45, 40, 40, 40,
    39, 39
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5614709844114682, 23000001891807919
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    39471121383794721, 45968533182874403, 45968288834559779, 39471121383794721, 40073223733634026, 44153379935396536,
    47752551867313302, 43153396949608481, 40132247548195833, 40128827162110779, 44351079895207870, 45351079663543276,
    38128785730629360, 40073223733634026, 40914372955328926, 40073073754992653, 39471117600176402, 45968529399255195,
    45968285050940575, 39471117600176402, 40914372955328926, 46993861275503218, 50592631304240056, 42993878371929905,
    40972474743545883, 44351079895207870, 50567266810863973, 50567266672009215, 44351040554372944, 44153379935396536,
    46993861275503218, 45153231871290168, 39471121383794721, 39471117600176402, 40073073754992653, 45153231871290168,
    48752402093030934, 43153248887166620, 40132090180115791, 45351079663543276, 50567266672009215, 50567266533153431,
    45351040322679529, 47752551867313302, 50592631304240056, 48752402093030934, 45968533182874403, 45968529399255195,
    38128785730629360, 44351040554372944, 45351040322679529, 40128744298450115, 43153396949608481, 42993878371929905,
    43153248887166620, 45968288834559779, 45968285050940575, 40132247548195833, 40972474743545883, 40132090180115791,
    39471121383794721, 39471117600176402
  ]

abbrev PositiveTerm := Fin 2
abbrev NegativeTerm := Fin 62
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
noncomputable def positiveFloor : ℝ := 284310163 / 1000000000000
noncomputable def negativeCeiling : ℝ := 289213327 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 429003945689366623588188160, coefficient := (-429003945689366623588188160) }, { argument := 19379703680397046956511199232, coefficient := (-19379703680397046956511199232) }, { argument := 19376421631387700159181750272, coefficient := (-19376421631387700159181750272) }, { argument := 429003945689366623588188160, coefficient := (-429003945689366623588188160) }, { argument := 325598322450672378749911040, coefficient := (-325598322450672378749911040) }, { argument := 11014418101247546713681428480, coefficient := (-11014418101247546713681428480) }, { argument := 133481251236823744492412600320, coefficient := (-133481251236823744492412600320) }, { argument := 11014547998934701680854302720, coefficient := (-11014547998934701680854302720) }, { argument := 339195511961961624040898560, coefficient := (-339195511961961624040898560) }, { argument := 338392289265737067921408000, coefficient := (-338392289265737067921408000) }, { argument := 12632088977556496753455267840, coefficient := (-12632088977556496753455267840) }, { argument := 12632086949125372961598996480, coefficient := (-12632086949125372961598996480) }, { argument := 338382571416757001351331840, coefficient := (-338382571416757001351331840) }, { argument := 325598322450672378749911040, coefficient := (-325598322450672378749911040) }, { argument := 1166603564804394789223006208, coefficient := (-1166603564804394789223006208) }, { argument := 325564475896496755199442944, coefficient := (-325564475896496755199442944) }, { argument := 429002820583219215288238080, coefficient := (-429002820583219215288238080) }, { argument := 19379652855168130404807868416, coefficient := (-19379652855168130404807868416) }, { argument := 19376370814766288395290279936, coefficient := (-19376370814766288395290279936) }, { argument := 429002820583219215288238080, coefficient := (-429002820583219215288238080) }, { argument := 1166603564804394789223006208, coefficient := (-1166603564804394789223006208) }, { argument := 39445879292311080793844744192, coefficient := (-39445879292311080793844744192) }, { argument := 477902578800117857831226441728, coefficient := (-477902578800117857831226441728) }, { argument := 39446346741999162808229429248, coefficient := (-39446346741999162808229429248) }, { argument := 1214545187141240670774099968, coefficient := (-1214545187141240670774099968) }, { argument := 12632088977556496753455267840, coefficient := (-12632088977556496753455267840) }, { argument := 469573846870772426817237155840, coefficient := (-469573846870772426817237155840) }, { argument := 469573801675801901015865753600, coefficient := (-469573801675801901015865753600) }, { argument := 12631744517960075468257361920, coefficient := (-12631744517960075468257361920) }, { argument := 11014418101247546713681428480, coefficient := (-11014418101247546713681428480) }, { argument := 39445879292311080793844744192, coefficient := (-39445879292311080793844744192) }, { argument := 11013287747123328108279627776, coefficient := (-11013287747123328108279627776) }, { argument := 429003945689366623588188160, coefficient := (-429003945689366623588188160) }, { argument := 429002820583219215288238080, coefficient := (-429002820583219215288238080) }, { argument := 325564475896496755199442944, coefficient := (-325564475896496755199442944) }, { argument := 11013287747123328108279627776, coefficient := (-11013287747123328108279627776) }, { argument := 133467394517118254146675277824, coefficient := (-133467394517118254146675277824) }, { argument := 11013417644186453052084977664, coefficient := (-11013417644186453052084977664) }, { argument := 339158514790817683707265024, coefficient := (-339158514790817683707265024) }, { argument := 12632086949125372961598996480, coefficient := (-12632086949125372961598996480) }, { argument := 469573801675801901015865753600, coefficient := (-469573801675801901015865753600) }, { argument := 469573756480502049491742883840, coefficient := (-469573756480502049491742883840) }, { argument := 12631742489331919192703631360, coefficient := (-12631742489331919192703631360) }, { argument := 133481251236823744492412600320, coefficient := (-133481251236823744492412600320) }, { argument := 477902578800117857831226441728, coefficient := (-477902578800117857831226441728) }, { argument := 133467394517118254146675277824, coefficient := (-133467394517118254146675277824) }, { argument := 19379703680397046956511199232, coefficient := (-19379703680397046956511199232) }, { argument := 19379652855168130404807868416, coefficient := (-19379652855168130404807868416) }, { argument := 338382571416757001351331840, coefficient := (-338382571416757001351331840) }, { argument := 12631744517960075468257361920, coefficient := (-12631744517960075468257361920) }, { argument := 12631742489331919192703631360, coefficient := (-12631742489331919192703631360) }, { argument := 338372853683181675232624640, coefficient := (-338372853683181675232624640) }, { argument := 11014547998934701680854302720, coefficient := (-11014547998934701680854302720) }, { argument := 39446346741999162808229429248, coefficient := (-39446346741999162808229429248) }, { argument := 11013417644186453052084977664, coefficient := (-11013417644186453052084977664) }, { argument := 19376421631387700159181750272, coefficient := (-19376421631387700159181750272) }, { argument := 19376370814766288395290279936, coefficient := (-19376370814766288395290279936) }, { argument := 339195511961961624040898560, coefficient := (-339195511961961624040898560) }, { argument := 1214545187141240670774099968, coefficient := (-1214545187141240670774099968) }, { argument := 339158514790817683707265024, coefficient := (-339158514790817683707265024) }, { argument := 429003945689366623588188160, coefficient := (-429003945689366623588188160) }, { argument := 429002820583219215288238080, coefficient := (-429002820583219215288238080) }, { argument := 3882179963198952542083653566464, coefficient := 3882179963198952542083653566464 }, { argument := 79228266406326960725738651648, coefficient := 79228266406326960725738651648 }] }

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
def constantNumerator : ℤ := (-188992328006739490980596442726400)
def positiveArguments : Array ℕ := #[
    8388597, 33071345, 59205057, 33067917, 2746605, 204222075,
    204222055, 1373265, 384927, 6508769, 78864191, 3254423,
    400837, 90845, 8207613, 8206223, 90845
  ]
def positiveCoefficients : Array ℕ := #[
    79228058622201714461349249024, 312350022342837253779478282240, 1118351907172747473786595442688, 312317645798230699491893182464, 51881901574728727568654008320, 1928822964084181800109631078400,
    1928822775189522485323822530560, 51880484864783866675089899520, 3635532726303127846344720384, 122947170281363911231611600896, 1489702449108119712940628639744, 122948624770240635082337419264,
    3785798427788039957044527104, 1716013532545171677752852480, 77518713071130354722638135296, 77505584892307977108944060416, 1716013532545171677752852480
  ]
def positiveScales : Array ℕ := #[
    22, 24, 25, 24, 21, 27,
    27, 20, 18, 22, 26, 21,
    18, 16, 22, 22, 16
  ]
def negativeArguments : Array ℕ := #[
    1, 11, 25, 11, 1
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 1743019575313815427057966907392, 3961408125713216879677197516800, 1743019575313815427057966907392, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 3, 4, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    22999998106730062, 24979078383792910, 25819217073068199, 24978928833937918, 21389218015043217, 27605563579142401,
    27605563437855509, 20389178619642203, 18554225344338227, 22633953282372011, 26232867044379005, 21633970349633279,
    18612656159747829, 16471119491986694, 22968531275983318, 22968286927729481, 16471119491986694
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 3459431618637364, 4643856189792934, 3459431618637364, 0
  ]

abbrev PositiveTerm := Fin 17
abbrev NegativeTerm := Fin 5
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
noncomputable def positiveFloor : ℝ := 122319249 / 50000000000
noncomputable def negativeCeiling : ℝ := 366599847 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 79228058622201714461349249024, coefficient := 79228058622201714461349249024 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 312350022342837253779478282240, coefficient := 312350022342837253779478282240 }, { argument := 1118351907172747473786595442688, coefficient := 1118351907172747473786595442688 }, { argument := 312317645798230699491893182464, coefficient := 312317645798230699491893182464 }, { argument := 1743019575313815427057966907392, coefficient := (-1743019575313815427057966907392) }, { argument := 51881901574728727568654008320, coefficient := 51881901574728727568654008320 }, { argument := 1928822964084181800109631078400, coefficient := 1928822964084181800109631078400 }, { argument := 1928822775189522485323822530560, coefficient := 1928822775189522485323822530560 }, { argument := 51880484864783866675089899520, coefficient := 51880484864783866675089899520 }, { argument := 3961408125713216879677197516800, coefficient := (-3961408125713216879677197516800) }, { argument := 3635532726303127846344720384, coefficient := 3635532726303127846344720384 }, { argument := 122947170281363911231611600896, coefficient := 122947170281363911231611600896 }, { argument := 1489702449108119712940628639744, coefficient := 1489702449108119712940628639744 }, { argument := 122948624770240635082337419264, coefficient := 122948624770240635082337419264 }, { argument := 3785798427788039957044527104, coefficient := 3785798427788039957044527104 }, { argument := 1743019575313815427057966907392, coefficient := (-1743019575313815427057966907392) }, { argument := 1716013532545171677752852480, coefficient := 1716013532545171677752852480 }, { argument := 77518713071130354722638135296, coefficient := 77518713071130354722638135296 }, { argument := 77505584892307977108944060416, coefficient := 77505584892307977108944060416 }, { argument := 1716013532545171677752852480, coefficient := 1716013532545171677752852480 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk7
