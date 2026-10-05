import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 10, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-166364006289608445173960907664916480)
def positiveArguments : Array ℕ := #[
    217445, 6925, 211905, 6925, 4155, 5405,
    4025, 4255, 345, 73945, 133745, 4025,
    73945, 2185, 2185, 4255, 4255, 133745,
    4255, 5405, 345, 3, 45, 79,
    3, 25, 3, 79, 157, 25,
    2423, 155, 45, 79, 3, 155,
    3, 79, 79, 3, 7, 51640265261,
    51640276435, 105794940957, 385034595233, 52900909601, 7113262511, 280775336325,
    280775361463, 7113315605, 17602683, 404350473, 67034467047, 6469612189,
    17602683, 4647261
  ]
def positiveCoefficients : Array ℕ := #[
    4205997997537648654303751045120, 133948980813300912557444300800, 4098838812887007924257795604480, 4286367386025629201838217625600, 160738776975961095068933160960, 104547904880273131028590100480,
    77854822783182118851077734400, 82303669799363954213996462080, 106772328388364048710049464320, 1430304315702460069178370949120, 2587004539909737263537240145920, 77854822783182118851077734400,
    1430304315702460069178370949120, 84528093307454871895455825920, 84528093307454871895455825920, 82303669799363954213996462080, 82303669799363954213996462080, 2587004539909737263537240145920,
    82303669799363954213996462080, 104547904880273131028590100480, 106772328388364048710049464320, 232113757366008801543585792, 3481706360490132023153786880, 6112328943971565107314425856,
    232113757366008801543585792, 3868562622766813359059763200, 232113757366008801543585792, 6112328943971565107314425856, 6073643317743896973723828224, 3868562622766813359059763200,
    93735272349639887690018062336, 5996272065288560706542632960, 3481706360490132023153786880, 6112328943971565107314425856, 232113757366008801543585792, 5996272065288560706542632960,
    232113757366008801543585792, 6112328943971565107314425856, 6112328943971565107314425856, 232113757366008801543585792, 17747108403195211620953844875264, 243864257835044091320220470214656,
    243864310602767170905636088053760, 499602483232509867310505967747072, 1818274467273599673157755147911168, 499634964826158833033348846190592, 33591432465799570998454340550656, 1325924037477631986008920896307200,
    1325924156188480632386062278197248, 33591683195125612479397316526080, 166252640415558590038315892736, 30551857936442999032002618851328, 316561320379782522074085785075712, 30551879758498516372633151340544,
    166252640415558590038315892736, 21946069583547270285446086656
  ]
def positiveScales : Array ℕ := #[
    17, 12, 17, 12, 12, 12,
    11, 12, 8, 16, 17, 11,
    16, 11, 11, 12, 12, 17,
    12, 12, 8, 1, 5, 6,
    1, 4, 1, 6, 7, 4,
    11, 7, 5, 6, 1, 7,
    1, 6, 6, 1, 2, 35,
    35, 36, 38, 35, 32, 38,
    38, 32, 24, 28, 35, 32,
    24, 22
  ]
def negativeArguments : Array ℕ := #[
    1385, 115, 1, 7, 1539, 17781,
    34319, 4771
  ]
def negativeCoefficients : Array ℕ := #[
    109731005082256107567058371215360, 9111238689140398823257554288640, 158456325028528675187087900672, 17747108403195211620953844875264, 487728568437811262225856558268416, 2817511915332268373501609961848832,
    2719031309327037801872834831581184, 377997563355555154658798187053056
  ]
def negativeScales : Array ℕ := #[
    10, 6, 0, 2, 10, 14,
    15, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    17730291009819162, 12757598355807462, 17693058103625387, 12757598355807462, 12020632761657706, 12400078902622011,
    11974773066918090, 12054943416573324, 8430452551665529, 16174164978272322, 17029125432417593, 11974773066918090,
    16174164978272322, 11093417564387960, 11093417564387960, 12054943416573324, 12054943416573324, 17029125432417593,
    12054943416573324, 12400078902622011, 8430452551665529, 1584962500720924, 5491853096329661, 6303780748177102,
    1584962500720924, 4643856189773592, 1584962500720924, 6303780748177102, 7294620748891626, 4643856189773592,
    11242578689451346, 7276124405274237, 5491853096329661, 6303780748177102, 1584962500720924, 7276124405274237,
    1584962500720924, 6303780748177102, 6303780748177102, 1584962500720924, 2807354922011143, 35587777360241682,
    35587777672414220, 36622479684154116, 38486197121071903, 35622573477744787, 32727864260360009, 38030625256738364,
    38030625385903791, 32727875028719042, 24069292005334898, 28591031058186623, 35964184023508157, 32591032088649651,
    24069292005334898, 22147949241250869
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    10435670260936578, 6845490052533228, 0, 2807354922807594, 10587777516332228, 14118048842888769,
    15066719895205685, 12220075970984306
  ]

abbrev PositiveTerm := Fin 56
abbrev NegativeTerm := Fin 8
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
noncomputable def positiveFloor : ℝ := 1445329628663 / 500000000000
noncomputable def negativeCeiling : ℝ := 1104822765401 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4205997997537648654303751045120, coefficient := 4205997997537648654303751045120 }, { argument := 133948980813300912557444300800, coefficient := 133948980813300912557444300800 }, { argument := 4098838812887007924257795604480, coefficient := 4098838812887007924257795604480 }, { argument := 4286367386025629201838217625600, coefficient := 4286367386025629201838217625600 }, { argument := 160738776975961095068933160960, coefficient := 160738776975961095068933160960 }, { argument := 109731005082256107567058371215360, coefficient := (-109731005082256107567058371215360) }, { argument := 104547904880273131028590100480, coefficient := 104547904880273131028590100480 }, { argument := 77854822783182118851077734400, coefficient := 77854822783182118851077734400 }, { argument := 82303669799363954213996462080, coefficient := 82303669799363954213996462080 }, { argument := 106772328388364048710049464320, coefficient := 106772328388364048710049464320 }, { argument := 1430304315702460069178370949120, coefficient := 1430304315702460069178370949120 }, { argument := 2587004539909737263537240145920, coefficient := 2587004539909737263537240145920 }, { argument := 77854822783182118851077734400, coefficient := 77854822783182118851077734400 }, { argument := 1430304315702460069178370949120, coefficient := 1430304315702460069178370949120 }, { argument := 84528093307454871895455825920, coefficient := 84528093307454871895455825920 }, { argument := 84528093307454871895455825920, coefficient := 84528093307454871895455825920 }, { argument := 82303669799363954213996462080, coefficient := 82303669799363954213996462080 }, { argument := 82303669799363954213996462080, coefficient := 82303669799363954213996462080 }, { argument := 2587004539909737263537240145920, coefficient := 2587004539909737263537240145920 }, { argument := 82303669799363954213996462080, coefficient := 82303669799363954213996462080 }, { argument := 104547904880273131028590100480, coefficient := 104547904880273131028590100480 }, { argument := 106772328388364048710049464320, coefficient := 106772328388364048710049464320 }, { argument := 9111238689140398823257554288640, coefficient := (-9111238689140398823257554288640) }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 3868562622766813359059763200, coefficient := 3868562622766813359059763200 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 3868562622766813359059763200, coefficient := 3868562622766813359059763200 }, { argument := 93735272349639887690018062336, coefficient := 93735272349639887690018062336 }, { argument := 5996272065288560706542632960, coefficient := 5996272065288560706542632960 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 5996272065288560706542632960, coefficient := 5996272065288560706542632960 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 17747108403195211620953844875264, coefficient := 17747108403195211620953844875264 }, { argument := 17747108403195211620953844875264, coefficient := (-17747108403195211620953844875264) }, { argument := 243864257835044091320220470214656, coefficient := 243864257835044091320220470214656 }, { argument := 243864310602767170905636088053760, coefficient := 243864310602767170905636088053760 }, { argument := 487728568437811262225856558268416, coefficient := (-487728568437811262225856558268416) }, { argument := 499602483232509867310505967747072, coefficient := 499602483232509867310505967747072 }, { argument := 1818274467273599673157755147911168, coefficient := 1818274467273599673157755147911168 }, { argument := 499634964826158833033348846190592, coefficient := 499634964826158833033348846190592 }, { argument := 2817511915332268373501609961848832, coefficient := (-2817511915332268373501609961848832) }, { argument := 33591432465799570998454340550656, coefficient := 33591432465799570998454340550656 }, { argument := 1325924037477631986008920896307200, coefficient := 1325924037477631986008920896307200 }, { argument := 1325924156188480632386062278197248, coefficient := 1325924156188480632386062278197248 }, { argument := 33591683195125612479397316526080, coefficient := 33591683195125612479397316526080 }, { argument := 2719031309327037801872834831581184, coefficient := (-2719031309327037801872834831581184) }, { argument := 166252640415558590038315892736, coefficient := 166252640415558590038315892736 }, { argument := 30551857936442999032002618851328, coefficient := 30551857936442999032002618851328 }, { argument := 316561320379782522074085785075712, coefficient := 316561320379782522074085785075712 }, { argument := 30551879758498516372633151340544, coefficient := 30551879758498516372633151340544 }, { argument := 166252640415558590038315892736, coefficient := 166252640415558590038315892736 }, { argument := 377997563355555154658798187053056, coefficient := (-377997563355555154658798187053056) }, { argument := 21946069583547270285446086656, coefficient := 21946069583547270285446086656 }] }

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

end TermShard6


end Parent1

namespace Parent1

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-204523055290303504206414947024896)
def positiveArguments : Array ℕ := #[
    909711011, 454855511, 2323625
  ]
def positiveCoefficients : Array ℕ := #[
    4295988787443859128562699206656, 4295988839389890440128796557312, 21946017637515958719348736000
  ]
def positiveScales : Array ℕ := #[
    29, 28, 21
  ]
def negativeArguments : Array ℕ := #[
    109
  ]
def negativeCoefficients : Array ℕ := #[
    8635869714054812797696290586624
  ]
def negativeScales : Array ℕ := #[
    6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    29760833074488882, 28760833091933593, 21147945826408400
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6768184325109843
  ]

abbrev PositiveTerm := Fin 3
abbrev NegativeTerm := Fin 1
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
noncomputable def positiveFloor : ℝ := 1515902687 / 500000000000
noncomputable def negativeCeiling : ℝ := 175889037 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4295988787443859128562699206656, coefficient := 4295988787443859128562699206656 }, { argument := 4295988839389890440128796557312, coefficient := 4295988839389890440128796557312 }, { argument := 21946017637515958719348736000, coefficient := 21946017637515958719348736000 }, { argument := 8635869714054812797696290586624, coefficient := (-8635869714054812797696290586624) }] }

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

end TermShard7


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10
