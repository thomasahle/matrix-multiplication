import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
parent chunk 16, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-650442114028643976534952127758336)
def positiveArguments : Array ℕ := #[
    1131, 1131, 1131, 1131, 1131, 1305,
    1363, 715, 3003, 13013, 429, 429,
    1001, 13013, 13013, 429, 160589, 6435,
    3003, 13013, 1001, 6435, 1001, 13013,
    13013, 429, 115, 2185, 3335, 34385,
    1035, 3335, 1035, 1035, 88665, 1035,
    34385, 88665, 115, 1035, 1035, 2185,
    15, 267, 15, 475, 811, 15,
    811, 811, 267, 15, 21056371, 75327777,
    5264091, 400867, 14803485, 118427851, 3206965
  ]
def positiveCoefficients : Array ℕ := #[
    350027546107941272727727374336, 350027546107941272727727374336, 350027546107941272727727374336, 11200881475454120727287275978752, 350027546107941272727727374336, 403877937816855314685839278080,
    421828068386493328671876579328, 110640891011130862069109227520, 1858766968986998482761035022336, 4027328432805163379315575881728, 132769069213357034482931073024, 2124305107413712551726897168384,
    154897247415583206896752918528, 4027328432805163379315575881728, 4027328432805163379315575881728, 2124305107413712551726897168384, 49699888242199983241443865001984, 3983072076400711034487932190720,
    1858766968986998482761035022336, 4027328432805163379315575881728, 154897247415583206896752918528, 3983072076400711034487932190720, 154897247415583206896752918528, 4027328432805163379315575881728,
    4027328432805163379315575881728, 132769069213357034482931073024, 71181552258909365806699642880, 84528093307454871895455825920, 64508281734636612762321551360, 665102628919184386756349788160,
    80079246291273036532537098240, 64508281734636612762321551360, 80079246291273036532537098240, 80079246291273036532537098240, 3430061049476195064810339041280, 80079246291273036532537098240,
    665102628919184386756349788160, 3430061049476195064810339041280, 71181552258909365806699642880, 80079246291273036532537098240, 80079246291273036532537098240, 84528093307454871895455825920,
    1160568786830044007717928960, 20658124405574783337379135488, 1160568786830044007717928960, 18375672458142363455533875200, 31374042870638856341974679552, 1160568786830044007717928960,
    31374042870638856341974679552, 31374042870638856341974679552, 20658124405574783337379135488, 1160568786830044007717928960, 198871801322536788515914514432, 711450738667757909452819267584,
    198871735209406028340881522688, 484618466531457553376940654592, 17896315236777868768325255823360, 17896310854421772665294497513472, 484622848887553656407698964480
  ]
def positiveScales : Array ℕ := #[
    10, 10, 10, 10, 10, 10,
    10, 9, 11, 13, 8, 8,
    9, 13, 13, 8, 17, 12,
    11, 13, 9, 12, 9, 13,
    13, 8, 6, 11, 11, 15,
    10, 11, 10, 10, 16, 10,
    15, 16, 6, 10, 10, 11,
    3, 8, 3, 8, 9, 3,
    9, 9, 8, 3, 24, 26,
    22, 18, 23, 26, 21
  ]
def negativeArguments : Array ℕ := #[
    29, 143, 115, 1, 7
  ]
def negativeCoefficients : Array ℕ := #[
    36761867406618652643404392955904, 90637017916318402207014279184384, 9111238689140398823257554288640, 158456325028528675187087900672, 1109194275199700726309615304704
  ]
def negativeScales : Array ℕ := #[
    4, 7, 6, 0, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10143383213989820, 10143383213989820, 10143383213989820, 10143383213989820, 10143383213989820, 10349834091457246,
    10412569846805208, 9481799431665742, 11552188759557060, 13667665976975023, 8744833837487090, 8744833837487090,
    9967226257978146, 13667665976975023, 13667665976975023, 8744833837487090, 17293013549178990, 12651724433106680,
    11552188759557060, 13667665976975023, 9967226257978146, 12651724433106680, 9967226257978146, 13667665976975023,
    13667665976975023, 8744833837487090, 6845490050846035, 11093417564387960, 11703471046067071, 15069491725142480,
    10015415052386687, 11703471046067071, 10015415052386687, 10015415052386687, 16436077100859407, 10015415052386687,
    15069491725142480, 16436077100859407, 6845490050846035, 10015415052386687, 10015415052386687, 11093417564387960,
    3906890595303263, 8060695931687553, 3906890595303263, 8891783702985444, 9663558104215410, 3906890595303263,
    9663558104215410, 9663558104215410, 8060695931687553, 3906890595303263, 24327753477999572, 26166678618759176,
    22327752998388580, 18612764131895271, 23819433515706322, 26819433162426661, 21612777177982569
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    4857980997143165, 7159871336778390, 6845490052533228, 0, 2807354922807594
  ]

abbrev PositiveTerm := Fin 59
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
noncomputable def positiveFloor : ℝ := 7860308243 / 250000000000
noncomputable def negativeCeiling : ℝ := 1074936897 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 350027546107941272727727374336, coefficient := 350027546107941272727727374336 }, { argument := 350027546107941272727727374336, coefficient := 350027546107941272727727374336 }, { argument := 350027546107941272727727374336, coefficient := 350027546107941272727727374336 }, { argument := 11200881475454120727287275978752, coefficient := 11200881475454120727287275978752 }, { argument := 350027546107941272727727374336, coefficient := 350027546107941272727727374336 }, { argument := 403877937816855314685839278080, coefficient := 403877937816855314685839278080 }, { argument := 421828068386493328671876579328, coefficient := 421828068386493328671876579328 }, { argument := 36761867406618652643404392955904, coefficient := (-36761867406618652643404392955904) }, { argument := 110640891011130862069109227520, coefficient := 110640891011130862069109227520 }, { argument := 1858766968986998482761035022336, coefficient := 1858766968986998482761035022336 }, { argument := 4027328432805163379315575881728, coefficient := 4027328432805163379315575881728 }, { argument := 132769069213357034482931073024, coefficient := 132769069213357034482931073024 }, { argument := 2124305107413712551726897168384, coefficient := 2124305107413712551726897168384 }, { argument := 154897247415583206896752918528, coefficient := 154897247415583206896752918528 }, { argument := 4027328432805163379315575881728, coefficient := 4027328432805163379315575881728 }, { argument := 4027328432805163379315575881728, coefficient := 4027328432805163379315575881728 }, { argument := 2124305107413712551726897168384, coefficient := 2124305107413712551726897168384 }, { argument := 49699888242199983241443865001984, coefficient := 49699888242199983241443865001984 }, { argument := 3983072076400711034487932190720, coefficient := 3983072076400711034487932190720 }, { argument := 1858766968986998482761035022336, coefficient := 1858766968986998482761035022336 }, { argument := 4027328432805163379315575881728, coefficient := 4027328432805163379315575881728 }, { argument := 154897247415583206896752918528, coefficient := 154897247415583206896752918528 }, { argument := 3983072076400711034487932190720, coefficient := 3983072076400711034487932190720 }, { argument := 154897247415583206896752918528, coefficient := 154897247415583206896752918528 }, { argument := 4027328432805163379315575881728, coefficient := 4027328432805163379315575881728 }, { argument := 4027328432805163379315575881728, coefficient := 4027328432805163379315575881728 }, { argument := 132769069213357034482931073024, coefficient := 132769069213357034482931073024 }, { argument := 90637017916318402207014279184384, coefficient := (-90637017916318402207014279184384) }, { argument := 71181552258909365806699642880, coefficient := 71181552258909365806699642880 }, { argument := 84528093307454871895455825920, coefficient := 84528093307454871895455825920 }, { argument := 64508281734636612762321551360, coefficient := 64508281734636612762321551360 }, { argument := 665102628919184386756349788160, coefficient := 665102628919184386756349788160 }, { argument := 80079246291273036532537098240, coefficient := 80079246291273036532537098240 }, { argument := 64508281734636612762321551360, coefficient := 64508281734636612762321551360 }, { argument := 80079246291273036532537098240, coefficient := 80079246291273036532537098240 }, { argument := 80079246291273036532537098240, coefficient := 80079246291273036532537098240 }, { argument := 3430061049476195064810339041280, coefficient := 3430061049476195064810339041280 }, { argument := 80079246291273036532537098240, coefficient := 80079246291273036532537098240 }, { argument := 665102628919184386756349788160, coefficient := 665102628919184386756349788160 }, { argument := 3430061049476195064810339041280, coefficient := 3430061049476195064810339041280 }, { argument := 71181552258909365806699642880, coefficient := 71181552258909365806699642880 }, { argument := 80079246291273036532537098240, coefficient := 80079246291273036532537098240 }, { argument := 80079246291273036532537098240, coefficient := 80079246291273036532537098240 }, { argument := 84528093307454871895455825920, coefficient := 84528093307454871895455825920 }, { argument := 9111238689140398823257554288640, coefficient := (-9111238689140398823257554288640) }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 20658124405574783337379135488, coefficient := 20658124405574783337379135488 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 18375672458142363455533875200, coefficient := 18375672458142363455533875200 }, { argument := 31374042870638856341974679552, coefficient := 31374042870638856341974679552 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 31374042870638856341974679552, coefficient := 31374042870638856341974679552 }, { argument := 31374042870638856341974679552, coefficient := 31374042870638856341974679552 }, { argument := 20658124405574783337379135488, coefficient := 20658124405574783337379135488 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 198871801322536788515914514432, coefficient := 198871801322536788515914514432 }, { argument := 711450738667757909452819267584, coefficient := 711450738667757909452819267584 }, { argument := 198871735209406028340881522688, coefficient := 198871735209406028340881522688 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 484618466531457553376940654592, coefficient := 484618466531457553376940654592 }, { argument := 17896315236777868768325255823360, coefficient := 17896315236777868768325255823360 }, { argument := 17896310854421772665294497513472, coefficient := 17896310854421772665294497513472 }, { argument := 484622848887553656407698964480, coefficient := 484622848887553656407698964480 }] }

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

end TermShard8


end Parent3

namespace Parent3

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-6029820005122675267289631841845248)
def positiveArguments : Array ℕ := #[
    313313, 50019541, 1996479199, 50019541, 1253109, 5668695,
    476676265, 238338075, 2834405, 1435659, 6952949, 1435659
  ]
def positiveCoefficients : Array ℕ := #[
    47346521915114788826839515136, 7558739325021568525501466673152, 75424851624832291981231791276032, 7558739325021568525501466673152, 47341119527858385952715046912, 53539310539221486949304893440,
    4502080034030977924679472250880, 4502078947886686864661073100800, 53540396683512546967704043520, 13559415884860303955699171328, 131337493258808067275689558016, 13559415884860303955699171328
  ]
def positiveScales : Array ℕ := #[
    18, 25, 30, 25, 20, 22,
    28, 27, 21, 20, 22, 20
  ]
def negativeArguments : Array ℕ := #[
    29, 143, 115, 1
  ]
def negativeCoefficients : Array ℕ := #[
    36761867406618652643404392955904, 90637017916318402207014279184384, 9111238689140398823257554288640, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    4, 7, 6, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    18257245105768611, 25575988483024481, 30894810894578857, 25575988483024481, 20257080480328724, 22434585217415222,
    28828434550537597, 27828434202481774, 21434614484865108, 20453281687963018, 22729193576691355, 20453281687963018
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    4857980997143165, 7159871336778390, 6845490052533228, 0
  ]

abbrev PositiveTerm := Fin 12
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 35866433733 / 1000000000000
noncomputable def negativeCeiling : ℝ := 5355943369 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 36761867406618652643404392955904, coefficient := (-36761867406618652643404392955904) }, { argument := 47346521915114788826839515136, coefficient := 47346521915114788826839515136 }, { argument := 7558739325021568525501466673152, coefficient := 7558739325021568525501466673152 }, { argument := 75424851624832291981231791276032, coefficient := 75424851624832291981231791276032 }, { argument := 7558739325021568525501466673152, coefficient := 7558739325021568525501466673152 }, { argument := 47341119527858385952715046912, coefficient := 47341119527858385952715046912 }, { argument := 90637017916318402207014279184384, coefficient := (-90637017916318402207014279184384) }, { argument := 53539310539221486949304893440, coefficient := 53539310539221486949304893440 }, { argument := 4502080034030977924679472250880, coefficient := 4502080034030977924679472250880 }, { argument := 4502078947886686864661073100800, coefficient := 4502078947886686864661073100800 }, { argument := 53540396683512546967704043520, coefficient := 53540396683512546967704043520 }, { argument := 9111238689140398823257554288640, coefficient := (-9111238689140398823257554288640) }, { argument := 13559415884860303955699171328, coefficient := 13559415884860303955699171328 }, { argument := 131337493258808067275689558016, coefficient := 131337493258808067275689558016 }, { argument := 13559415884860303955699171328, coefficient := 13559415884860303955699171328 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end TermShard9


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16
