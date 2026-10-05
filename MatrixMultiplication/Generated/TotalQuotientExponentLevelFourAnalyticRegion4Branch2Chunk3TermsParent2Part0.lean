import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 3, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk3

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
def constantNumerator : ℤ := 190395601242671476060339920961536
def positiveArguments : Array ℕ := #[
    49, 4194299
  ]
def positiveCoefficients : Array ℕ := #[
    3882179963198952542083653566464, 79228068066934680200639676416
  ]
def positiveScales : Array ℕ := #[
    5, 21
  ]
def negativeArguments : Array ℕ := #[
    727060760155, 17228599041277, 34448008373445, 368196537715, 76730593325, 39724011678585,
    476556273673415, 39724246711865, 1276265918135, 1207426879675, 22454756212125, 5613693434475,
    1207432585395, 76730593325, 2176205677557, 614239640227, 727062493605, 17228640117507,
    34448090503995, 368197415565, 2176205677557, 140772984737697, 1688407699531559, 35193455799089,
    2261194803781, 22454756212125, 1668190726650165, 1668191949889305, 5613709311375, 39724011678585,
    140772984737697, 19875251790451, 727060760155, 727062493605, 614239640227, 19875251790451,
    238440053897737, 39750738711811, 1277118545087, 5613693434475, 1668191949889305, 417048293282415,
    44909709542355, 476556273673415, 1688407699531559, 238440053897737, 17228599041277, 17228640117507,
    1207432585395, 5613709311375, 44909709542355, 603719145345, 39724246711865, 35193455799089,
    39750738711811, 34448008373445, 34448090503995, 1276265918135, 2261194803781, 1277118545087,
    368196537715, 368197415565
  ]
def negativeCoefficients : Array ℕ := #[
    409298821063720945697423360, 19397678055602695458518990848, 19392504709287828501917859840, 414552447513095194185564160, 345563871506387067679539200, 11181315262083539832416501760,
    134138666033541494186694410240, 11181381418070554061507133440, 359236919583653122078146560, 339860452836340669402316800, 12640903963702685029367808000, 12640913829836904951762124800,
    339862058853744786926469120, 345563871506387067679539200, 1225094884815907871243894784, 345786176855313090634317824, 409299796909317703870709760, 19397724303326225904716218368,
    19392550944677125468654141440, 414553435884328415983042560, 1225094884815907871243894784, 39624072600532795612024799232, 475244517903737842885883592704, 39624308605664310484885569536,
    1272939509465026677463580672, 12640903963702685029367808000, 469553945932787502809339658240, 469554290243995945872213934080, 12640949581437366851076096000, 11181315262083539832416501760,
    39624072600532795612024799232, 11188772069671238381141491712, 409298821063720945697423360, 409299796909317703870709760, 345786176855313090634317824, 11188772069671238381141491712,
    134229817235506166944124370944, 11188838253138373111516758016, 359476912735110199689347072, 12640913829836904951762124800, 469554290243995945872213934080, 469554634555546381031791656960,
    12640959447516699153011834880, 134138666033541494186694410240, 475244517903737842885883592704, 134229817235506166944124370944, 19397678055602695458518990848, 19397724303326225904716218368,
    339862058853744786926469120, 12640949581437366851076096000, 12640959447516699153011834880, 339863664751522039348592640, 11181381418070554061507133440, 39624308605664310484885569536,
    11188838253138373111516758016, 19392504709287828501917859840, 19392550944677125468654141440, 359236919583653122078146560, 1272939509465026677463580672, 359476912735110199689347072,
    414552447513095194185564160, 414553435884328415983042560
  ]
def negativeScales : Array ℕ := #[
    39, 43, 44, 38, 36, 45,
    48, 45, 40, 40, 44, 42,
    40, 36, 40, 39, 39, 43,
    44, 38, 40, 47, 50, 45,
    41, 44, 50, 50, 42, 45,
    47, 44, 39, 39, 39, 44,
    47, 45, 40, 42, 50, 48,
    45, 48, 50, 47, 43, 43,
    40, 42, 45, 39, 45, 45,
    45, 44, 44, 40, 41, 40,
    38, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5614709844114682, 21999998278712924
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    39403284978347973, 43969870640372546, 44969485823268377, 38421685104330178, 36159082859563666, 45175076559739049,
    48759639912103107, 45175085095642903, 40215066093773921, 40135072962471811, 44352086292617459, 42352087418630076,
    40135079779940130, 36159082859563666, 40984952072265905, 39160010664042084, 39403288418000991, 43969874080026388,
    44969489262922214, 38421688543983195, 40984952072265905, 47000363826286973, 50584584736762068, 45000372419104332,
    41040222425449170, 44352086292617459, 50567205666928577, 50567206724817442, 42352091498919242, 45175076559739049,
    47000363826286973, 44176038370890391, 39403284978347973, 39403288418000991, 39160010664042084, 44176038370890391,
    47760619933238928, 45176046904648772, 40216029584183466, 42352087418630076, 50567206724817442, 48567207782706582,
    45352092624921532, 48759639912103107, 50584584736762068, 47760619933238928, 43969870640372546, 43969874080026388,
    40135079779940130, 42352091498919242, 45352092624921532, 39135086596868426, 45175085095642903, 45000372419104332,
    45176046904648772, 44969485823268377, 44969489262922214, 40215066093773921, 41040222425449170, 40216029584183466,
    38421685104330178, 38421688543983195
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
noncomputable def positiveFloor : ℝ := 17709777 / 62500000000
noncomputable def negativeCeiling : ℝ := 2300733901 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 409298821063720945697423360, coefficient := (-409298821063720945697423360) }, { argument := 19397678055602695458518990848, coefficient := (-19397678055602695458518990848) }, { argument := 19392504709287828501917859840, coefficient := (-19392504709287828501917859840) }, { argument := 414552447513095194185564160, coefficient := (-414552447513095194185564160) }, { argument := 345563871506387067679539200, coefficient := (-345563871506387067679539200) }, { argument := 11181315262083539832416501760, coefficient := (-11181315262083539832416501760) }, { argument := 134138666033541494186694410240, coefficient := (-134138666033541494186694410240) }, { argument := 11181381418070554061507133440, coefficient := (-11181381418070554061507133440) }, { argument := 359236919583653122078146560, coefficient := (-359236919583653122078146560) }, { argument := 339860452836340669402316800, coefficient := (-339860452836340669402316800) }, { argument := 12640903963702685029367808000, coefficient := (-12640903963702685029367808000) }, { argument := 12640913829836904951762124800, coefficient := (-12640913829836904951762124800) }, { argument := 339862058853744786926469120, coefficient := (-339862058853744786926469120) }, { argument := 345563871506387067679539200, coefficient := (-345563871506387067679539200) }, { argument := 1225094884815907871243894784, coefficient := (-1225094884815907871243894784) }, { argument := 345786176855313090634317824, coefficient := (-345786176855313090634317824) }, { argument := 409299796909317703870709760, coefficient := (-409299796909317703870709760) }, { argument := 19397724303326225904716218368, coefficient := (-19397724303326225904716218368) }, { argument := 19392550944677125468654141440, coefficient := (-19392550944677125468654141440) }, { argument := 414553435884328415983042560, coefficient := (-414553435884328415983042560) }, { argument := 1225094884815907871243894784, coefficient := (-1225094884815907871243894784) }, { argument := 39624072600532795612024799232, coefficient := (-39624072600532795612024799232) }, { argument := 475244517903737842885883592704, coefficient := (-475244517903737842885883592704) }, { argument := 39624308605664310484885569536, coefficient := (-39624308605664310484885569536) }, { argument := 1272939509465026677463580672, coefficient := (-1272939509465026677463580672) }, { argument := 12640903963702685029367808000, coefficient := (-12640903963702685029367808000) }, { argument := 469553945932787502809339658240, coefficient := (-469553945932787502809339658240) }, { argument := 469554290243995945872213934080, coefficient := (-469554290243995945872213934080) }, { argument := 12640949581437366851076096000, coefficient := (-12640949581437366851076096000) }, { argument := 11181315262083539832416501760, coefficient := (-11181315262083539832416501760) }, { argument := 39624072600532795612024799232, coefficient := (-39624072600532795612024799232) }, { argument := 11188772069671238381141491712, coefficient := (-11188772069671238381141491712) }, { argument := 409298821063720945697423360, coefficient := (-409298821063720945697423360) }, { argument := 409299796909317703870709760, coefficient := (-409299796909317703870709760) }, { argument := 345786176855313090634317824, coefficient := (-345786176855313090634317824) }, { argument := 11188772069671238381141491712, coefficient := (-11188772069671238381141491712) }, { argument := 134229817235506166944124370944, coefficient := (-134229817235506166944124370944) }, { argument := 11188838253138373111516758016, coefficient := (-11188838253138373111516758016) }, { argument := 359476912735110199689347072, coefficient := (-359476912735110199689347072) }, { argument := 12640913829836904951762124800, coefficient := (-12640913829836904951762124800) }, { argument := 469554290243995945872213934080, coefficient := (-469554290243995945872213934080) }, { argument := 469554634555546381031791656960, coefficient := (-469554634555546381031791656960) }, { argument := 12640959447516699153011834880, coefficient := (-12640959447516699153011834880) }, { argument := 134138666033541494186694410240, coefficient := (-134138666033541494186694410240) }, { argument := 475244517903737842885883592704, coefficient := (-475244517903737842885883592704) }, { argument := 134229817235506166944124370944, coefficient := (-134229817235506166944124370944) }, { argument := 19397678055602695458518990848, coefficient := (-19397678055602695458518990848) }, { argument := 19397724303326225904716218368, coefficient := (-19397724303326225904716218368) }, { argument := 339862058853744786926469120, coefficient := (-339862058853744786926469120) }, { argument := 12640949581437366851076096000, coefficient := (-12640949581437366851076096000) }, { argument := 12640959447516699153011834880, coefficient := (-12640959447516699153011834880) }, { argument := 339863664751522039348592640, coefficient := (-339863664751522039348592640) }, { argument := 11181381418070554061507133440, coefficient := (-11181381418070554061507133440) }, { argument := 39624308605664310484885569536, coefficient := (-39624308605664310484885569536) }, { argument := 11188838253138373111516758016, coefficient := (-11188838253138373111516758016) }, { argument := 19392504709287828501917859840, coefficient := (-19392504709287828501917859840) }, { argument := 19392550944677125468654141440, coefficient := (-19392550944677125468654141440) }, { argument := 359236919583653122078146560, coefficient := (-359236919583653122078146560) }, { argument := 1272939509465026677463580672, coefficient := (-1272939509465026677463580672) }, { argument := 359476912735110199689347072, coefficient := (-359476912735110199689347072) }, { argument := 414552447513095194185564160, coefficient := (-414552447513095194185564160) }, { argument := 414553435884328415983042560, coefficient := (-414553435884328415983042560) }, { argument := 3882179963198952542083653566464, coefficient := 3882179963198952542083653566464 }, { argument := 79228068066934680200639676416, coefficient := 79228068066934680200639676416 }] }

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
def constantNumerator : ℤ := (-187949339241233103183278241742848)
def positiveArguments : Array ℕ := #[
    4194309, 8322425, 58973709, 16656129, 2748785, 204217545,
    204217695, 2748795, 405823, 6563887, 78733089, 3281963,
    421749, 173345, 4107623, 8213055, 87785
  ]
def positiveCoefficients : Array ℕ := #[
    79228256961593994986448224256, 314412327009571256540751462400, 1113981867008431767063002873856, 314625381295812403454212571136, 51923080610459350874917437440, 1928780179443847001123994992640,
    1928781596153791862017559101440, 51923269505118665660725985280, 3832889866355216059115503616, 123988319864575147651165585408, 1487226002345571008033404747776, 123989056553746475315818921984,
    3983306683567579998462148608, 1637197235946077299136266240, 77590804717857842726470418432, 77570111307929907941144002560, 1658211766794847220337213440
  ]
def positiveScales : Array ℕ := #[
    22, 22, 25, 23, 21, 27,
    27, 21, 18, 22, 26, 21,
    18, 17, 21, 22, 16
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
    22000001719825483, 22988572532258839, 25813568595772280, 23989549810294250, 21390362638210677, 27605531577308028,
    27605532636982781, 21390367886683791, 18630491106523261, 22646118971803046, 26230466745987046, 21646127543696413,
    18686025122207242, 17403286698175498, 21969872344780066, 22969487527773511, 16421686824157693
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
noncomputable def positiveFloor : ℝ := 2433607207 / 1000000000000
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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 79228256961593994986448224256, coefficient := 79228256961593994986448224256 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 314412327009571256540751462400, coefficient := 314412327009571256540751462400 }, { argument := 1113981867008431767063002873856, coefficient := 1113981867008431767063002873856 }, { argument := 314625381295812403454212571136, coefficient := 314625381295812403454212571136 }, { argument := 1743019575313815427057966907392, coefficient := (-1743019575313815427057966907392) }, { argument := 51923080610459350874917437440, coefficient := 51923080610459350874917437440 }, { argument := 1928780179443847001123994992640, coefficient := 1928780179443847001123994992640 }, { argument := 1928781596153791862017559101440, coefficient := 1928781596153791862017559101440 }, { argument := 51923269505118665660725985280, coefficient := 51923269505118665660725985280 }, { argument := 3961408125713216879677197516800, coefficient := (-3961408125713216879677197516800) }, { argument := 3832889866355216059115503616, coefficient := 3832889866355216059115503616 }, { argument := 123988319864575147651165585408, coefficient := 123988319864575147651165585408 }, { argument := 1487226002345571008033404747776, coefficient := 1487226002345571008033404747776 }, { argument := 123989056553746475315818921984, coefficient := 123989056553746475315818921984 }, { argument := 3983306683567579998462148608, coefficient := 3983306683567579998462148608 }, { argument := 1743019575313815427057966907392, coefficient := (-1743019575313815427057966907392) }, { argument := 1637197235946077299136266240, coefficient := 1637197235946077299136266240 }, { argument := 77590804717857842726470418432, coefficient := 77590804717857842726470418432 }, { argument := 77570111307929907941144002560, coefficient := 77570111307929907941144002560 }, { argument := 1658211766794847220337213440, coefficient := 1658211766794847220337213440 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk3
