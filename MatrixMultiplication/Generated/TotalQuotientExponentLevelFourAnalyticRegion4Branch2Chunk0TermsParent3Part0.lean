import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 0, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk0

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 475368975085586025561263702016
def positiveArguments : Array ℕ := #[
    1, 755715, 10728723, 3025633, 84047, 8220507,
    4110255, 168105, 39217, 151941, 222933, 1215537,
    19611
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 28550105492814671461346181120, 101329923798385337212040380416, 28576295737328666513701339136, 3175205886285960570204061696, 155280986915981194266817855488,
    155281043584378988702560419840, 3175413670411206834593464320, 370394092717397752691032064, 11480337372379148214626942976, 134754729872074062902385967104, 11480422374975839868240789504,
    370441316382226449143169024
  ]
def positiveScales : Array ℕ := #[
    0, 19, 23, 21, 16, 22,
    21, 17, 15, 17, 17, 20,
    14
  ]
def negativeArguments : Array ℕ := #[
    29636875155, 114824092815, 168473812095, 918599543955, 14820326865, 7063898209,
    690908951829, 345454601985, 14128720935, 29636875155, 420748329891, 118656249361,
    420748329891, 1630132901343, 2391786404559, 13041159769251, 210400986753, 690908951829,
    67576735337049, 33788379999285, 1381908329235, 114824092815, 1630132901343, 459717703653,
    118656249361, 459717703653, 674513441589, 3677768859921, 59335688763, 345454601985,
    33788379999285, 16894196165025, 690954416775, 168473812095, 2391786404559, 674513441589,
    14128720935, 1381908329235, 690954416775, 28259291025, 918599543955, 13041159769251,
    3677768859921, 14820326865, 210400986753, 59335688763, 1, 1,
    1
  ]
def negativeCoefficients : Array ℕ := #[
    33368154976120977720606720, 1034243483229578494193172480, 12139817557963663392815185920, 1034251140964611390355537920, 33372409273361475588587520, 15906484670917757036920832,
    777894324501006092699959296, 777894608386534503906017280, 15907525584521931459133440, 33368154976120977720606720, 118430126357116632743018496, 33398765025461265881890816,
    118430126357116632743018496, 3670732963526360159238488064, 43086593441286923180945965056, 3670760142329869199952838656, 118445225692399433139879936, 777894324501006092699959296,
    38042320010356063227019788288, 38042333893558161475727523840, 777945229575366337961656320, 1034243483229578494193172480, 3670732963526360159238488064, 1035192239433635453881810944,
    33398765025461265881890816, 1035192239433635453881810944, 12150953936786444877431832576, 1035199904193439343812018176, 33403023225352315843117056, 777894608386534503906017280,
    38042333893558161475727523840, 38042347776765326274016051200, 777945513479472097630617600, 12139817557963663392815185920, 43086593441286923180945965056, 12150953936786444877431832576,
    15907525584521931459133440, 777945229575366337961656320, 777945513479472097630617600, 15908566566243050245324800, 1034251140964611390355537920, 3670760142329869199952838656,
    1035199904193439343812018176, 33372409273361475588587520, 118445225692399433139879936, 33403023225352315843117056, 158456325028528675187087900672, 316912650057057350374175801344,
    158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    34, 36, 37, 39, 33, 32,
    39, 38, 33, 34, 38, 36,
    38, 40, 41, 43, 37, 39,
    45, 44, 40, 36, 40, 38,
    36, 38, 39, 41, 35, 38,
    44, 43, 39, 37, 41, 39,
    33, 40, 39, 34, 39, 43,
    41, 33, 37, 35, 0, 0,
    0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 19527482733211083, 23354975031899148, 21528805573008920, 16358908703920281, 22970795943322402,
    21970796469820861, 17359003110182379, 15259191556827033, 17213151695924778, 17766250663973315, 20213162377873116,
    14259375482558218
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    34786674290529285, 36740634429318908, 37293733397204250, 39740645111267290, 33786858216262349, 32717817407950029,
    39329704648152544, 38329705174651011, 33717911814212364, 34786674290529285, 38614166588734512, 36787997130340787,
    38614166588734512, 40568126727826209, 41121225695892273, 43568137409774548, 37614350514465739, 39329704648152544,
    45941591897502483, 44941592424001031, 40329799054414642, 36740634429318908, 40568126727826209, 38741957269122184,
    36787997130340787, 38741957269122184, 39295056237002089, 41741967951070566, 35788181056073899, 38329705174651011,
    44941592424001031, 43941592950499579, 39329799580913109, 37293733397204250, 41121225695892273, 39295056237002089,
    33717911814212364, 40329799054414642, 39329799580913109, 34718006220474698, 39740645111267290, 43568137409774548,
    41741967951070566, 33786858216262349, 37614350514465739, 35788181056073899, 0, 0,
    0
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
noncomputable def positiveFloor : ℝ := 162014197 / 1000000000000
noncomputable def negativeCeiling : ℝ := 81007099 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 33368154976120977720606720, coefficient := (-33368154976120977720606720) }, { argument := 1034243483229578494193172480, coefficient := (-1034243483229578494193172480) }, { argument := 12139817557963663392815185920, coefficient := (-12139817557963663392815185920) }, { argument := 1034251140964611390355537920, coefficient := (-1034251140964611390355537920) }, { argument := 33372409273361475588587520, coefficient := (-33372409273361475588587520) }, { argument := 15906484670917757036920832, coefficient := (-15906484670917757036920832) }, { argument := 777894324501006092699959296, coefficient := (-777894324501006092699959296) }, { argument := 777894608386534503906017280, coefficient := (-777894608386534503906017280) }, { argument := 15907525584521931459133440, coefficient := (-15907525584521931459133440) }, { argument := 33368154976120977720606720, coefficient := (-33368154976120977720606720) }, { argument := 118430126357116632743018496, coefficient := (-118430126357116632743018496) }, { argument := 33398765025461265881890816, coefficient := (-33398765025461265881890816) }, { argument := 118430126357116632743018496, coefficient := (-118430126357116632743018496) }, { argument := 3670732963526360159238488064, coefficient := (-3670732963526360159238488064) }, { argument := 43086593441286923180945965056, coefficient := (-43086593441286923180945965056) }, { argument := 3670760142329869199952838656, coefficient := (-3670760142329869199952838656) }, { argument := 118445225692399433139879936, coefficient := (-118445225692399433139879936) }, { argument := 777894324501006092699959296, coefficient := (-777894324501006092699959296) }, { argument := 38042320010356063227019788288, coefficient := (-38042320010356063227019788288) }, { argument := 38042333893558161475727523840, coefficient := (-38042333893558161475727523840) }, { argument := 777945229575366337961656320, coefficient := (-777945229575366337961656320) }, { argument := 1034243483229578494193172480, coefficient := (-1034243483229578494193172480) }, { argument := 3670732963526360159238488064, coefficient := (-3670732963526360159238488064) }, { argument := 1035192239433635453881810944, coefficient := (-1035192239433635453881810944) }, { argument := 33398765025461265881890816, coefficient := (-33398765025461265881890816) }, { argument := 1035192239433635453881810944, coefficient := (-1035192239433635453881810944) }, { argument := 12150953936786444877431832576, coefficient := (-12150953936786444877431832576) }, { argument := 1035199904193439343812018176, coefficient := (-1035199904193439343812018176) }, { argument := 33403023225352315843117056, coefficient := (-33403023225352315843117056) }, { argument := 777894608386534503906017280, coefficient := (-777894608386534503906017280) }, { argument := 38042333893558161475727523840, coefficient := (-38042333893558161475727523840) }, { argument := 38042347776765326274016051200, coefficient := (-38042347776765326274016051200) }, { argument := 777945513479472097630617600, coefficient := (-777945513479472097630617600) }, { argument := 12139817557963663392815185920, coefficient := (-12139817557963663392815185920) }, { argument := 43086593441286923180945965056, coefficient := (-43086593441286923180945965056) }, { argument := 12150953936786444877431832576, coefficient := (-12150953936786444877431832576) }, { argument := 15907525584521931459133440, coefficient := (-15907525584521931459133440) }, { argument := 777945229575366337961656320, coefficient := (-777945229575366337961656320) }, { argument := 777945513479472097630617600, coefficient := (-777945513479472097630617600) }, { argument := 15908566566243050245324800, coefficient := (-15908566566243050245324800) }, { argument := 1034251140964611390355537920, coefficient := (-1034251140964611390355537920) }, { argument := 3670760142329869199952838656, coefficient := (-3670760142329869199952838656) }, { argument := 1035199904193439343812018176, coefficient := (-1035199904193439343812018176) }, { argument := 33372409273361475588587520, coefficient := (-33372409273361475588587520) }, { argument := 118445225692399433139879936, coefficient := (-118445225692399433139879936) }, { argument := 33403023225352315843117056, coefficient := (-33403023225352315843117056) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 28550105492814671461346181120, coefficient := 28550105492814671461346181120 }, { argument := 101329923798385337212040380416, coefficient := 101329923798385337212040380416 }, { argument := 28576295737328666513701339136, coefficient := 28576295737328666513701339136 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 3175205886285960570204061696, coefficient := 3175205886285960570204061696 }, { argument := 155280986915981194266817855488, coefficient := 155280986915981194266817855488 }, { argument := 155281043584378988702560419840, coefficient := 155281043584378988702560419840 }, { argument := 3175413670411206834593464320, coefficient := 3175413670411206834593464320 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 370394092717397752691032064, coefficient := 370394092717397752691032064 }, { argument := 11480337372379148214626942976, coefficient := 11480337372379148214626942976 }, { argument := 134754729872074062902385967104, coefficient := 134754729872074062902385967104 }, { argument := 11480422374975839868240789504, coefficient := 11480422374975839868240789504 }, { argument := 370441316382226449143169024, coefficient := 370441316382226449143169024 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk0
