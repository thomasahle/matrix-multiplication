import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 15, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-6196554312484129843816215022141440)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    114255889305, 1162251, 65295, 196524807015, 3530283, 114255889305,
    3530283, 3530283, 1162251, 65295, 2015900415, 73056898305,
    584455401225, 16126988535, 8024662605, 316395, 17775, 13777158507,
    961035, 8024662605, 961035, 961035, 316395, 17775,
    11155278373, 11155273179, 6772363280849, 24647417759241, 4038110531, 15428922398656273,
    133124523, 310623887, 4038110531, 4038110531, 133124523, 49832946443,
    1996867845, 24647418145289, 4038110531, 310623887, 1996867845, 310623887,
    4038110531, 4038110531, 14271133774029, 196976125915235, 2403568153, 7190082561747869,
    37824572513, 1138532283, 14379540427237711, 1138532283, 1138532283, 97534265577,
    1138532283, 37824572513, 97534265577, 394576948088497, 1138532283, 1138532283,
    2403568153, 6469775548058257, 7209, 405
  ]
def negativeCoefficients : Array ℕ := #[
    1053824574461711645079439933440, 10977150334163456038526779392, 616693838997946968456560640, 3625242819140864566496581386240, 16671290114244499713942355968, 1053824574461711645079439933440,
    16671290114244499713942355968, 16671290114244499713942355968, 10977150334163456038526779392, 616693838997946968456560640, 74373598067179751384316641280, 2695323811702720273034520821760,
    2695324802223701740961031782400, 74372607546198283457805680640, 2368462357636838439747720314880, 2988266286695082794774691840, 167880128466015887346892800, 8132598945329900290992959913984,
    4538359472864629487944335360, 2368462357636838439747720314880, 4538359472864629487944335360, 4538359472864629487944335360, 2988266286695082794774691840, 167880128466015887346892800,
    205778565217718079025492000768, 205778469405329360178080907264, 7625003187012296537356107776, 888016811489301704745878028288, 74489991506708380615857668096, 8685711145664586302127840690176,
    39291424091450574390782066688, 2864999673334937715994525696, 74489991506708380615857668096, 74489991506708380615857668096, 39291424091450574390782066688, 919255609472895730017672101888,
    73671420171469826982716375040, 888016825398146736322879946752, 74489991506708380615857668096, 2864999673334937715994525696, 73671420171469826982716375040, 2864999673334937715994525696,
    74489991506708380615857668096, 74489991506708380615857668096, 8033934093358938083240706048, 887101607272736246364435906560, 22169003291054881418063642624, 32381253145850804125242201473024,
    174435052211194988000027082752, 21002213644157256080270819328, 32379846454933369055031829987328, 21002213644157256080270819328, 21002213644157256080270819328, 899594817758069135438266761216,
    21002213644157256080270819328, 174435052211194988000027082752, 899594817758069135438266761216, 888508298190171316574807392256, 21002213644157256080270819328, 21002213644157256080270819328,
    22169003291054881418063642624, 7284319686851478190230882746368, 272348319800058178764275712, 15300467404497650492375040
  ]
def negativeScales : Array ℕ := #[
    36, 20, 15, 37, 21, 36,
    21, 21, 20, 15, 30, 36,
    39, 33, 32, 18, 14, 33,
    19, 32, 19, 19, 18, 14,
    33, 33, 42, 44, 31, 53,
    26, 28, 31, 31, 26, 35,
    30, 44, 31, 28, 30, 28,
    31, 31, 43, 47, 31, 52,
    35, 30, 53, 30, 30, 36,
    30, 35, 36, 48, 30, 30,
    31, 52, 12, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36733477574645798, 20148490236475455, 15994684922143517, 37515920476849056, 21751352409236794, 36733477574645798,
    21751352409236794, 21751352409236794, 20148490236475455, 15994684922143517, 30908777230900846, 36088301452984392,
    39088301983169091, 33908758016698623, 32901793594242163, 18271367275473176, 14117561939394141, 33681559316601393,
    19874229450734182, 32901793594242163, 19874229450734182, 19874229450734182, 18271367275473176, 14117561939394141,
    33377007464457979, 33377006792725770, 42622796502533594, 44486501740947196, 31911033259902951, 53776486821954811,
    26988201134701109, 28210593536445993, 31911033259902951, 31911033259902951, 26988201134701109, 35536380826789865,
    30895091714716707, 44486501763543864, 31911033259902951, 28210593536445993, 30895091714716707, 28210593536445993,
    31911033259902951, 31911033259902951, 43698165188264087, 47485014109826158, 31162530565554903, 52674929760181634,
    35138604726309423, 30084528053553630, 53674867085952029, 30084528053553630, 30084528053553630, 36505190102026674,
    30084528053553630, 35138604726309423, 36505190102026674, 48487300002047181, 30084528053553630, 30084528053553630,
    31162530565554903, 52522637085865699, 12815583434735727, 8661778097800657
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
noncomputable def negativeCeiling : ℝ := 32870256579 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1053824574461711645079439933440, coefficient := (-1053824574461711645079439933440) }, { argument := 10977150334163456038526779392, coefficient := (-10977150334163456038526779392) }, { argument := 616693838997946968456560640, coefficient := (-616693838997946968456560640) }, { argument := 3625242819140864566496581386240, coefficient := (-3625242819140864566496581386240) }, { argument := 16671290114244499713942355968, coefficient := (-16671290114244499713942355968) }, { argument := 1053824574461711645079439933440, coefficient := (-1053824574461711645079439933440) }, { argument := 16671290114244499713942355968, coefficient := (-16671290114244499713942355968) }, { argument := 16671290114244499713942355968, coefficient := (-16671290114244499713942355968) }, { argument := 10977150334163456038526779392, coefficient := (-10977150334163456038526779392) }, { argument := 616693838997946968456560640, coefficient := (-616693838997946968456560640) }, { argument := 74373598067179751384316641280, coefficient := (-74373598067179751384316641280) }, { argument := 2695323811702720273034520821760, coefficient := (-2695323811702720273034520821760) }, { argument := 2695324802223701740961031782400, coefficient := (-2695324802223701740961031782400) }, { argument := 74372607546198283457805680640, coefficient := (-74372607546198283457805680640) }, { argument := 2368462357636838439747720314880, coefficient := (-2368462357636838439747720314880) }, { argument := 2988266286695082794774691840, coefficient := (-2988266286695082794774691840) }, { argument := 167880128466015887346892800, coefficient := (-167880128466015887346892800) }, { argument := 8132598945329900290992959913984, coefficient := (-8132598945329900290992959913984) }, { argument := 4538359472864629487944335360, coefficient := (-4538359472864629487944335360) }, { argument := 2368462357636838439747720314880, coefficient := (-2368462357636838439747720314880) }, { argument := 4538359472864629487944335360, coefficient := (-4538359472864629487944335360) }, { argument := 4538359472864629487944335360, coefficient := (-4538359472864629487944335360) }, { argument := 2988266286695082794774691840, coefficient := (-2988266286695082794774691840) }, { argument := 167880128466015887346892800, coefficient := (-167880128466015887346892800) }, { argument := 205778565217718079025492000768, coefficient := (-205778565217718079025492000768) }, { argument := 205778469405329360178080907264, coefficient := (-205778469405329360178080907264) }, { argument := 7625003187012296537356107776, coefficient := (-7625003187012296537356107776) }, { argument := 888016811489301704745878028288, coefficient := (-888016811489301704745878028288) }, { argument := 74489991506708380615857668096, coefficient := (-74489991506708380615857668096) }, { argument := 8685711145664586302127840690176, coefficient := (-8685711145664586302127840690176) }, { argument := 39291424091450574390782066688, coefficient := (-39291424091450574390782066688) }, { argument := 2864999673334937715994525696, coefficient := (-2864999673334937715994525696) }, { argument := 74489991506708380615857668096, coefficient := (-74489991506708380615857668096) }, { argument := 74489991506708380615857668096, coefficient := (-74489991506708380615857668096) }, { argument := 39291424091450574390782066688, coefficient := (-39291424091450574390782066688) }, { argument := 919255609472895730017672101888, coefficient := (-919255609472895730017672101888) }, { argument := 73671420171469826982716375040, coefficient := (-73671420171469826982716375040) }, { argument := 888016825398146736322879946752, coefficient := (-888016825398146736322879946752) }, { argument := 74489991506708380615857668096, coefficient := (-74489991506708380615857668096) }, { argument := 2864999673334937715994525696, coefficient := (-2864999673334937715994525696) }, { argument := 73671420171469826982716375040, coefficient := (-73671420171469826982716375040) }, { argument := 2864999673334937715994525696, coefficient := (-2864999673334937715994525696) }, { argument := 74489991506708380615857668096, coefficient := (-74489991506708380615857668096) }, { argument := 74489991506708380615857668096, coefficient := (-74489991506708380615857668096) }, { argument := 8033934093358938083240706048, coefficient := (-8033934093358938083240706048) }, { argument := 887101607272736246364435906560, coefficient := (-887101607272736246364435906560) }, { argument := 22169003291054881418063642624, coefficient := (-22169003291054881418063642624) }, { argument := 32381253145850804125242201473024, coefficient := (-32381253145850804125242201473024) }, { argument := 174435052211194988000027082752, coefficient := (-174435052211194988000027082752) }, { argument := 21002213644157256080270819328, coefficient := (-21002213644157256080270819328) }, { argument := 32379846454933369055031829987328, coefficient := (-32379846454933369055031829987328) }, { argument := 21002213644157256080270819328, coefficient := (-21002213644157256080270819328) }, { argument := 21002213644157256080270819328, coefficient := (-21002213644157256080270819328) }, { argument := 899594817758069135438266761216, coefficient := (-899594817758069135438266761216) }, { argument := 21002213644157256080270819328, coefficient := (-21002213644157256080270819328) }, { argument := 174435052211194988000027082752, coefficient := (-174435052211194988000027082752) }, { argument := 899594817758069135438266761216, coefficient := (-899594817758069135438266761216) }, { argument := 888508298190171316574807392256, coefficient := (-888508298190171316574807392256) }, { argument := 21002213644157256080270819328, coefficient := (-21002213644157256080270819328) }, { argument := 21002213644157256080270819328, coefficient := (-21002213644157256080270819328) }, { argument := 22169003291054881418063642624, coefficient := (-22169003291054881418063642624) }, { argument := 7284319686851478190230882746368, coefficient := (-7284319686851478190230882746368) }, { argument := 272348319800058178764275712, coefficient := (-272348319800058178764275712) }, { argument := 15300467404497650492375040, coefficient := (-15300467404497650492375040) }] }

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


end Parent0

namespace Parent0

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2575499531691602939055057821237248)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    23473120059675899, 21897, 1617443821733917, 21897, 21897, 7209,
    405, 4076598617, 147737283239, 1181898700255, 32612354593, 114255889305,
    1162251, 65295, 196524807015, 3530283, 114255889305, 3530283,
    3530283, 1162251, 65295, 49215916333, 49215908563, 1028931575,
    28035, 1575, 1767321065, 85155, 1028931575, 85155,
    85155, 28035, 1575, 4938531943, 4938529689, 1,
    1575, 405, 1575, 1395, 65295, 17775,
    405, 65295, 1575, 1575, 675, 1575,
    17775, 675, 1575, 1395, 42422679, 4447941381,
    47944362375, 2223972387, 42422679, 313584509, 11364406403, 90915284635,
    2508642661, 42422679, 4447941381, 47944362375
  ]
def negativeCoefficients : Array ℕ := #[
    26428383688494823391729838718976, 413622635501586484977205248, 7284319392853579560626088312832, 413622635501586484977205248, 413622635501586484977205248, 272348319800058178764275712,
    15300467404497650492375040, 75199971379037304177475715072, 2725271854054972720512682164224, 2725272855581742871416154357760, 75198969852267153274003521536, 1053824574461711645079439933440,
    10977150334163456038526779392, 616693838997946968456560640, 3625242819140864566496581386240, 16671290114244499713942355968, 1053824574461711645079439933440, 16671290114244499713942355968,
    16671290114244499713942355968, 10977150334163456038526779392, 616693838997946968456560640, 453936706473976438638000472064, 453936634808375712276392443904, 75921749733535540147178700800,
    264783088694501007131934720, 14875454421039382423142400, 260810555057046426101292728320, 402133117848764638172282880, 75921749733535540147178700800, 402133117848764638172282880,
    402133117848764638172282880, 264783088694501007131934720, 14875454421039382423142400, 182199669704721134319646539776, 182199586546798850036987854848, 19807040628566084398385987584,
    14875454421039382423142400, 15300467404497650492375040, 14875454421039382423142400, 13175402487206310146211840, 616693838997946968456560640, 167880128466015887346892800,
    15300467404497650492375040, 616693838997946968456560640, 14875454421039382423142400, 14875454421039382423142400, 12750389503748042076979200, 14875454421039382423142400,
    167880128466015887346892800, 12750389503748042076979200, 14875454421039382423142400, 13175402487206310146211840, 195640075608533161859874816, 20512509077542307201940455424,
    221104345627203613294067712000, 20512524724992967726067613696, 195640075608533161859874816, 2892306591501434776056758272, 104818148232883566173564698624, 104818186753143956592929013760,
    2892268071241044356692443136, 195640075608533161859874816, 20512509077542307201940455424, 221104345627203613294067712000
  ]
def negativeScales : Array ℕ := #[
    54, 14, 50, 14, 14, 12,
    8, 31, 37, 40, 34, 36,
    20, 15, 37, 21, 36, 21,
    21, 20, 15, 35, 35, 29,
    14, 10, 30, 16, 29, 16,
    16, 14, 10, 32, 32, 0,
    10, 8, 10, 10, 15, 14,
    8, 15, 10, 10, 9, 10,
    14, 9, 10, 10, 25, 32,
    35, 31, 25, 28, 33, 36,
    31, 25, 32, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    54381859136601330, 14418445606380756, 50522637027637980, 14418445606380756, 14418445606380756, 12815583434735727,
    8661778097800657, 31924718776420632, 37104242996853413, 40104243527038113, 34924699562217890, 36733477574645798,
    20148490236475455, 15994684922143517, 37515920476849056, 21751352409236794, 36733477574645798, 21751352409236794,
    21751352409236794, 20148490236475455, 15994684922143517, 35518405904708705, 35518405676942117, 29938499907288165,
    14774941449737867, 10621136113284685, 30718917008762599, 16377803621883399, 29938499907288165, 16377803621883399,
    16377803621883399, 14774941449737867, 10621136113284685, 32201435095528836, 32201434437066888, 0,
    10621136113284685, 8661778097800657, 10621136113284685, 10446049406716591, 15994684922143517, 14117561939394141,
    8661778097800657, 15994684922143517, 10621136113284685, 10621136113284685, 9398743691938200, 10621136113284685,
    14117561939394141, 9398743691938200, 10621136113284685, 10446049406716591, 25338332394414632, 32050490629031076,
    35480642132171395, 31050491729554214, 25338332394414632, 28224279051521148, 33403803278712329, 36403803808897028,
    31224259837320665, 25338332394414632, 32050490629031076, 35480642132171395
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
noncomputable def negativeCeiling : ℝ := 13947486883 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 26428383688494823391729838718976, coefficient := (-26428383688494823391729838718976) }, { argument := 413622635501586484977205248, coefficient := (-413622635501586484977205248) }, { argument := 7284319392853579560626088312832, coefficient := (-7284319392853579560626088312832) }, { argument := 413622635501586484977205248, coefficient := (-413622635501586484977205248) }, { argument := 413622635501586484977205248, coefficient := (-413622635501586484977205248) }, { argument := 272348319800058178764275712, coefficient := (-272348319800058178764275712) }, { argument := 15300467404497650492375040, coefficient := (-15300467404497650492375040) }, { argument := 75199971379037304177475715072, coefficient := (-75199971379037304177475715072) }, { argument := 2725271854054972720512682164224, coefficient := (-2725271854054972720512682164224) }, { argument := 2725272855581742871416154357760, coefficient := (-2725272855581742871416154357760) }, { argument := 75198969852267153274003521536, coefficient := (-75198969852267153274003521536) }, { argument := 1053824574461711645079439933440, coefficient := (-1053824574461711645079439933440) }, { argument := 10977150334163456038526779392, coefficient := (-10977150334163456038526779392) }, { argument := 616693838997946968456560640, coefficient := (-616693838997946968456560640) }, { argument := 3625242819140864566496581386240, coefficient := (-3625242819140864566496581386240) }, { argument := 16671290114244499713942355968, coefficient := (-16671290114244499713942355968) }, { argument := 1053824574461711645079439933440, coefficient := (-1053824574461711645079439933440) }, { argument := 16671290114244499713942355968, coefficient := (-16671290114244499713942355968) }, { argument := 16671290114244499713942355968, coefficient := (-16671290114244499713942355968) }, { argument := 10977150334163456038526779392, coefficient := (-10977150334163456038526779392) }, { argument := 616693838997946968456560640, coefficient := (-616693838997946968456560640) }, { argument := 453936706473976438638000472064, coefficient := (-453936706473976438638000472064) }, { argument := 453936634808375712276392443904, coefficient := (-453936634808375712276392443904) }, { argument := 75921749733535540147178700800, coefficient := (-75921749733535540147178700800) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 260810555057046426101292728320, coefficient := (-260810555057046426101292728320) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 75921749733535540147178700800, coefficient := (-75921749733535540147178700800) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 182199669704721134319646539776, coefficient := (-182199669704721134319646539776) }, { argument := 182199586546798850036987854848, coefficient := (-182199586546798850036987854848) }, { argument := 19807040628566084398385987584, coefficient := (-19807040628566084398385987584) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 15300467404497650492375040, coefficient := (-15300467404497650492375040) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }, { argument := 616693838997946968456560640, coefficient := (-616693838997946968456560640) }, { argument := 167880128466015887346892800, coefficient := (-167880128466015887346892800) }, { argument := 15300467404497650492375040, coefficient := (-15300467404497650492375040) }, { argument := 616693838997946968456560640, coefficient := (-616693838997946968456560640) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 167880128466015887346892800, coefficient := (-167880128466015887346892800) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }, { argument := 195640075608533161859874816, coefficient := (-195640075608533161859874816) }, { argument := 20512509077542307201940455424, coefficient := (-20512509077542307201940455424) }, { argument := 221104345627203613294067712000, coefficient := (-221104345627203613294067712000) }, { argument := 20512524724992967726067613696, coefficient := (-20512524724992967726067613696) }, { argument := 195640075608533161859874816, coefficient := (-195640075608533161859874816) }, { argument := 2892306591501434776056758272, coefficient := (-2892306591501434776056758272) }, { argument := 104818148232883566173564698624, coefficient := (-104818148232883566173564698624) }, { argument := 104818186753143956592929013760, coefficient := (-104818186753143956592929013760) }, { argument := 2892268071241044356692443136, coefficient := (-2892268071241044356692443136) }, { argument := 195640075608533161859874816, coefficient := (-195640075608533161859874816) }, { argument := 20512509077542307201940455424, coefficient := (-20512509077542307201940455424) }, { argument := 221104345627203613294067712000, coefficient := (-221104345627203613294067712000) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15
