import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
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

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2046294532075480781634283824480256)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2223972387, 42422679, 2015900415, 73056898305, 584455401225, 16126988535,
    8025706605, 28035, 1575, 13785423507, 85155, 8025706605,
    85155, 85155, 28035, 1575, 313584509, 11364406403,
    90915284635, 2508642661, 8025476205, 12015, 675, 13783599507,
    36495, 8025476205, 36495, 36495, 12015, 675,
    936378585, 936378151, 89558989, 9390098471, 101215876125, 4695052817,
    89558989, 4076598617, 147737283239, 1181898700255, 32612354593, 8025706605,
    28035, 1575, 13785423507, 85155, 8025706605, 85155,
    85155, 28035, 1575, 4076598617, 147737283239, 1181898700255,
    32612354593, 8024662605, 316395, 17775, 13777158507, 961035,
    8024662605, 961035, 961035, 316395
  ]
def negativeCoefficients : Array ℕ := #[
    20512524724992967726067613696, 195640075608533161859874816, 74373598067179751384316641280, 2695323811702720273034520821760, 2695324802223701740961031782400, 74372607546198283457805680640,
    74024077876557677628059811840, 264783088694501007131934720, 14875454421039382423142400, 254296179381328593537636237312, 402133117848764638172282880, 74024077876557677628059811840,
    402133117848764638172282880, 402133117848764638172282880, 264783088694501007131934720, 14875454421039382423142400, 2892306591501434776056758272, 104818148232883566173564698624,
    104818186753143956592929013760, 2892268071241044356692443136, 74021952811640386287713648640, 226956933166715148970229760, 12750389503748042076979200, 254262532520138147315488653312,
    344685529584655404147671040, 74021952811640386287713648640, 344685529584655404147671040, 344685529584655404147671040, 226956933166715148970229760, 12750389503748042076979200,
    8636568056798642821587271680, 8636564053855178826614571008, 206508968697896115296534528, 21652092915183546490937147392, 233387920384270480699293696000, 21652109431937021488626925568,
    206508968697896115296534528, 75199971379037304177475715072, 2725271854054972720512682164224, 2725272855581742871416154357760, 75198969852267153274003521536, 74024077876557677628059811840,
    264783088694501007131934720, 14875454421039382423142400, 254296179381328593537636237312, 402133117848764638172282880, 74024077876557677628059811840, 402133117848764638172282880,
    402133117848764638172282880, 264783088694501007131934720, 14875454421039382423142400, 75199971379037304177475715072, 2725271854054972720512682164224, 2725272855581742871416154357760,
    75198969852267153274003521536, 2368462357636838439747720314880, 2988266286695082794774691840, 167880128466015887346892800, 8132598945329900290992959913984, 4538359472864629487944335360,
    2368462357636838439747720314880, 4538359472864629487944335360, 4538359472864629487944335360, 2988266286695082794774691840
  ]
def negativeScales : Array ℕ := #[
    31, 25, 30, 36, 39, 33,
    32, 14, 10, 33, 16, 32,
    16, 16, 14, 10, 28, 33,
    36, 31, 32, 13, 9, 33,
    15, 32, 15, 15, 13, 9,
    29, 29, 26, 33, 36, 32,
    26, 31, 37, 40, 34, 32,
    14, 10, 33, 16, 32, 16,
    16, 14, 10, 31, 37, 40,
    34, 32, 18, 14, 33, 19,
    32, 19, 19, 18
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31050491729554214, 25338332394414632, 30908777230900846, 36088301452984392, 39088301983169091, 33908758016698623,
    32901981275126860, 14774941449737867, 10621136113284685, 33682424538508242, 16377803621883399, 32901981275126860,
    16377803621883399, 16377803621883399, 14774941449737867, 10621136113284685, 28224279051521148, 33403803278712329,
    36403803808897028, 31224259837320665, 32901939857996637, 13552549028018665, 9398743691938200, 33682233637600357,
    15155411200546948, 32901939857996637, 15155411200546948, 15155411200546948, 13552549028018665, 9398743691938200,
    29802516700136985, 29802516031465348, 26416334906415918, 33128493141032349, 36558644644174252, 32128494241555487,
    26416334906415918, 31924718776420632, 37104242996853413, 40104243527038113, 34924699562217890, 32901981275126860,
    14774941449737867, 10621136113284685, 33682424538508242, 16377803621883399, 32901981275126860, 16377803621883399,
    16377803621883399, 14774941449737867, 10621136113284685, 31924718776420632, 37104242996853413, 40104243527038113,
    34924699562217890, 32901793594242163, 18271367275473176, 14117561939394141, 33681559316601393, 19874229450734182,
    32901793594242163, 19874229450734182, 19874229450734182, 18271367275473176
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
noncomputable def negativeCeiling : ℝ := 13571427773 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 20512524724992967726067613696, coefficient := (-20512524724992967726067613696) }, { argument := 195640075608533161859874816, coefficient := (-195640075608533161859874816) }, { argument := 74373598067179751384316641280, coefficient := (-74373598067179751384316641280) }, { argument := 2695323811702720273034520821760, coefficient := (-2695323811702720273034520821760) }, { argument := 2695324802223701740961031782400, coefficient := (-2695324802223701740961031782400) }, { argument := 74372607546198283457805680640, coefficient := (-74372607546198283457805680640) }, { argument := 74024077876557677628059811840, coefficient := (-74024077876557677628059811840) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 254296179381328593537636237312, coefficient := (-254296179381328593537636237312) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 74024077876557677628059811840, coefficient := (-74024077876557677628059811840) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 2892306591501434776056758272, coefficient := (-2892306591501434776056758272) }, { argument := 104818148232883566173564698624, coefficient := (-104818148232883566173564698624) }, { argument := 104818186753143956592929013760, coefficient := (-104818186753143956592929013760) }, { argument := 2892268071241044356692443136, coefficient := (-2892268071241044356692443136) }, { argument := 74021952811640386287713648640, coefficient := (-74021952811640386287713648640) }, { argument := 226956933166715148970229760, coefficient := (-226956933166715148970229760) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 254262532520138147315488653312, coefficient := (-254262532520138147315488653312) }, { argument := 344685529584655404147671040, coefficient := (-344685529584655404147671040) }, { argument := 74021952811640386287713648640, coefficient := (-74021952811640386287713648640) }, { argument := 344685529584655404147671040, coefficient := (-344685529584655404147671040) }, { argument := 344685529584655404147671040, coefficient := (-344685529584655404147671040) }, { argument := 226956933166715148970229760, coefficient := (-226956933166715148970229760) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 8636568056798642821587271680, coefficient := (-8636568056798642821587271680) }, { argument := 8636564053855178826614571008, coefficient := (-8636564053855178826614571008) }, { argument := 206508968697896115296534528, coefficient := (-206508968697896115296534528) }, { argument := 21652092915183546490937147392, coefficient := (-21652092915183546490937147392) }, { argument := 233387920384270480699293696000, coefficient := (-233387920384270480699293696000) }, { argument := 21652109431937021488626925568, coefficient := (-21652109431937021488626925568) }, { argument := 206508968697896115296534528, coefficient := (-206508968697896115296534528) }, { argument := 75199971379037304177475715072, coefficient := (-75199971379037304177475715072) }, { argument := 2725271854054972720512682164224, coefficient := (-2725271854054972720512682164224) }, { argument := 2725272855581742871416154357760, coefficient := (-2725272855581742871416154357760) }, { argument := 75198969852267153274003521536, coefficient := (-75198969852267153274003521536) }, { argument := 74024077876557677628059811840, coefficient := (-74024077876557677628059811840) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 254296179381328593537636237312, coefficient := (-254296179381328593537636237312) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 74024077876557677628059811840, coefficient := (-74024077876557677628059811840) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 75199971379037304177475715072, coefficient := (-75199971379037304177475715072) }, { argument := 2725271854054972720512682164224, coefficient := (-2725271854054972720512682164224) }, { argument := 2725272855581742871416154357760, coefficient := (-2725272855581742871416154357760) }, { argument := 75198969852267153274003521536, coefficient := (-75198969852267153274003521536) }, { argument := 2368462357636838439747720314880, coefficient := (-2368462357636838439747720314880) }, { argument := 2988266286695082794774691840, coefficient := (-2988266286695082794774691840) }, { argument := 167880128466015887346892800, coefficient := (-167880128466015887346892800) }, { argument := 8132598945329900290992959913984, coefficient := (-8132598945329900290992959913984) }, { argument := 4538359472864629487944335360, coefficient := (-4538359472864629487944335360) }, { argument := 2368462357636838439747720314880, coefficient := (-2368462357636838439747720314880) }, { argument := 4538359472864629487944335360, coefficient := (-4538359472864629487944335360) }, { argument := 4538359472864629487944335360, coefficient := (-4538359472864629487944335360) }, { argument := 2988266286695082794774691840, coefficient := (-2988266286695082794774691840) }] }

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


end Parent0

namespace Parent0

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 203434192514889806260689135118319616
def positiveArguments : Array ℕ := #[
    26775, 1, 1, 1
  ]
def positiveCoefficients : Array ℕ := #[
    2121334051319427639067139270246400, 19807040628566084398385987584, 19807040628566084398385987584, 19807040628566084398385987584
  ]
def positiveScales : Array ℕ := #[
    14, 0, 0, 0
  ]
def negativeArguments : Array ℕ := #[
    17775, 19724767637, 19724758635, 8025476205, 12015, 675,
    13783599507, 36495, 8025476205, 36495, 36495, 12015,
    675, 9765914837, 9765910315, 1, 7150971188243, 45848501,
    258633279661037, 721510621, 21717711, 517250959926979, 21717711, 21717711,
    1860483909, 21717711, 721510621, 1860483909, 14317541771581, 21717711,
    21717711, 45848501, 152138376050031, 28035, 1575, 537458168474373,
    85155, 38034593232867, 85155, 85155, 28035, 1575,
    4245185497, 4245185063, 9671490245, 24831, 1395, 16609124411,
    75423, 9671490245, 75423, 75423, 24831, 1395,
    11155278373, 11155273179, 1, 935330009, 935329575, 1
  ]
def negativeCoefficients : Array ℕ := #[
    167880128466015887346892800, 181928870256563853126528925696, 181928787227768777359837102080, 74021952811640386287713648640, 226956933166715148970229760, 12750389503748042076979200,
    254262532520138147315488653312, 344685529584655404147671040, 74021952811640386287713648640, 344685529584655404147671040, 344685529584655404147671040, 226956933166715148970229760,
    12750389503748042076979200, 180149331643781931755311726592, 180149248227605230440719319040, 19807040628566084398385987584, 8051277794677081951680069632, 211438891027554112743931904,
    291195185476763878803623641088, 1663690221506281045011464192, 200310528341893369967935488, 291186403798021747910742376448, 200310528341893369967935488, 200310528341893369967935488,
    8579967630644432680293236736, 200310528341893369967935488, 1663690221506281045011464192, 8579967630644432680293236736, 8060059473419212844561334272, 200310528341893369967935488,
    200310528341893369967935488, 211438891027554112743931904, 171292583421918001177867321344, 264783088694501007131934720, 14875454421039382423142400, 605124101817103875861488074752,
    402133117848764638172282880, 171292579910728209995013292032, 402133117848764638172282880, 402133117848764638172282880, 264783088694501007131934720, 14875454421039382423142400,
    39154925204291243755308056576, 39154921201347779760335355904, 89203752680446744708733992960, 234522164272272320602570752, 13175402487206310146211840, 306384267298118897069170098176,
    356175047237477250952593408, 89203752680446744708733992960, 356175047237477250952593408, 356175047237477250952593408, 234522164272272320602570752, 13175402487206310146211840,
    205778565217718079025492000768, 205778469405329360178080907264, 19807040628566084398385987584, 8626896650241725788189622272, 8626892647298261793216921600, 19807040628566084398385987584
  ]
def negativeScales : Array ℕ := #[
    14, 34, 34, 32, 13, 9,
    33, 15, 32, 15, 15, 13,
    9, 33, 33, 0, 42, 25,
    47, 29, 24, 48, 24, 24,
    30, 24, 29, 30, 43, 24,
    24, 25, 47, 14, 10, 48,
    16, 45, 16, 16, 14, 10,
    31, 31, 33, 14, 10, 33,
    16, 33, 16, 16, 14, 10,
    33, 33, 0, 29, 29, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14708598954519486, 0, 0, 0
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    14117561939394141, 34199289253881822, 34199288595463738, 32901939857996637, 13552549028018665, 9398743691938200,
    33682233637600357, 15155411200546948, 32901939857996637, 15155411200546948, 15155411200546948, 13552549028018665,
    9398743691938200, 33185108051091939, 33185107383067633, 0, 42701276329329010, 25450371230415368,
    47877901257355750, 29426445391169860, 24372368718414050, 48877857748820149, 24372368718414050, 24372368718414050,
    30793030767446857, 24372368718414050, 29426445391169860, 30793030767446857, 43702849046160439, 24372368718414050,
    24372368718414050, 25450371230415368, 47112377439103724, 14774941449737867, 10621136113284685, 48933145807255592,
    16377803621883399, 45112377409531070, 16377803621883399, 16377803621883399, 14774941449737867, 10621136113284685,
    31983180466992630, 31983180319500874, 33171091060484885, 14599854742801218, 10446049406716591, 33951256979768792,
    16202716915325305, 33171091060484885, 16202716915325305, 16202716915325305, 14599854742801218, 10446049406716591,
    33377007464457979, 33377006792725770, 0, 29800900235288889, 29800899565867620, 0
  ]

abbrev PositiveTerm := Fin 4
abbrev NegativeTerm := Fin 60
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
noncomputable def positiveFloor : ℝ := 751157259 / 2000000000
noncomputable def negativeCeiling : ℝ := 439149091 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 167880128466015887346892800, coefficient := (-167880128466015887346892800) }, { argument := 181928870256563853126528925696, coefficient := (-181928870256563853126528925696) }, { argument := 181928787227768777359837102080, coefficient := (-181928787227768777359837102080) }, { argument := 74021952811640386287713648640, coefficient := (-74021952811640386287713648640) }, { argument := 226956933166715148970229760, coefficient := (-226956933166715148970229760) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 254262532520138147315488653312, coefficient := (-254262532520138147315488653312) }, { argument := 344685529584655404147671040, coefficient := (-344685529584655404147671040) }, { argument := 74021952811640386287713648640, coefficient := (-74021952811640386287713648640) }, { argument := 344685529584655404147671040, coefficient := (-344685529584655404147671040) }, { argument := 344685529584655404147671040, coefficient := (-344685529584655404147671040) }, { argument := 226956933166715148970229760, coefficient := (-226956933166715148970229760) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 180149331643781931755311726592, coefficient := (-180149331643781931755311726592) }, { argument := 180149248227605230440719319040, coefficient := (-180149248227605230440719319040) }, { argument := 19807040628566084398385987584, coefficient := (-19807040628566084398385987584) }, { argument := 8051277794677081951680069632, coefficient := (-8051277794677081951680069632) }, { argument := 211438891027554112743931904, coefficient := (-211438891027554112743931904) }, { argument := 291195185476763878803623641088, coefficient := (-291195185476763878803623641088) }, { argument := 1663690221506281045011464192, coefficient := (-1663690221506281045011464192) }, { argument := 200310528341893369967935488, coefficient := (-200310528341893369967935488) }, { argument := 291186403798021747910742376448, coefficient := (-291186403798021747910742376448) }, { argument := 200310528341893369967935488, coefficient := (-200310528341893369967935488) }, { argument := 200310528341893369967935488, coefficient := (-200310528341893369967935488) }, { argument := 8579967630644432680293236736, coefficient := (-8579967630644432680293236736) }, { argument := 200310528341893369967935488, coefficient := (-200310528341893369967935488) }, { argument := 1663690221506281045011464192, coefficient := (-1663690221506281045011464192) }, { argument := 8579967630644432680293236736, coefficient := (-8579967630644432680293236736) }, { argument := 8060059473419212844561334272, coefficient := (-8060059473419212844561334272) }, { argument := 200310528341893369967935488, coefficient := (-200310528341893369967935488) }, { argument := 200310528341893369967935488, coefficient := (-200310528341893369967935488) }, { argument := 211438891027554112743931904, coefficient := (-211438891027554112743931904) }, { argument := 171292583421918001177867321344, coefficient := (-171292583421918001177867321344) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 605124101817103875861488074752, coefficient := (-605124101817103875861488074752) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 171292579910728209995013292032, coefficient := (-171292579910728209995013292032) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 39154925204291243755308056576, coefficient := (-39154925204291243755308056576) }, { argument := 39154921201347779760335355904, coefficient := (-39154921201347779760335355904) }, { argument := 89203752680446744708733992960, coefficient := (-89203752680446744708733992960) }, { argument := 234522164272272320602570752, coefficient := (-234522164272272320602570752) }, { argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }, { argument := 306384267298118897069170098176, coefficient := (-306384267298118897069170098176) }, { argument := 356175047237477250952593408, coefficient := (-356175047237477250952593408) }, { argument := 89203752680446744708733992960, coefficient := (-89203752680446744708733992960) }, { argument := 356175047237477250952593408, coefficient := (-356175047237477250952593408) }, { argument := 356175047237477250952593408, coefficient := (-356175047237477250952593408) }, { argument := 234522164272272320602570752, coefficient := (-234522164272272320602570752) }, { argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }, { argument := 205778565217718079025492000768, coefficient := (-205778565217718079025492000768) }, { argument := 205778469405329360178080907264, coefficient := (-205778469405329360178080907264) }, { argument := 19807040628566084398385987584, coefficient := (-19807040628566084398385987584) }, { argument := 8626896650241725788189622272, coefficient := (-8626896650241725788189622272) }, { argument := 8626892647298261793216921600, coefficient := (-8626892647298261793216921600) }, { argument := 19807040628566084398385987584, coefficient := (-19807040628566084398385987584) }, { argument := 2121334051319427639067139270246400, coefficient := 2121334051319427639067139270246400 }, { argument := 19807040628566084398385987584, coefficient := 19807040628566084398385987584 }, { argument := 19807040628566084398385987584, coefficient := 19807040628566084398385987584 }, { argument := 19807040628566084398385987584, coefficient := 19807040628566084398385987584 }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15
