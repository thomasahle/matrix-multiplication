import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 4, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk4

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
def constantNumerator : ℤ := 4802361993441797636794452279296
def positiveArguments : Array ℕ := #[
    5, 27035205, 96912969, 13523385, 2443679, 89831081,
    179705055, 4844177, 386091, 4952499, 130437893, 4942245,
    11921
  ]
def positiveCoefficients : Array ℕ := #[
    3169126500570573503741758013440, 255340291899019693259080335360, 915317113121969915271837646848, 255449520235768468152873123840, 46159791217969646984637710336, 1696861144137392846531150741504,
    1697266257068492301915452866560, 45751958203776058684692496384, 3646526395475248380402204672, 93550061136181740204736905216, 1231951067998674230664081965056, 93356368552520358836651950080,
    3602901173906498597918081024
  ]
def positiveScales : Array ℕ := #[
    2, 24, 26, 23, 21, 26,
    27, 22, 18, 22, 26, 22,
    13
  ]
def negativeArguments : Array ℕ := #[
    1160481963987, 7440443579061, 391805892613317, 1856288604561, 286676830689, 546930718467,
    19952332240081, 39913872880335, 1083862037897, 1160481963987, 4156150478083, 580449830293,
    4156150478083, 53321361815381, 1404603674835125, 53210521454603, 513277782641, 19952332240081,
    733605798714895, 1467562217561355, 39552419429685, 7440443579061, 53321361815381, 14886896489281,
    580449830293, 14886896489281, 195987568998723, 14856281598829, 286777139517, 39913872880335,
    1467562217561355, 22936138102405, 19780797515635, 391805892613317, 1404603674835125, 195987568998723,
    1083862037897, 39552419429685, 19780797515635, 268481843095, 1856288604561, 53210521454603,
    14856281598829, 286676830689, 513277782641, 286777139517, 9, 11,
    9
  ]
def negativeCoefficients : Array ℕ := #[
    326646633786377159911145472, 8377194732532579798628696064, 110283554498431188276401405952, 8359980667793017601582432256, 322769416966683793016487936, 307894622485682356909768704,
    11232164505200140666926006272, 11234756439424378242607349760, 305080041874622225875730432, 326646633786377159911145472, 1169852359024394225160552448, 326764204926852805129404416,
    1169852359024394225160552448, 30017258150329658216254799872, 395360786661918642475630592000, 29954860574392481698740699136, 1155798815319781020132179968, 11232164505200140666926006272,
    412983350216154526918104842240, 413082041009521072435762298880, 11133016337820683244782223360, 8377194732532579798628696064, 30017258150329658216254799872, 8380577685228632087484956672,
    326764204926852805129404416, 8380577685228632087484956672, 110331192838987284580008984576, 8363343034074680118002843648, 322882354666784485810372608, 11234756439424378242607349760,
    413082041009521072435762298880, 413180732045237572901294571520, 11135599040063127378062213120, 110283554498431188276401405952, 395360786661918642475630592000, 110331192838987284580008984576,
    305080041874622225875730432, 11133016337820683244782223360, 11135599040063127378062213120, 302283682129596493626081280, 8359980667793017601582432256, 29954860574392481698740699136,
    8363343034074680118002843648, 322769416966683793016487936, 1155798815319781020132179968, 322882354666784485810372608, 1426106925256758076683791106048, 3486039150627630854115933814784,
    1426106925256758076683791106048
  ]
def negativeScales : Array ℕ := #[
    40, 42, 48, 40, 38, 38,
    44, 45, 39, 40, 41, 39,
    41, 45, 50, 45, 38, 44,
    49, 50, 45, 42, 45, 43,
    39, 43, 47, 43, 38, 45,
    50, 44, 44, 48, 50, 47,
    39, 45, 44, 37, 40, 45,
    43, 38, 38, 38, 3, 3,
    3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 24688335960201262, 26530186405806565, 23688952977919303, 21220623355494163, 26420711359138083,
    27421055750700560, 22207820149541587, 18558581399069487, 22239725253132487, 26958787800481375, 22236735099926908,
    13541217641736082
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    40077861239384415, 42758525772380669, 48477132423782863, 40755558168333172, 38060634353987124, 38992567158393902,
    44181622627328686, 45181955505223029, 39979318286922767, 40077861239384415, 41918385034276520, 39078380420558332,
    41918385034276520, 45599778860540006, 50319084538091860, 45596776775311773, 38900948862682716, 44181622627328686,
    49381998371042193, 50382343091255293, 45168831180887353, 42758525772380669, 45599778860540006, 43759108256621590,
    39078380420558332, 43759108256621590, 47477755479127752, 43756138300529247, 38061139067731235, 45181955505223029,
    50382343091255293, 44382687729966194, 44169165826905594, 48477132423782863, 50319084538091860, 47477755479127752,
    39979318286922767, 45168831180887353, 44169165826905594, 37966033582241199, 40755558168333172, 45596776775311773,
    43756138300529247, 38060634353987124, 38900948862682716, 38061139067731235, 3169925001442313, 3459431618637364,
    3169925001442313
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
noncomputable def positiveFloor : ℝ := 2104690139 / 1000000000000
noncomputable def negativeCeiling : ℝ := 2107458993 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 326646633786377159911145472, coefficient := (-326646633786377159911145472) }, { argument := 8377194732532579798628696064, coefficient := (-8377194732532579798628696064) }, { argument := 110283554498431188276401405952, coefficient := (-110283554498431188276401405952) }, { argument := 8359980667793017601582432256, coefficient := (-8359980667793017601582432256) }, { argument := 322769416966683793016487936, coefficient := (-322769416966683793016487936) }, { argument := 307894622485682356909768704, coefficient := (-307894622485682356909768704) }, { argument := 11232164505200140666926006272, coefficient := (-11232164505200140666926006272) }, { argument := 11234756439424378242607349760, coefficient := (-11234756439424378242607349760) }, { argument := 305080041874622225875730432, coefficient := (-305080041874622225875730432) }, { argument := 326646633786377159911145472, coefficient := (-326646633786377159911145472) }, { argument := 1169852359024394225160552448, coefficient := (-1169852359024394225160552448) }, { argument := 326764204926852805129404416, coefficient := (-326764204926852805129404416) }, { argument := 1169852359024394225160552448, coefficient := (-1169852359024394225160552448) }, { argument := 30017258150329658216254799872, coefficient := (-30017258150329658216254799872) }, { argument := 395360786661918642475630592000, coefficient := (-395360786661918642475630592000) }, { argument := 29954860574392481698740699136, coefficient := (-29954860574392481698740699136) }, { argument := 1155798815319781020132179968, coefficient := (-1155798815319781020132179968) }, { argument := 11232164505200140666926006272, coefficient := (-11232164505200140666926006272) }, { argument := 412983350216154526918104842240, coefficient := (-412983350216154526918104842240) }, { argument := 413082041009521072435762298880, coefficient := (-413082041009521072435762298880) }, { argument := 11133016337820683244782223360, coefficient := (-11133016337820683244782223360) }, { argument := 8377194732532579798628696064, coefficient := (-8377194732532579798628696064) }, { argument := 30017258150329658216254799872, coefficient := (-30017258150329658216254799872) }, { argument := 8380577685228632087484956672, coefficient := (-8380577685228632087484956672) }, { argument := 326764204926852805129404416, coefficient := (-326764204926852805129404416) }, { argument := 8380577685228632087484956672, coefficient := (-8380577685228632087484956672) }, { argument := 110331192838987284580008984576, coefficient := (-110331192838987284580008984576) }, { argument := 8363343034074680118002843648, coefficient := (-8363343034074680118002843648) }, { argument := 322882354666784485810372608, coefficient := (-322882354666784485810372608) }, { argument := 11234756439424378242607349760, coefficient := (-11234756439424378242607349760) }, { argument := 413082041009521072435762298880, coefficient := (-413082041009521072435762298880) }, { argument := 413180732045237572901294571520, coefficient := (-413180732045237572901294571520) }, { argument := 11135599040063127378062213120, coefficient := (-11135599040063127378062213120) }, { argument := 110283554498431188276401405952, coefficient := (-110283554498431188276401405952) }, { argument := 395360786661918642475630592000, coefficient := (-395360786661918642475630592000) }, { argument := 110331192838987284580008984576, coefficient := (-110331192838987284580008984576) }, { argument := 305080041874622225875730432, coefficient := (-305080041874622225875730432) }, { argument := 11133016337820683244782223360, coefficient := (-11133016337820683244782223360) }, { argument := 11135599040063127378062213120, coefficient := (-11135599040063127378062213120) }, { argument := 302283682129596493626081280, coefficient := (-302283682129596493626081280) }, { argument := 8359980667793017601582432256, coefficient := (-8359980667793017601582432256) }, { argument := 29954860574392481698740699136, coefficient := (-29954860574392481698740699136) }, { argument := 8363343034074680118002843648, coefficient := (-8363343034074680118002843648) }, { argument := 322769416966683793016487936, coefficient := (-322769416966683793016487936) }, { argument := 1155798815319781020132179968, coefficient := (-1155798815319781020132179968) }, { argument := 322882354666784485810372608, coefficient := (-322882354666784485810372608) }, { argument := 3169126500570573503741758013440, coefficient := 3169126500570573503741758013440 }, { argument := 255340291899019693259080335360, coefficient := 255340291899019693259080335360 }, { argument := 915317113121969915271837646848, coefficient := 915317113121969915271837646848 }, { argument := 255449520235768468152873123840, coefficient := 255449520235768468152873123840 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 46159791217969646984637710336, coefficient := 46159791217969646984637710336 }, { argument := 1696861144137392846531150741504, coefficient := 1696861144137392846531150741504 }, { argument := 1697266257068492301915452866560, coefficient := 1697266257068492301915452866560 }, { argument := 45751958203776058684692496384, coefficient := 45751958203776058684692496384 }, { argument := 3486039150627630854115933814784, coefficient := (-3486039150627630854115933814784) }, { argument := 3646526395475248380402204672, coefficient := 3646526395475248380402204672 }, { argument := 93550061136181740204736905216, coefficient := 93550061136181740204736905216 }, { argument := 1231951067998674230664081965056, coefficient := 1231951067998674230664081965056 }, { argument := 93356368552520358836651950080, coefficient := 93356368552520358836651950080 }, { argument := 3602901173906498597918081024, coefficient := 3602901173906498597918081024 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk4
