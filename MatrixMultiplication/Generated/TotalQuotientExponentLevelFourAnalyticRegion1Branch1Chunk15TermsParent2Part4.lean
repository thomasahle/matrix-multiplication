import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
parent chunk 15, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-258373353570653454854056878089961472)
def positiveArguments : Array ℕ := #[
    2291, 87, 4495, 87, 2291, 2291,
    87, 1053, 4797, 117, 50193, 2223,
    117, 2223, 4329, 81783, 4329, 50193,
    81783, 1053, 4329, 4329, 4797, 21,
    105, 87, 1563, 585, 21, 2343,
    2343, 1677, 87, 387, 74616668621, 74616667699,
    87052790217, 636186295477, 174094495673, 764868821, 478973764883, 478973800695,
    6118985299, 30892573, 1481543873, 1893393491, 2963093297, 30892573,
    7730589, 1409944163, 352486069, 1932619
  ]
def positiveCoefficients : Array ℕ := #[
    709030157500701552448473399296, 26925195854457020979055951872, 695567559573473041958945423360, 26925195854457020979055951872, 709030157500701552448473399296, 709030157500701552448473399296,
    26925195854457020979055951872, 81471928835469089341798612992, 92787474507062018417048420352, 72419492298194746081598767104, 970873818622673314656433471488, 85998147104106260971898535936,
    72419492298194746081598767104, 85998147104106260971898535936, 83735037969787675156848574464, 3163826569777382969439846137856, 83735037969787675156848574464, 970873818622673314656433471488,
    3163826569777382969439846137856, 81471928835469089341798612992, 83735037969787675156848574464, 83735037969787675156848574464, 92787474507062018417048420352, 3249592603124123221610201088,
    64991852062482464432204021760, 3365649481807127622381993984, 60465633793845292802104098816, 90524365372743432601998458880, 3249592603124123221610201088, 90640422251426437002770251776,
    90640422251426437002770251776, 64875795183799460031432228864, 3365649481807127622381993984, 30661298893020298648701508780032, 352367254959201590050193162633216, 352367250605179692844380275605504,
    822190357522086697890192046424064, 3004304838621589368794562263252992, 822138011218269677278843432337408, 57791854145318755700607241158656, 2261889653457365093722454195437568, 2261889822574753578250188588318720,
    57792182170339388791903074910208, 291772102609607528496408559616, 55971145030048658592280675876864, 572243069490044751941843868975104, 55971249885474044229883000782848, 291772102609607528496408559616,
    73013348772881535445801893888, 13316546116137791517863125712896, 13316547183392616646402944008192, 73012281518056406905983598592
  ]
def positiveScales : Array ℕ := #[
    11, 6, 12, 6, 11, 11,
    6, 10, 12, 6, 15, 11,
    6, 11, 12, 16, 12, 15,
    16, 10, 12, 12, 12, 4,
    6, 6, 10, 9, 4, 11,
    11, 10, 6, 8, 36, 36,
    36, 39, 37, 29, 38, 38,
    32, 24, 30, 30, 31, 24,
    22, 30, 28, 20
  ]
def negativeArguments : Array ℕ := #[
    29, 117, 3, 387, 8895, 29337,
    58557, 8643, 169
  ]
def negativeCoefficients : Array ℕ := #[
    18380933703309326321702196477952, 9269695014168927498444642189312, 475368975085586025561263702016, 30661298893020298648701508780032, 704734505564381282894573438238720, 4648633207361945743963597742014464,
    4639363512347776816465153099825152, 684769008610786669821000362754048, 26779118929821346106617855213568
  ]
def negativeScales : Array ℕ := #[
    4, 6, 1, 8, 13, 14,
    15, 13, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11161761743304674, 6442943495848725, 12134105400401809, 6442943495848725, 11161761743304674, 11161761743304674,
    6442943495848725, 10040289721025716, 12227916724201487, 6870364719426147, 15615198557082416, 11118292233026989,
    6870364719426147, 11118292233026989, 12079818085212354, 16319513364958840, 12079818085212354, 15615198557082416,
    16319513364958840, 10040289721025716, 12079818085212354, 12079818085212354, 12227916724201487, 4392317422778759,
    6714245517659862, 6442943495848725, 10610102062999199, 9192292814470766, 4392317422778759, 11194141238863135,
    11194141238863135, 10711666973558447, 6442943495848725, 8596189756144093, 36118778899067844, 36118778881241199,
    36341171488768570, 39210658337895055, 37341079633936668, 29510637098380459, 38801155680245669, 38801155788113357,
    32510645287055740, 24880756700080464, 30464454203486487, 30818327121557933, 31464456906205191, 24880756700080464,
    22882146907600585, 30392990883732263, 28392990999357078, 20882125819203500
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    4857980997143165, 6870364722125690, 1584962500724866, 8596189756149498, 13118778890154523, 14840433729629628,
    15837554024084007, 13077316445881027, 7400879436282192
  ]

abbrev PositiveTerm := Fin 52
abbrev NegativeTerm := Fin 9
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
noncomputable def positiveFloor : ℝ := 2439273224661 / 500000000000
noncomputable def negativeCeiling : ℝ := 970666246717 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 709030157500701552448473399296, coefficient := 709030157500701552448473399296 }, { argument := 26925195854457020979055951872, coefficient := 26925195854457020979055951872 }, { argument := 695567559573473041958945423360, coefficient := 695567559573473041958945423360 }, { argument := 26925195854457020979055951872, coefficient := 26925195854457020979055951872 }, { argument := 709030157500701552448473399296, coefficient := 709030157500701552448473399296 }, { argument := 709030157500701552448473399296, coefficient := 709030157500701552448473399296 }, { argument := 26925195854457020979055951872, coefficient := 26925195854457020979055951872 }, { argument := 18380933703309326321702196477952, coefficient := (-18380933703309326321702196477952) }, { argument := 81471928835469089341798612992, coefficient := 81471928835469089341798612992 }, { argument := 92787474507062018417048420352, coefficient := 92787474507062018417048420352 }, { argument := 72419492298194746081598767104, coefficient := 72419492298194746081598767104 }, { argument := 970873818622673314656433471488, coefficient := 970873818622673314656433471488 }, { argument := 85998147104106260971898535936, coefficient := 85998147104106260971898535936 }, { argument := 72419492298194746081598767104, coefficient := 72419492298194746081598767104 }, { argument := 85998147104106260971898535936, coefficient := 85998147104106260971898535936 }, { argument := 83735037969787675156848574464, coefficient := 83735037969787675156848574464 }, { argument := 3163826569777382969439846137856, coefficient := 3163826569777382969439846137856 }, { argument := 83735037969787675156848574464, coefficient := 83735037969787675156848574464 }, { argument := 970873818622673314656433471488, coefficient := 970873818622673314656433471488 }, { argument := 3163826569777382969439846137856, coefficient := 3163826569777382969439846137856 }, { argument := 81471928835469089341798612992, coefficient := 81471928835469089341798612992 }, { argument := 83735037969787675156848574464, coefficient := 83735037969787675156848574464 }, { argument := 83735037969787675156848574464, coefficient := 83735037969787675156848574464 }, { argument := 92787474507062018417048420352, coefficient := 92787474507062018417048420352 }, { argument := 9269695014168927498444642189312, coefficient := (-9269695014168927498444642189312) }, { argument := 3249592603124123221610201088, coefficient := 3249592603124123221610201088 }, { argument := 64991852062482464432204021760, coefficient := 64991852062482464432204021760 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 60465633793845292802104098816, coefficient := 60465633793845292802104098816 }, { argument := 90524365372743432601998458880, coefficient := 90524365372743432601998458880 }, { argument := 3249592603124123221610201088, coefficient := 3249592603124123221610201088 }, { argument := 90640422251426437002770251776, coefficient := 90640422251426437002770251776 }, { argument := 90640422251426437002770251776, coefficient := 90640422251426437002770251776 }, { argument := 64875795183799460031432228864, coefficient := 64875795183799460031432228864 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 30661298893020298648701508780032, coefficient := 30661298893020298648701508780032 }, { argument := 30661298893020298648701508780032, coefficient := (-30661298893020298648701508780032) }, { argument := 352367254959201590050193162633216, coefficient := 352367254959201590050193162633216 }, { argument := 352367250605179692844380275605504, coefficient := 352367250605179692844380275605504 }, { argument := 704734505564381282894573438238720, coefficient := (-704734505564381282894573438238720) }, { argument := 822190357522086697890192046424064, coefficient := 822190357522086697890192046424064 }, { argument := 3004304838621589368794562263252992, coefficient := 3004304838621589368794562263252992 }, { argument := 822138011218269677278843432337408, coefficient := 822138011218269677278843432337408 }, { argument := 4648633207361945743963597742014464, coefficient := (-4648633207361945743963597742014464) }, { argument := 57791854145318755700607241158656, coefficient := 57791854145318755700607241158656 }, { argument := 2261889653457365093722454195437568, coefficient := 2261889653457365093722454195437568 }, { argument := 2261889822574753578250188588318720, coefficient := 2261889822574753578250188588318720 }, { argument := 57792182170339388791903074910208, coefficient := 57792182170339388791903074910208 }, { argument := 4639363512347776816465153099825152, coefficient := (-4639363512347776816465153099825152) }, { argument := 291772102609607528496408559616, coefficient := 291772102609607528496408559616 }, { argument := 55971145030048658592280675876864, coefficient := 55971145030048658592280675876864 }, { argument := 572243069490044751941843868975104, coefficient := 572243069490044751941843868975104 }, { argument := 55971249885474044229883000782848, coefficient := 55971249885474044229883000782848 }, { argument := 291772102609607528496408559616, coefficient := 291772102609607528496408559616 }, { argument := 684769008610786669821000362754048, coefficient := (-684769008610786669821000362754048) }, { argument := 73013348772881535445801893888, coefficient := 73013348772881535445801893888 }, { argument := 13316546116137791517863125712896, coefficient := 13316546116137791517863125712896 }, { argument := 13316547183392616646402944008192, coefficient := 13316547183392616646402944008192 }, { argument := 73012281518056406905983598592, coefficient := 73012281518056406905983598592 }, { argument := 26779118929821346106617855213568, coefficient := (-26779118929821346106617855213568) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15
