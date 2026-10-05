import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 4, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4

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
def constantNumerator : ℤ := (-3021441364433308680435018107977728)
def positiveArguments : Array ℕ := #[
    143, 5929, 8877, 275, 8877, 9251,
    5511, 275, 3069, 3465, 1485, 39105,
    3465, 1485, 3465, 3465, 143649, 891,
    39105, 143649, 3069, 3465, 891, 3465,
    2697, 78213, 69223, 4495, 2697, 4495,
    137547, 4495, 2697, 2203449, 141143, 78213,
    137547, 4495, 141143, 4495, 137547, 4495,
    2697, 141, 105, 111, 9, 1929,
    3489, 105, 1929, 57, 57, 111,
    111, 3489, 111, 141, 9, 29622263
  ]
def positiveCoefficients : Array ℕ := #[
    44256356404452344827643691008, 917468311615377456234613440512, 1373649216092040087534940717056, 42554188850434946949657395200, 1373649216092040087534940717056, 1431522912928631615386474774528,
    852785944562716336871134199808, 42554188850434946949657395200, 949809495141708015916353060864, 1072365559030960663131366359040, 919170479169394854112599736320, 12102411309063698912482563194880,
    1072365559030960663131366359040, 919170479169394854112599736320, 1072365559030960663131366359040, 1072365559030960663131366359040, 44457212175826397777246073913344, 1103004575003273824935119683584,
    12102411309063698912482563194880, 44457212175826397777246073913344, 949809495141708015916353060864, 1072365559030960663131366359040, 1103004575003273824935119683584, 1072365559030960663131366359040,
    208670267872041912587683627008, 3025718884144607732521412591616, 5355870208715742423083879759872, 173891889893368260489736355840, 3338724285952670601402938032128, 173891889893368260489736355840,
    5321091830737068770985932488704, 5564540476587784335671563386880, 3338724285952670601402938032128, 85241804425729121292068761632768, 5460205342651763379377721573376, 3025718884144607732521412591616,
    5321091830737068770985932488704, 173891889893368260489736355840, 5460205342651763379377721573376, 173891889893368260489736355840, 5321091830737068770985932488704, 5564540476587784335671563386880,
    208670267872041912587683627008, 87274772769619309380388257792, 64991852062482464432204021760, 68705672180338605256901394432, 89131682828547379792736944128, 1193993167890749275140205314048,
    2159586398533345889561522208768, 64991852062482464432204021760, 1193993167890749275140205314048, 70562582239266675669250080768, 70562582239266675669250080768, 68705672180338605256901394432,
    68705672180338605256901394432, 2159586398533345889561522208768, 68705672180338605256901394432, 87274772769619309380388257792, 89131682828547379792736944128, 4476389822014388007577411649536
  ]
def positiveScales : Array ℕ := #[
    7, 12, 13, 8, 13, 13,
    12, 8, 11, 11, 10, 15,
    11, 10, 11, 11, 17, 9,
    15, 17, 11, 11, 9, 11,
    11, 16, 16, 12, 11, 12,
    17, 12, 11, 21, 17, 16,
    17, 12, 17, 12, 17, 12,
    11, 7, 6, 6, 3, 10,
    11, 6, 10, 5, 5, 6,
    6, 11, 6, 7, 3, 24
  ]
def negativeArguments : Array ℕ := #[
    11, 99, 899, 3
  ]
def negativeCoefficients : Array ℕ := #[
    6972078301255261708231867629568, 125497409422594710748173617332224, 142452236200647278993192022704128, 7605903601369376408980219232256
  ]
def negativeScales : Array ℕ := #[
    3, 6, 9, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7159871336778389, 12533573081389752, 13115856481915077, 8103287808412021, 13115856481915077, 13175393608892441,
    12428098411832503, 8103287808412021, 11583552930466262, 11758639637007751, 10536247215688073, 15255065463144074,
    11758639637007751, 10536247215688073, 11758639637007751, 11758639637007751, 17132188424146353, 9799281621482476,
    15255065463144074, 17132188424146353, 11583552930466262, 11758639637007751, 9799281621482476, 11758639637007751,
    11397139806235602, 16255120801363175, 16078963846209348, 12134105400401809, 11397139806235602, 12134105400401809,
    17069565148207099, 12134105400401809, 11397139806235602, 21071332074381286, 17106798054406074, 16255120801363175,
    17069565148207099, 12134105400401809, 17106798054406074, 12134105400401809, 17069565148207099, 12134105400401809,
    11397139806235602, 7139551352398793, 6714245517659862, 6794415866314396, 3169925001442312, 10913637427705176,
    11768597882173550, 6714245517659862, 10913637427705176, 5832890014087662, 5832890014087662, 6794415866314396,
    6794415866314396, 11768597882173550, 6794415866314396, 7139551352398793, 3169925001442312, 24820178524027619
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    3459431618637364, 6629356620092098, 9812177306340859, 1584962500724866
  ]

abbrev PositiveTerm := Fin 60
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
noncomputable def positiveFloor : ℝ := 59786235077 / 1000000000000
noncomputable def negativeCeiling : ℝ := 27274877611 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 44256356404452344827643691008, coefficient := 44256356404452344827643691008 }, { argument := 917468311615377456234613440512, coefficient := 917468311615377456234613440512 }, { argument := 1373649216092040087534940717056, coefficient := 1373649216092040087534940717056 }, { argument := 42554188850434946949657395200, coefficient := 42554188850434946949657395200 }, { argument := 1373649216092040087534940717056, coefficient := 1373649216092040087534940717056 }, { argument := 1431522912928631615386474774528, coefficient := 1431522912928631615386474774528 }, { argument := 852785944562716336871134199808, coefficient := 852785944562716336871134199808 }, { argument := 42554188850434946949657395200, coefficient := 42554188850434946949657395200 }, { argument := 6972078301255261708231867629568, coefficient := (-6972078301255261708231867629568) }, { argument := 949809495141708015916353060864, coefficient := 949809495141708015916353060864 }, { argument := 1072365559030960663131366359040, coefficient := 1072365559030960663131366359040 }, { argument := 919170479169394854112599736320, coefficient := 919170479169394854112599736320 }, { argument := 12102411309063698912482563194880, coefficient := 12102411309063698912482563194880 }, { argument := 1072365559030960663131366359040, coefficient := 1072365559030960663131366359040 }, { argument := 919170479169394854112599736320, coefficient := 919170479169394854112599736320 }, { argument := 1072365559030960663131366359040, coefficient := 1072365559030960663131366359040 }, { argument := 1072365559030960663131366359040, coefficient := 1072365559030960663131366359040 }, { argument := 44457212175826397777246073913344, coefficient := 44457212175826397777246073913344 }, { argument := 1103004575003273824935119683584, coefficient := 1103004575003273824935119683584 }, { argument := 12102411309063698912482563194880, coefficient := 12102411309063698912482563194880 }, { argument := 44457212175826397777246073913344, coefficient := 44457212175826397777246073913344 }, { argument := 949809495141708015916353060864, coefficient := 949809495141708015916353060864 }, { argument := 1072365559030960663131366359040, coefficient := 1072365559030960663131366359040 }, { argument := 1103004575003273824935119683584, coefficient := 1103004575003273824935119683584 }, { argument := 1072365559030960663131366359040, coefficient := 1072365559030960663131366359040 }, { argument := 125497409422594710748173617332224, coefficient := (-125497409422594710748173617332224) }, { argument := 208670267872041912587683627008, coefficient := 208670267872041912587683627008 }, { argument := 3025718884144607732521412591616, coefficient := 3025718884144607732521412591616 }, { argument := 5355870208715742423083879759872, coefficient := 5355870208715742423083879759872 }, { argument := 173891889893368260489736355840, coefficient := 173891889893368260489736355840 }, { argument := 3338724285952670601402938032128, coefficient := 3338724285952670601402938032128 }, { argument := 173891889893368260489736355840, coefficient := 173891889893368260489736355840 }, { argument := 5321091830737068770985932488704, coefficient := 5321091830737068770985932488704 }, { argument := 5564540476587784335671563386880, coefficient := 5564540476587784335671563386880 }, { argument := 3338724285952670601402938032128, coefficient := 3338724285952670601402938032128 }, { argument := 85241804425729121292068761632768, coefficient := 85241804425729121292068761632768 }, { argument := 5460205342651763379377721573376, coefficient := 5460205342651763379377721573376 }, { argument := 3025718884144607732521412591616, coefficient := 3025718884144607732521412591616 }, { argument := 5321091830737068770985932488704, coefficient := 5321091830737068770985932488704 }, { argument := 173891889893368260489736355840, coefficient := 173891889893368260489736355840 }, { argument := 5460205342651763379377721573376, coefficient := 5460205342651763379377721573376 }, { argument := 173891889893368260489736355840, coefficient := 173891889893368260489736355840 }, { argument := 5321091830737068770985932488704, coefficient := 5321091830737068770985932488704 }, { argument := 5564540476587784335671563386880, coefficient := 5564540476587784335671563386880 }, { argument := 208670267872041912587683627008, coefficient := 208670267872041912587683627008 }, { argument := 142452236200647278993192022704128, coefficient := (-142452236200647278993192022704128) }, { argument := 87274772769619309380388257792, coefficient := 87274772769619309380388257792 }, { argument := 64991852062482464432204021760, coefficient := 64991852062482464432204021760 }, { argument := 68705672180338605256901394432, coefficient := 68705672180338605256901394432 }, { argument := 89131682828547379792736944128, coefficient := 89131682828547379792736944128 }, { argument := 1193993167890749275140205314048, coefficient := 1193993167890749275140205314048 }, { argument := 2159586398533345889561522208768, coefficient := 2159586398533345889561522208768 }, { argument := 64991852062482464432204021760, coefficient := 64991852062482464432204021760 }, { argument := 1193993167890749275140205314048, coefficient := 1193993167890749275140205314048 }, { argument := 70562582239266675669250080768, coefficient := 70562582239266675669250080768 }, { argument := 70562582239266675669250080768, coefficient := 70562582239266675669250080768 }, { argument := 68705672180338605256901394432, coefficient := 68705672180338605256901394432 }, { argument := 68705672180338605256901394432, coefficient := 68705672180338605256901394432 }, { argument := 2159586398533345889561522208768, coefficient := 2159586398533345889561522208768 }, { argument := 68705672180338605256901394432, coefficient := 68705672180338605256901394432 }, { argument := 87274772769619309380388257792, coefficient := 87274772769619309380388257792 }, { argument := 89131682828547379792736944128, coefficient := 89131682828547379792736944128 }, { argument := 7605903601369376408980219232256, coefficient := (-7605903601369376408980219232256) }, { argument := 4476389822014388007577411649536, coefficient := 4476389822014388007577411649536 }] }

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
def constantNumerator : ℤ := (-19069192416949393944425499262451712)
def positiveArguments : Array ℕ := #[
    29622281, 4165042943, 7507312183, 4165828755, 345396967, 1717384495,
    6869537291, 345398155, 4277895, 182437615, 3766459749, 182437659,
    4277895, 810525, 158573027, 158573029, 810523
  ]
def positiveCoefficients : Array ℕ := #[
    4476392542097482140493054738432, 39337718387471892372436503494656, 141809117717752593254670477033472, 39345140171973165895725833256960, 6524364240982531652706661040128, 259523807276416377476879105392640,
    259523781246732323899394687500288, 6524386681668058249260716523520, 40403575930471281822888099840, 6892298226325411429462908600320, 71146413111020866845185950089216, 6892299888598413399578023821312,
    40403575930471281822888099840, 3827596093527919186830950400, 748839947791983287951836577792, 748839957236716253691127005184, 3827586648794953447540523008
  ]
def positiveScales : Array ℕ := #[
    24, 31, 32, 31, 28, 30,
    32, 28, 22, 27, 31, 27,
    22, 19, 27, 27, 19
  ]
def negativeArguments : Array ℕ := #[
    113, 2783, 1679, 1073, 19
  ]
def negativeCoefficients : Array ℕ := #[
    8952782364111870148070466387968, 220491976277197651522832813785088, 532096339445799291278241170456576, 85011818377805634237872658710528, 1505335087771022414277335056384
  ]
def negativeScales : Array ℕ := #[
    6, 11, 10, 10, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    24820179400682546, 31955684223619101, 32805649331010655, 31955956388911392, 28363680173427024, 30677565925897854,
    32677565781198613, 28363685135597873, 22028469641626491, 27442827974233098, 31810561965710289, 27442828322179842,
    22028469641626491, 19628497159648063, 27240572151056699, 27240572169252669, 19628493599741037
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6820178963384638, 11442425193331643, 10713386515035898, 10067434360756522, 4247927513443586
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
noncomputable def positiveFloor : ℝ := 322281732433 / 1000000000000
noncomputable def negativeCeiling : ℝ := 11010086161 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4476392542097482140493054738432, coefficient := 4476392542097482140493054738432 }, { argument := 8952782364111870148070466387968, coefficient := (-8952782364111870148070466387968) }, { argument := 39337718387471892372436503494656, coefficient := 39337718387471892372436503494656 }, { argument := 141809117717752593254670477033472, coefficient := 141809117717752593254670477033472 }, { argument := 39345140171973165895725833256960, coefficient := 39345140171973165895725833256960 }, { argument := 220491976277197651522832813785088, coefficient := (-220491976277197651522832813785088) }, { argument := 6524364240982531652706661040128, coefficient := 6524364240982531652706661040128 }, { argument := 259523807276416377476879105392640, coefficient := 259523807276416377476879105392640 }, { argument := 259523781246732323899394687500288, coefficient := 259523781246732323899394687500288 }, { argument := 6524386681668058249260716523520, coefficient := 6524386681668058249260716523520 }, { argument := 532096339445799291278241170456576, coefficient := (-532096339445799291278241170456576) }, { argument := 40403575930471281822888099840, coefficient := 40403575930471281822888099840 }, { argument := 6892298226325411429462908600320, coefficient := 6892298226325411429462908600320 }, { argument := 71146413111020866845185950089216, coefficient := 71146413111020866845185950089216 }, { argument := 6892299888598413399578023821312, coefficient := 6892299888598413399578023821312 }, { argument := 40403575930471281822888099840, coefficient := 40403575930471281822888099840 }, { argument := 85011818377805634237872658710528, coefficient := (-85011818377805634237872658710528) }, { argument := 3827596093527919186830950400, coefficient := 3827596093527919186830950400 }, { argument := 748839947791983287951836577792, coefficient := 748839947791983287951836577792 }, { argument := 748839957236716253691127005184, coefficient := 748839957236716253691127005184 }, { argument := 3827586648794953447540523008, coefficient := 3827586648794953447540523008 }, { argument := 1505335087771022414277335056384, coefficient := (-1505335087771022414277335056384) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4
