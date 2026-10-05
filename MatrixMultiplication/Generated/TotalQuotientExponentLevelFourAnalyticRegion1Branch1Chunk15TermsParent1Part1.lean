import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 15, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 11917069504907328220139824479207424
def positiveArguments : Array ℕ := #[
    21, 609, 539, 35, 21, 35,
    1071, 35, 21, 17157, 1099, 609,
    1071, 35, 1099, 35, 1071, 35,
    21, 9, 135, 237, 9, 75,
    9, 237, 471, 75, 7269, 465,
    135, 237, 9, 465, 9, 237,
    237, 9, 63, 287, 7, 3003,
    133, 7, 133, 259, 4893, 259,
    3003, 4893, 63, 259, 259, 287,
    1391, 190656281025, 190656284223, 21397645239
  ]
def positiveCoefficients : Array ℕ := #[
    1624796301562061610805100544, 23559546372649893356673957888, 41703105073426248010664247296, 1353996917968384675670917120, 25996740824992985772881608704, 1353996917968384675670917120,
    41432305689832571075530063872, 43327901374988309621469347840, 25996740824992985772881608704, 663729289188102168013883572224, 42515503224207278816066797568, 23559546372649893356673957888,
    41432305689832571075530063872, 1353996917968384675670917120, 42515503224207278816066797568, 1353996917968384675670917120, 41432305689832571075530063872, 43327901374988309621469347840,
    1624796301562061610805100544, 1392682544196052809261514752, 20890238162940792138922721280, 36673973663829390643886555136, 1392682544196052809261514752, 23211375736600880154358579200,
    1392682544196052809261514752, 36673973663829390643886555136, 36441859906463381842342969344, 23211375736600880154358579200, 562411634097839326140108374016, 35977632391731364239255797760,
    20890238162940792138922721280, 36673973663829390643886555136, 1392682544196052809261514752, 35977632391731364239255797760, 1392682544196052809261514752, 36673973663829390643886555136,
    36673973663829390643886555136, 1392682544196052809261514752, 4874388904686184832415301632, 5551387363670377170250760192, 4332790137498830962146934784, 58086467780843702586282344448,
    5145188288279861767549485056, 4332790137498830962146934784, 5145188288279861767549485056, 5009788596483023299982393344, 189288769131980177658794213376, 5009788596483023299982393344,
    58086467780843702586282344448, 189288769131980177658794213376, 4874388904686184832415301632, 5009788596483023299982393344, 5009788596483023299982393344, 5551387363670377170250760192,
    220412748114683387185239269834752, 900348831261035926304470754918400, 900348846363163938521596148318208, 808380181511910711715690815946752
  ]
def positiveScales : Array ℕ := #[
    4, 9, 9, 5, 4, 5,
    10, 5, 4, 14, 10, 9,
    10, 5, 10, 5, 10, 5,
    4, 3, 7, 7, 3, 6,
    3, 7, 8, 6, 12, 8,
    7, 7, 3, 8, 3, 7,
    7, 3, 5, 8, 2, 11,
    7, 2, 7, 8, 12, 8,
    11, 12, 5, 8, 8, 8,
    10, 37, 37, 34
  ]
def negativeArguments : Array ℕ := #[
    1, 7, 3, 7, 1391, 2841
  ]
def negativeCoefficients : Array ℕ := #[
    633825300114114700748351602688, 1109194275199700726309615304704, 950737950171172051122527404032, 554597137599850363154807652352, 220412748114683387185239269834752, 1800697677624199864826066903236608
  ]
def negativeScales : Array ℕ := #[
    0, 2, 1, 2, 10, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4392317422778759, 9250298417906332, 9074141462752505, 5129283016944966, 4392317422778759, 5129283016944966,
    10064742764750255, 5129283016944966, 4392317422778759, 14066509690924443, 10101975670949231, 9250298417906332,
    10064742764750255, 5129283016944966, 10101975670949231, 5129283016944966, 10064742764750255, 5129283016944966,
    4392317422778759, 3169925001442312, 7076815597050830, 7888743248677875, 3169925001442312, 6228818690495880,
    3169925001442312, 7888743248677875, 8879583249426338, 6228818690495880, 12827541190103080, 8861086905863166,
    7076815597050830, 7888743248677875, 3169925001442312, 8861086905863166, 3169925001442312, 7888743248677875,
    7888743248677875, 3169925001442312, 5977279922488012, 8164906926675687, 2807354922011143, 11552188759557060,
    7055282435501189, 2807354922011143, 7055282435501189, 8016808287686553, 12256503567433040, 8016808287686553,
    11552188759557060, 12256503567433040, 5977279922488012, 8016808287686553, 8016808287686553, 8164906926675687,
    10441906704542236, 37472183104089909, 37472183128289158, 34316732989007643
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 2807354922807594, 1584962500724866, 2807354922807594, 10441906704542274, 11472183116189646
  ]

abbrev PositiveTerm := Fin 58
abbrev NegativeTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 1174193347481 / 1000000000000
noncomputable def negativeCeiling : ℝ := 276438843079 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 1624796301562061610805100544, coefficient := 1624796301562061610805100544 }, { argument := 23559546372649893356673957888, coefficient := 23559546372649893356673957888 }, { argument := 41703105073426248010664247296, coefficient := 41703105073426248010664247296 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 25996740824992985772881608704, coefficient := 25996740824992985772881608704 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 41432305689832571075530063872, coefficient := 41432305689832571075530063872 }, { argument := 43327901374988309621469347840, coefficient := 43327901374988309621469347840 }, { argument := 25996740824992985772881608704, coefficient := 25996740824992985772881608704 }, { argument := 663729289188102168013883572224, coefficient := 663729289188102168013883572224 }, { argument := 42515503224207278816066797568, coefficient := 42515503224207278816066797568 }, { argument := 23559546372649893356673957888, coefficient := 23559546372649893356673957888 }, { argument := 41432305689832571075530063872, coefficient := 41432305689832571075530063872 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 42515503224207278816066797568, coefficient := 42515503224207278816066797568 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 41432305689832571075530063872, coefficient := 41432305689832571075530063872 }, { argument := 43327901374988309621469347840, coefficient := 43327901374988309621469347840 }, { argument := 1624796301562061610805100544, coefficient := 1624796301562061610805100544 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 20890238162940792138922721280, coefficient := 20890238162940792138922721280 }, { argument := 36673973663829390643886555136, coefficient := 36673973663829390643886555136 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 23211375736600880154358579200, coefficient := 23211375736600880154358579200 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 36673973663829390643886555136, coefficient := 36673973663829390643886555136 }, { argument := 36441859906463381842342969344, coefficient := 36441859906463381842342969344 }, { argument := 23211375736600880154358579200, coefficient := 23211375736600880154358579200 }, { argument := 562411634097839326140108374016, coefficient := 562411634097839326140108374016 }, { argument := 35977632391731364239255797760, coefficient := 35977632391731364239255797760 }, { argument := 20890238162940792138922721280, coefficient := 20890238162940792138922721280 }, { argument := 36673973663829390643886555136, coefficient := 36673973663829390643886555136 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 35977632391731364239255797760, coefficient := 35977632391731364239255797760 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 36673973663829390643886555136, coefficient := 36673973663829390643886555136 }, { argument := 36673973663829390643886555136, coefficient := 36673973663829390643886555136 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 4874388904686184832415301632, coefficient := 4874388904686184832415301632 }, { argument := 5551387363670377170250760192, coefficient := 5551387363670377170250760192 }, { argument := 4332790137498830962146934784, coefficient := 4332790137498830962146934784 }, { argument := 58086467780843702586282344448, coefficient := 58086467780843702586282344448 }, { argument := 5145188288279861767549485056, coefficient := 5145188288279861767549485056 }, { argument := 4332790137498830962146934784, coefficient := 4332790137498830962146934784 }, { argument := 5145188288279861767549485056, coefficient := 5145188288279861767549485056 }, { argument := 5009788596483023299982393344, coefficient := 5009788596483023299982393344 }, { argument := 189288769131980177658794213376, coefficient := 189288769131980177658794213376 }, { argument := 5009788596483023299982393344, coefficient := 5009788596483023299982393344 }, { argument := 58086467780843702586282344448, coefficient := 58086467780843702586282344448 }, { argument := 189288769131980177658794213376, coefficient := 189288769131980177658794213376 }, { argument := 4874388904686184832415301632, coefficient := 4874388904686184832415301632 }, { argument := 5009788596483023299982393344, coefficient := 5009788596483023299982393344 }, { argument := 5009788596483023299982393344, coefficient := 5009788596483023299982393344 }, { argument := 5551387363670377170250760192, coefficient := 5551387363670377170250760192 }, { argument := 554597137599850363154807652352, coefficient := (-554597137599850363154807652352) }, { argument := 220412748114683387185239269834752, coefficient := 220412748114683387185239269834752 }, { argument := 220412748114683387185239269834752, coefficient := (-220412748114683387185239269834752) }, { argument := 900348831261035926304470754918400, coefficient := 900348831261035926304470754918400 }, { argument := 900348846363163938521596148318208, coefficient := 900348846363163938521596148318208 }, { argument := 1800697677624199864826066903236608, coefficient := (-1800697677624199864826066903236608) }, { argument := 808380181511910711715690815946752, coefficient := 808380181511910711715690815946752 }] }

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

end TermShard2


end Parent1

namespace Parent1

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-206340265584828072217042703821570048)
def positiveArguments : Array ℕ := #[
    19573836653, 21396564629, 4742183513, 46447059425, 185788266751, 1185554761,
    4476431, 467306331, 4840660975, 467307175, 4476431
  ]
def positiveCoefficients : Array ℕ := #[
    2957914564841361859358361036783616, 808339357220350281577175839670272, 22394328477408228460548532994048, 877360146625898623076819743539200, 877360283815367316922882846621696, 22394496267811731301912620826624,
    84557390869114595174361595904, 17654334037977506048671909675008, 182875001146200780784270101708800, 17654365923395998384516392550400, 84557390869114595174361595904
  ]
def positiveScales : Array ℕ := #[
    34, 34, 32, 35, 37, 30,
    22, 28, 32, 28, 22
  ]
def negativeArguments : Array ℕ := #[
    14435, 22713, 689
  ]
def negativeCoefficients : Array ℕ := #[
    4574634103573622852651227692400640, 1799509255186485899762163743981568, 218352815889312514407807127126016
  ]
def negativeScales : Array ℕ := #[
    13, 14, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    34188207514125712, 34316660129118734, 32142904347293794, 35434868210987270, 37434868436575988, 30142915156703705,
    22093917517977063, 28799793341822275, 32172556909801698, 28799795947465369, 22093917517977063
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    13817283488038559, 14471230653594217, 9428360172704312
  ]

abbrev PositiveTerm := Fin 11
abbrev NegativeTerm := Fin 3
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
noncomputable def positiveFloor : ℝ := 96824848253 / 40000000000
noncomputable def negativeCeiling : ℝ := 1099090167113 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2957914564841361859358361036783616, coefficient := 2957914564841361859358361036783616 }, { argument := 808339357220350281577175839670272, coefficient := 808339357220350281577175839670272 }, { argument := 4574634103573622852651227692400640, coefficient := (-4574634103573622852651227692400640) }, { argument := 22394328477408228460548532994048, coefficient := 22394328477408228460548532994048 }, { argument := 877360146625898623076819743539200, coefficient := 877360146625898623076819743539200 }, { argument := 877360283815367316922882846621696, coefficient := 877360283815367316922882846621696 }, { argument := 22394496267811731301912620826624, coefficient := 22394496267811731301912620826624 }, { argument := 1799509255186485899762163743981568, coefficient := (-1799509255186485899762163743981568) }, { argument := 84557390869114595174361595904, coefficient := 84557390869114595174361595904 }, { argument := 17654334037977506048671909675008, coefficient := 17654334037977506048671909675008 }, { argument := 182875001146200780784270101708800, coefficient := 182875001146200780784270101708800 }, { argument := 17654365923395998384516392550400, coefficient := 17654365923395998384516392550400 }, { argument := 84557390869114595174361595904, coefficient := 84557390869114595174361595904 }, { argument := 218352815889312514407807127126016, coefficient := (-218352815889312514407807127126016) }] }

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

end TermShard3


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15
