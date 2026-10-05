import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 3, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk3

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
def constantNumerator : ℤ := 3180917034608635004555146297344
def positiveArguments : Array ℕ := #[
    3, 8388589, 8388627, 3863903, 105944539, 30916397,
    2296165, 81589979, 10198713, 287039, 72421, 2555335,
    7075761, 1275617, 36199
  ]
def positiveCoefficients : Array ℕ := #[
    1901475900342344102245054808064, 158455966128675977094051659776, 158456683928381373280124141568, 291948256324151532002169847808, 1000617880033351918517158412288, 291997113927783301351550746624,
    21686665270276757804212551680, 770595564335276425445814304768, 770592967033710847140946771968, 21688053646022721479905378304, 683997006111805152042156032, 24134456713007409704279736320,
    267314692697569629495254581248, 24095723863114912874237001728, 683779777253593148362326016
  ]
def positiveScales : Array ℕ := #[
    1, 22, 23, 21, 26, 24,
    21, 26, 23, 18, 16, 21,
    22, 20, 15
  ]
def negativeArguments : Array ℕ := #[
    303755003975, 10717827535251, 59355650889133, 5350313367771, 151829267595, 7101855734587,
    252200481067949, 63049909535163, 1775576732299, 7101855734587, 12158996736053, 7103406969947,
    303755003975, 303756375993, 303756375993, 10717876088429, 59355919772243, 5350337603365,
    151829953397, 12158996736053, 432204948085297, 216101741932083, 3039944681549, 252200481067949,
    432204948085297, 252242323879921, 10717827535251, 10717876088429, 7103406969947, 252242323879921,
    31530185189385, 1775964511451, 63049909535163, 216101741932083, 31530185189385, 59355650889133,
    59355919772243, 1775576732299, 3039944681549, 1775964511451, 5350313367771, 5350337603365,
    151829267595, 151829953397, 1, 5, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    170998865339216691409715200, 6033600511747205647734669312, 66828521806658157096302804992, 6023917322352214780730671104, 170944558241194330847969280, 1998994677495314583830659072,
    70988124535017184218048364544, 70987887272075892366835187712, 1999121677487374832370712576, 1998994677495314583830659072, 6844906646210920988368961536, 1999431311432143329906655232,
    170998865339216691409715200, 170999637716685884611362816, 170999637716685884611362816, 6033627844756499204405198848, 66828824542126657651324485632, 6023944609205241656387829760,
    170945330385602243333193728, 6844906646210920988368961536, 243309755393078517228753649664, 243308931109861022277977505792, 6845346867525498763479089152, 70988124535017184218048364544,
    243309755393078517228753649664, 70999902239542511276105138176, 6033600511747205647734669312, 6033627844756499204405198848, 1999431311432143329906655232, 70999902239542511276105138176,
    70999665134918508925660692480, 1999558277998487144102887424, 70987887272075892366835187712, 243308931109861022277977505792, 70999665134918508925660692480, 66828521806658157096302804992,
    66828824542126657651324485632, 1999121677487374832370712576, 6845346867525498763479089152, 1999558277998487144102887424, 6023917322352214780730671104, 6023944609205241656387829760,
    170944558241194330847969280, 170945330385602243333193728, 316912650057057350374175801344, 1584563250285286751870879006720, 1584563250285286751870879006720, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    38, 43, 45, 42, 37, 42,
    47, 45, 40, 42, 43, 42,
    38, 38, 38, 43, 45, 42,
    37, 43, 48, 47, 41, 47,
    48, 47, 43, 43, 42, 47,
    44, 40, 45, 47, 44, 45,
    45, 40, 41, 40, 42, 42,
    37, 37, 0, 2, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 22999996730866427, 23000003267666665, 21881627446126367, 26658733983799607, 24881868861251734,
    21130794885609866, 26281888633383816, 23281883770754731, 18130887243686382, 16144120477449985, 21285081007711035,
    22754453887837745, 20282763798784799, 15143662222853289
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    38144117219229868, 43285077739914948, 45754450620375878, 42282760531262949, 37143658964581539, 42691333192798962,
    47841564357480280, 45841559535566012, 40691424847089527, 42691333192798962, 43467089427479012, 42691648281596645,
    38144117219229868, 38144123735662745, 38144123735662745, 43285084275499723, 45754457155818536, 42282767066299251,
    37143665481117683, 43467089427479012, 48618708917375062, 47618704029813843, 41467182209560369, 47841564357480280,
    48618708917375062, 47841803696484008, 43285077739914948, 43285084275499723, 42691648281596645, 47841803696484008,
    44841798878586583, 40691739891755585, 45841559535566012, 47618704029813843, 44841798878586583, 45754450620375878,
    45754457155818536, 40691424847089527, 41467182209560369, 40691739891755585, 42282760531262949, 42282767066299251,
    37143658964581539, 37143665481117683, 0, 2321928094887363, 2321928094887363, 0
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 48
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
noncomputable def positiveFloor : ℝ := 46599403 / 40000000000
noncomputable def negativeCeiling : ℝ := 291376989 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 170998865339216691409715200, coefficient := (-170998865339216691409715200) }, { argument := 6033600511747205647734669312, coefficient := (-6033600511747205647734669312) }, { argument := 66828521806658157096302804992, coefficient := (-66828521806658157096302804992) }, { argument := 6023917322352214780730671104, coefficient := (-6023917322352214780730671104) }, { argument := 170944558241194330847969280, coefficient := (-170944558241194330847969280) }, { argument := 1998994677495314583830659072, coefficient := (-1998994677495314583830659072) }, { argument := 70988124535017184218048364544, coefficient := (-70988124535017184218048364544) }, { argument := 70987887272075892366835187712, coefficient := (-70987887272075892366835187712) }, { argument := 1999121677487374832370712576, coefficient := (-1999121677487374832370712576) }, { argument := 1998994677495314583830659072, coefficient := (-1998994677495314583830659072) }, { argument := 6844906646210920988368961536, coefficient := (-6844906646210920988368961536) }, { argument := 1999431311432143329906655232, coefficient := (-1999431311432143329906655232) }, { argument := 170998865339216691409715200, coefficient := (-170998865339216691409715200) }, { argument := 170999637716685884611362816, coefficient := (-170999637716685884611362816) }, { argument := 170999637716685884611362816, coefficient := (-170999637716685884611362816) }, { argument := 6033627844756499204405198848, coefficient := (-6033627844756499204405198848) }, { argument := 66828824542126657651324485632, coefficient := (-66828824542126657651324485632) }, { argument := 6023944609205241656387829760, coefficient := (-6023944609205241656387829760) }, { argument := 170945330385602243333193728, coefficient := (-170945330385602243333193728) }, { argument := 6844906646210920988368961536, coefficient := (-6844906646210920988368961536) }, { argument := 243309755393078517228753649664, coefficient := (-243309755393078517228753649664) }, { argument := 243308931109861022277977505792, coefficient := (-243308931109861022277977505792) }, { argument := 6845346867525498763479089152, coefficient := (-6845346867525498763479089152) }, { argument := 70988124535017184218048364544, coefficient := (-70988124535017184218048364544) }, { argument := 243309755393078517228753649664, coefficient := (-243309755393078517228753649664) }, { argument := 70999902239542511276105138176, coefficient := (-70999902239542511276105138176) }, { argument := 6033600511747205647734669312, coefficient := (-6033600511747205647734669312) }, { argument := 6033627844756499204405198848, coefficient := (-6033627844756499204405198848) }, { argument := 1999431311432143329906655232, coefficient := (-1999431311432143329906655232) }, { argument := 70999902239542511276105138176, coefficient := (-70999902239542511276105138176) }, { argument := 70999665134918508925660692480, coefficient := (-70999665134918508925660692480) }, { argument := 1999558277998487144102887424, coefficient := (-1999558277998487144102887424) }, { argument := 70987887272075892366835187712, coefficient := (-70987887272075892366835187712) }, { argument := 243308931109861022277977505792, coefficient := (-243308931109861022277977505792) }, { argument := 70999665134918508925660692480, coefficient := (-70999665134918508925660692480) }, { argument := 66828521806658157096302804992, coefficient := (-66828521806658157096302804992) }, { argument := 66828824542126657651324485632, coefficient := (-66828824542126657651324485632) }, { argument := 1999121677487374832370712576, coefficient := (-1999121677487374832370712576) }, { argument := 6845346867525498763479089152, coefficient := (-6845346867525498763479089152) }, { argument := 1999558277998487144102887424, coefficient := (-1999558277998487144102887424) }, { argument := 6023917322352214780730671104, coefficient := (-6023917322352214780730671104) }, { argument := 6023944609205241656387829760, coefficient := (-6023944609205241656387829760) }, { argument := 170944558241194330847969280, coefficient := (-170944558241194330847969280) }, { argument := 170945330385602243333193728, coefficient := (-170945330385602243333193728) }, { argument := 1901475900342344102245054808064, coefficient := 1901475900342344102245054808064 }, { argument := 158455966128675977094051659776, coefficient := 158455966128675977094051659776 }, { argument := 158456683928381373280124141568, coefficient := 158456683928381373280124141568 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 291948256324151532002169847808, coefficient := 291948256324151532002169847808 }, { argument := 1000617880033351918517158412288, coefficient := 1000617880033351918517158412288 }, { argument := 291997113927783301351550746624, coefficient := 291997113927783301351550746624 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }, { argument := 21686665270276757804212551680, coefficient := 21686665270276757804212551680 }, { argument := 770595564335276425445814304768, coefficient := 770595564335276425445814304768 }, { argument := 770592967033710847140946771968, coefficient := 770592967033710847140946771968 }, { argument := 21688053646022721479905378304, coefficient := 21688053646022721479905378304 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }, { argument := 683997006111805152042156032, coefficient := 683997006111805152042156032 }, { argument := 24134456713007409704279736320, coefficient := 24134456713007409704279736320 }, { argument := 267314692697569629495254581248, coefficient := 267314692697569629495254581248 }, { argument := 24095723863114912874237001728, coefficient := 24095723863114912874237001728 }, { argument := 683779777253593148362326016, coefficient := 683779777253593148362326016 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk3
