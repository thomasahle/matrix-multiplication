import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 21, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk21

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
def constantNumerator : ℤ := (-2206942404386512958462583680008192)
def positiveArguments : Array ℕ := #[
    2387, 15, 267, 15, 475, 811,
    15, 811, 811, 267, 15, 483,
    541, 483, 541, 1, 1179, 10108273769,
    10108271511, 1766313291, 6340765151, 883156587
  ]
def positiveCoefficients : Array ℕ := #[
    189117623921548973835789409452032, 2321137573660088015435857920, 41316248811149566674758270976, 2321137573660088015435857920, 36751344916284726911067750400, 62748085741277712683949359104,
    2321137573660088015435857920, 62748085741277712683949359104, 62748085741277712683949359104, 41316248811149566674758270976, 2321137573660088015435857920, 37370314935927417048517312512,
    41857847578336920545026637824, 37370314935927417048517312512, 41857847578336920545026637824, 158456325028528675187087900672, 93410003604317654022788317446144, 95469946492792045119879352680448,
    95469925166585008480561567629312, 16682357367331156322811560067072, 59886833649660569693475089416192, 16682356262297399331314580062208
  ]
def positiveScales : Array ℕ := #[
    11, 3, 8, 3, 8, 9,
    3, 9, 9, 8, 3, 8,
    9, 8, 9, 0, 10, 33,
    33, 30, 32, 29
  ]
def negativeArguments : Array ℕ := #[
    888515785, 267, 15, 6382431569, 811, 1777031453,
    811, 811, 267, 15, 5053899881, 541,
    5053898761, 541, 439021633, 541, 541, 267,
    15, 5053898743, 541, 5053897623, 541, 6306881133,
    811, 1756086415, 541, 541, 811, 811,
    267, 15, 1, 1, 1, 1179,
    1205, 1177
  ]
def negativeCoefficients : Array ℕ := #[
    8391794325169223739437188382720, 20658124405574783337379135488, 1160568786830044007717928960, 30140180920654721323723101569024, 31374042870638856341974679552, 8391793772652345243688698380288,
    31374042870638856341974679552, 31374042870638856341974679552, 20658124405574783337379135488, 1160568786830044007717928960, 23866367405813288484010433970176, 10464461894584230136256659456,
    23866362116762827670007794630656, 10464461894584230136256659456, 8292884179735592671389807542272, 10464461894584230136256659456, 10464461894584230136256659456, 20658124405574783337379135488,
    1160568786830044007717928960, 23866362031760230978354180784128, 10464461894584230136256659456, 23866356742709770164351541444608, 10464461894584230136256659456, 29783404073922133096663055597568,
    31374042870638856341974679552, 8292883627218714175641317539840, 10464461894584230136256659456, 10464461894584230136256659456, 31374042870638856341974679552, 31374042870638856341974679552,
    20658124405574783337379135488, 1160568786830044007717928960, 316912650057057350374175801344, 158456325028528675187087900672, 158456325028528675187087900672, 93410003604317654022788317446144,
    190939871659377053600440920309760, 93251547279289125347601229545472
  ]
def negativeScales : Array ℕ := #[
    29, 8, 3, 32, 9, 30,
    9, 9, 8, 3, 32, 9,
    32, 9, 28, 9, 9, 8,
    3, 32, 9, 32, 9, 32,
    9, 30, 9, 9, 9, 9,
    8, 3, 0, 0, 0, 10,
    10, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11220982851081776, 3906890595303263, 8060695931687553, 3906890595303263, 8891783702985444, 9663558104215410,
    3906890595303263, 9663558104215410, 9663558104215410, 8060695931687553, 3906890595303263, 8915879378478017,
    9079484783826815, 8915879378478017, 9079484783826815, 0, 10203348002979762, 33234817592252927,
    33234817269981702, 30718094110491022, 32562009797339315, 29718094014927383
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    29726822166031867, 8060695931687554, 3906890600547867, 32571459018451395, 9663558104247244, 30726822071044626,
    9663558104247244, 9663558104247244, 8060695931687554, 3906890600547867, 32234749938408345, 9079484783826816,
    32234749618691164, 9079484783826816, 28709716790186959, 9079484783826816, 9079484783826816, 8060695931687554,
    3906890600547867, 32234749613552851, 9079484783826816, 32234749293835598, 9079484783826816, 32554279596702545,
    9663558104247244, 30709716694066795, 9079484783826816, 9079484783826816, 9663558104247244, 9663558104247244,
    8060695931687554, 3906890600547867, 0, 0, 0, 10203348002979763,
    10234817431117325, 10200898605038445
  ]

abbrev PositiveTerm := Fin 22
abbrev NegativeTerm := Fin 38
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
noncomputable def positiveFloor : ℝ := 149061688613 / 1000000000000
noncomputable def negativeCeiling : ℝ := 14881581303 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8391794325169223739437188382720, coefficient := (-8391794325169223739437188382720) }, { argument := 20658124405574783337379135488, coefficient := (-20658124405574783337379135488) }, { argument := 1160568786830044007717928960, coefficient := (-1160568786830044007717928960) }, { argument := 30140180920654721323723101569024, coefficient := (-30140180920654721323723101569024) }, { argument := 31374042870638856341974679552, coefficient := (-31374042870638856341974679552) }, { argument := 8391793772652345243688698380288, coefficient := (-8391793772652345243688698380288) }, { argument := 31374042870638856341974679552, coefficient := (-31374042870638856341974679552) }, { argument := 31374042870638856341974679552, coefficient := (-31374042870638856341974679552) }, { argument := 20658124405574783337379135488, coefficient := (-20658124405574783337379135488) }, { argument := 1160568786830044007717928960, coefficient := (-1160568786830044007717928960) }, { argument := 23866367405813288484010433970176, coefficient := (-23866367405813288484010433970176) }, { argument := 10464461894584230136256659456, coefficient := (-10464461894584230136256659456) }, { argument := 23866362116762827670007794630656, coefficient := (-23866362116762827670007794630656) }, { argument := 10464461894584230136256659456, coefficient := (-10464461894584230136256659456) }, { argument := 8292884179735592671389807542272, coefficient := (-8292884179735592671389807542272) }, { argument := 10464461894584230136256659456, coefficient := (-10464461894584230136256659456) }, { argument := 10464461894584230136256659456, coefficient := (-10464461894584230136256659456) }, { argument := 20658124405574783337379135488, coefficient := (-20658124405574783337379135488) }, { argument := 1160568786830044007717928960, coefficient := (-1160568786830044007717928960) }, { argument := 23866362031760230978354180784128, coefficient := (-23866362031760230978354180784128) }, { argument := 10464461894584230136256659456, coefficient := (-10464461894584230136256659456) }, { argument := 23866356742709770164351541444608, coefficient := (-23866356742709770164351541444608) }, { argument := 10464461894584230136256659456, coefficient := (-10464461894584230136256659456) }, { argument := 29783404073922133096663055597568, coefficient := (-29783404073922133096663055597568) }, { argument := 31374042870638856341974679552, coefficient := (-31374042870638856341974679552) }, { argument := 8292883627218714175641317539840, coefficient := (-8292883627218714175641317539840) }, { argument := 10464461894584230136256659456, coefficient := (-10464461894584230136256659456) }, { argument := 10464461894584230136256659456, coefficient := (-10464461894584230136256659456) }, { argument := 31374042870638856341974679552, coefficient := (-31374042870638856341974679552) }, { argument := 31374042870638856341974679552, coefficient := (-31374042870638856341974679552) }, { argument := 20658124405574783337379135488, coefficient := (-20658124405574783337379135488) }, { argument := 1160568786830044007717928960, coefficient := (-1160568786830044007717928960) }, { argument := 189117623921548973835789409452032, coefficient := 189117623921548973835789409452032 }, { argument := 2321137573660088015435857920, coefficient := 2321137573660088015435857920 }, { argument := 41316248811149566674758270976, coefficient := 41316248811149566674758270976 }, { argument := 2321137573660088015435857920, coefficient := 2321137573660088015435857920 }, { argument := 36751344916284726911067750400, coefficient := 36751344916284726911067750400 }, { argument := 62748085741277712683949359104, coefficient := 62748085741277712683949359104 }, { argument := 2321137573660088015435857920, coefficient := 2321137573660088015435857920 }, { argument := 62748085741277712683949359104, coefficient := 62748085741277712683949359104 }, { argument := 62748085741277712683949359104, coefficient := 62748085741277712683949359104 }, { argument := 41316248811149566674758270976, coefficient := 41316248811149566674758270976 }, { argument := 2321137573660088015435857920, coefficient := 2321137573660088015435857920 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 37370314935927417048517312512, coefficient := 37370314935927417048517312512 }, { argument := 41857847578336920545026637824, coefficient := 41857847578336920545026637824 }, { argument := 37370314935927417048517312512, coefficient := 37370314935927417048517312512 }, { argument := 41857847578336920545026637824, coefficient := 41857847578336920545026637824 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 93410003604317654022788317446144, coefficient := 93410003604317654022788317446144 }, { argument := 93410003604317654022788317446144, coefficient := (-93410003604317654022788317446144) }, { argument := 95469946492792045119879352680448, coefficient := 95469946492792045119879352680448 }, { argument := 95469925166585008480561567629312, coefficient := 95469925166585008480561567629312 }, { argument := 190939871659377053600440920309760, coefficient := (-190939871659377053600440920309760) }, { argument := 16682357367331156322811560067072, coefficient := 16682357367331156322811560067072 }, { argument := 59886833649660569693475089416192, coefficient := 59886833649660569693475089416192 }, { argument := 16682356262297399331314580062208, coefficient := 16682356262297399331314580062208 }, { argument := 93251547279289125347601229545472, coefficient := (-93251547279289125347601229545472) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk21
