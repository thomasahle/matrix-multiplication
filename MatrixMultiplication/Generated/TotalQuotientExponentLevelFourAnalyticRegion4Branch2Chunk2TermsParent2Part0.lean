import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 2, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk2

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
def constantNumerator : ℤ := 224638490640255496399569813504
def positiveArguments : Array ℕ := #[
    1, 4194309, 4194299, 6073069, 21401569, 3039897,
    84047, 8220507, 4110255, 168105
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 79228256961593994986448224256, 79228068066934680200639676416, 57358514987509346776591106048, 202132104252844060092869378048, 57422030816703943504715317248,
    1587602943142980285102030848, 77640493457990597133408927744, 77640521792189494351280209920, 1587706835205603417296732160
  ]
def positiveScales : Array ℕ := #[
    0, 22, 21, 22, 24, 21,
    16, 22, 21, 17
  ]
def negativeArguments : Array ℕ := #[
    352519088523, 34479346494663, 17239679538795, 705084314445, 2305088694435, 64987366712667,
    18461114127757, 352519088523, 352518248053, 352518248053, 34479264289593, 17239638436245,
    705082633395, 64987366712667, 57253004177829, 65059362427921, 34479346494663, 34479264289593,
    18461114127757, 65059362427921, 9240770308913, 17239679538795, 17239638436245, 705084314445,
    705082633395, 1, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    396901208928292423285604352, 19410146503167813031198457856, 19410153586725981584967598080, 396927181974910453772451840, 5190598292656704558339194880, 18292317531934804799549079552,
    5196341669163164030407278592, 396901208928292423285604352, 396900262643197719265411072, 396900262643197719265411072, 19410100225827485535506006016, 19410107309368765590672506880,
    396926235627891254875914240, 18292317531934804799549079552, 64461152070278033776412983296, 18312582524209191470472626176, 19410146503167813031198457856, 19410100225827485535506006016,
    5196341669163164030407278592, 18312582524209191470472626176, 5202091214979616251477753856, 19410153586725981584967598080, 19410107309368765590672506880, 396927181974910453772451840,
    396926235627891254875914240, 158456325028528675187087900672, 316912650057057350374175801344, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    38, 44, 43, 39, 41, 45,
    44, 38, 38, 38, 44, 43,
    39, 45, 45, 45, 44, 44,
    44, 45, 43, 43, 43, 39,
    39, 0, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 22000001719825483, 21999998278712924, 22533994329981286, 24351213232124995, 21535591011378958,
    16358908703920281, 22970795943322402, 21970796469820861, 17359003110182379
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    38358910423745767, 44970797678805384, 43970798205303979, 39359004830007865, 41067959401910214, 45885224528059904,
    44069554855754897, 38358910423745767, 38358906984092750, 38358906984092750, 44970794239151531, 43970794765650126,
    39359001390354848, 45885224528059904, 45702416629856739, 45886821921229063, 44970797678805384, 44970794239151531,
    44069554855754897, 45886821921229063, 43071150258095710, 43970798205303979, 43970794765650126, 39359004830007865,
    39359001390354848, 0, 0, 0
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 28
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
noncomputable def positiveFloor : ℝ := 17429853 / 100000000000
noncomputable def negativeCeiling : ℝ := 171280473 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 396901208928292423285604352, coefficient := (-396901208928292423285604352) }, { argument := 19410146503167813031198457856, coefficient := (-19410146503167813031198457856) }, { argument := 19410153586725981584967598080, coefficient := (-19410153586725981584967598080) }, { argument := 396927181974910453772451840, coefficient := (-396927181974910453772451840) }, { argument := 5190598292656704558339194880, coefficient := (-5190598292656704558339194880) }, { argument := 18292317531934804799549079552, coefficient := (-18292317531934804799549079552) }, { argument := 5196341669163164030407278592, coefficient := (-5196341669163164030407278592) }, { argument := 396901208928292423285604352, coefficient := (-396901208928292423285604352) }, { argument := 396900262643197719265411072, coefficient := (-396900262643197719265411072) }, { argument := 396900262643197719265411072, coefficient := (-396900262643197719265411072) }, { argument := 19410100225827485535506006016, coefficient := (-19410100225827485535506006016) }, { argument := 19410107309368765590672506880, coefficient := (-19410107309368765590672506880) }, { argument := 396926235627891254875914240, coefficient := (-396926235627891254875914240) }, { argument := 18292317531934804799549079552, coefficient := (-18292317531934804799549079552) }, { argument := 64461152070278033776412983296, coefficient := (-64461152070278033776412983296) }, { argument := 18312582524209191470472626176, coefficient := (-18312582524209191470472626176) }, { argument := 19410146503167813031198457856, coefficient := (-19410146503167813031198457856) }, { argument := 19410100225827485535506006016, coefficient := (-19410100225827485535506006016) }, { argument := 5196341669163164030407278592, coefficient := (-5196341669163164030407278592) }, { argument := 18312582524209191470472626176, coefficient := (-18312582524209191470472626176) }, { argument := 5202091214979616251477753856, coefficient := (-5202091214979616251477753856) }, { argument := 19410153586725981584967598080, coefficient := (-19410153586725981584967598080) }, { argument := 19410107309368765590672506880, coefficient := (-19410107309368765590672506880) }, { argument := 396927181974910453772451840, coefficient := (-396927181974910453772451840) }, { argument := 396926235627891254875914240, coefficient := (-396926235627891254875914240) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 79228256961593994986448224256, coefficient := 79228256961593994986448224256 }, { argument := 79228068066934680200639676416, coefficient := 79228068066934680200639676416 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 57358514987509346776591106048, coefficient := 57358514987509346776591106048 }, { argument := 202132104252844060092869378048, coefficient := 202132104252844060092869378048 }, { argument := 57422030816703943504715317248, coefficient := 57422030816703943504715317248 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 1587602943142980285102030848, coefficient := 1587602943142980285102030848 }, { argument := 77640493457990597133408927744, coefficient := 77640493457990597133408927744 }, { argument := 77640521792189494351280209920, coefficient := 77640521792189494351280209920 }, { argument := 1587706835205603417296732160, coefficient := 1587706835205603417296732160 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk2
