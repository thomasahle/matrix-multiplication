import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 0, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk0

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
def constantNumerator : ℤ := 158456325028528675187087900672
def positiveArguments : Array ℕ := #[
    1, 40359, 66303, 14579815, 528377, 2465,
    169551, 8219023, 4110085, 21059
  ]
def positiveCoefficients : Array ℕ := #[
    158456325028528675187087900672, 381179977764272022359113728, 10019426077238594771317948416, 137702459364880192662646292480, 9980759340476858116308205568, 372500268168757614456340480,
    1601363919074062431254740992, 77626477474269440026414678016, 77637310582981142992534896640, 1591173052204029736883585024
  ]
def positiveScales : Array ℕ := #[
    0, 15, 16, 23, 19, 11,
    17, 22, 21, 14
  ]
def negativeArguments : Array ℕ := #[
    6842908809, 331711549257, 165878920515, 849920181, 11241739953, 544945881969,
    272510965755, 1396274877, 6842908809, 11241739953, 2472022213065, 89586848727,
    417943215, 2472022213065, 119831834820745, 59924278934275, 307036324085, 331711549257,
    544945881969, 119831834820745, 4342742715671, 20259891695, 89586848727, 4342742715671,
    2171674382045, 11127091243, 165878920515, 272510965755, 59924278934275, 2171674382045,
    10131359525, 417943215, 20259891695, 10131359525, 51910435, 849920181,
    1396274877, 307036324085, 11127091243, 51910435, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1926107597646417786568704, 93368500601769695580782592, 93381530577496765555015680, 1913850105223132257189888, 50628295863326817216626688, 2454218070972674695048986624,
    2454560567657183992306728960, 50306104126111881086631936, 1926107597646417786568704, 50628295863326817216626688, 695812394850695179287920640, 50432912318026774241869824,
    1882248907336027094384640, 695812394850695179287920640, 33729662915364375583491358720, 33734370034855819145432268800, 691384337369206423111598080, 93368500601769695580782592,
    2454218070972674695048986624, 33729662915364375583491358720, 2444746809507731432487780352, 91242440688168606598430720, 50432912318026774241869824, 2444746809507731432487780352,
    2445087984436978542266286080, 50111963975692309158166528, 93381530577496765555015680, 2454560567657183992306728960, 33734370034855819145432268800, 2445087984436978542266286080,
    91255173963093050707148800, 1882248907336027094384640, 91242440688168606598430720, 91255173963093050707148800, 1870270525781122828206080, 1913850105223132257189888,
    50306104126111881086631936, 691384337369206423111598080, 50111963975692309158166528, 1870270525781122828206080, 158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    32, 38, 37, 29, 33, 38,
    37, 30, 32, 33, 41, 36,
    28, 41, 46, 45, 38, 38,
    38, 46, 41, 34, 36, 41,
    40, 33, 37, 37, 45, 40,
    33, 28, 34, 33, 25, 29,
    30, 38, 33, 25, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 15300602807885839, 16016786528729018, 23797469077920961, 19011208142558024, 11267371931265273,
    17371359767740210, 22970535478526328, 21970736798772385, 14362149310248596
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32671962575662946, 38271138287318136, 37271339607567199, 29662752118163812, 33388146296469235, 38987322027476417,
    37987523347788470, 30378935838977619, 32671962575662946, 33388146296469235, 41168828845699186, 36382567910298240,
    28638731699021438, 41168828845699186, 46768004557722914, 45768205877973403, 38159618388207572, 38271138287318136,
    38987322027476417, 46768004557722914, 41981743639633943, 34237907410697569, 36382567910298240, 41981743639633943,
    40981944959940912, 33373357452806625, 37271339607567199, 37987523347788470, 45768205877973403, 40981944959940912,
    33238108730946633, 28638731699021438, 34237907410697569, 33238108730946633, 25629521241526414, 29662752118163812,
    30378935838977619, 38159618388207572, 33373357452806625, 25629521241526414, 0, 0
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 42
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
noncomputable def positiveFloor : ℝ := 86387177 / 1000000000000
noncomputable def negativeCeiling : ℝ := 43193589 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1926107597646417786568704, coefficient := (-1926107597646417786568704) }, { argument := 93368500601769695580782592, coefficient := (-93368500601769695580782592) }, { argument := 93381530577496765555015680, coefficient := (-93381530577496765555015680) }, { argument := 1913850105223132257189888, coefficient := (-1913850105223132257189888) }, { argument := 50628295863326817216626688, coefficient := (-50628295863326817216626688) }, { argument := 2454218070972674695048986624, coefficient := (-2454218070972674695048986624) }, { argument := 2454560567657183992306728960, coefficient := (-2454560567657183992306728960) }, { argument := 50306104126111881086631936, coefficient := (-50306104126111881086631936) }, { argument := 1926107597646417786568704, coefficient := (-1926107597646417786568704) }, { argument := 50628295863326817216626688, coefficient := (-50628295863326817216626688) }, { argument := 695812394850695179287920640, coefficient := (-695812394850695179287920640) }, { argument := 50432912318026774241869824, coefficient := (-50432912318026774241869824) }, { argument := 1882248907336027094384640, coefficient := (-1882248907336027094384640) }, { argument := 695812394850695179287920640, coefficient := (-695812394850695179287920640) }, { argument := 33729662915364375583491358720, coefficient := (-33729662915364375583491358720) }, { argument := 33734370034855819145432268800, coefficient := (-33734370034855819145432268800) }, { argument := 691384337369206423111598080, coefficient := (-691384337369206423111598080) }, { argument := 93368500601769695580782592, coefficient := (-93368500601769695580782592) }, { argument := 2454218070972674695048986624, coefficient := (-2454218070972674695048986624) }, { argument := 33729662915364375583491358720, coefficient := (-33729662915364375583491358720) }, { argument := 2444746809507731432487780352, coefficient := (-2444746809507731432487780352) }, { argument := 91242440688168606598430720, coefficient := (-91242440688168606598430720) }, { argument := 50432912318026774241869824, coefficient := (-50432912318026774241869824) }, { argument := 2444746809507731432487780352, coefficient := (-2444746809507731432487780352) }, { argument := 2445087984436978542266286080, coefficient := (-2445087984436978542266286080) }, { argument := 50111963975692309158166528, coefficient := (-50111963975692309158166528) }, { argument := 93381530577496765555015680, coefficient := (-93381530577496765555015680) }, { argument := 2454560567657183992306728960, coefficient := (-2454560567657183992306728960) }, { argument := 33734370034855819145432268800, coefficient := (-33734370034855819145432268800) }, { argument := 2445087984436978542266286080, coefficient := (-2445087984436978542266286080) }, { argument := 91255173963093050707148800, coefficient := (-91255173963093050707148800) }, { argument := 1882248907336027094384640, coefficient := (-1882248907336027094384640) }, { argument := 91242440688168606598430720, coefficient := (-91242440688168606598430720) }, { argument := 91255173963093050707148800, coefficient := (-91255173963093050707148800) }, { argument := 1870270525781122828206080, coefficient := (-1870270525781122828206080) }, { argument := 1913850105223132257189888, coefficient := (-1913850105223132257189888) }, { argument := 50306104126111881086631936, coefficient := (-50306104126111881086631936) }, { argument := 691384337369206423111598080, coefficient := (-691384337369206423111598080) }, { argument := 50111963975692309158166528, coefficient := (-50111963975692309158166528) }, { argument := 1870270525781122828206080, coefficient := (-1870270525781122828206080) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 381179977764272022359113728, coefficient := 381179977764272022359113728 }, { argument := 10019426077238594771317948416, coefficient := 10019426077238594771317948416 }, { argument := 137702459364880192662646292480, coefficient := 137702459364880192662646292480 }, { argument := 9980759340476858116308205568, coefficient := 9980759340476858116308205568 }, { argument := 372500268168757614456340480, coefficient := 372500268168757614456340480 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1601363919074062431254740992, coefficient := 1601363919074062431254740992 }, { argument := 77626477474269440026414678016, coefficient := 77626477474269440026414678016 }, { argument := 77637310582981142992534896640, coefficient := 77637310582981142992534896640 }, { argument := 1591173052204029736883585024, coefficient := 1591173052204029736883585024 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk0
