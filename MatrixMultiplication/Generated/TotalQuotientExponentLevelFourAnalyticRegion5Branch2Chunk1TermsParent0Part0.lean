import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 1, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk1

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 474959097436301423527306723328
def positiveArguments : Array ℕ := #[
    3, 323001, 24519813, 24519803, 323015, 74163,
    1976321, 42132855, 3950303, 73761
  ]
def positiveCoefficients : Array ℕ := #[
    475368975085586025561263702016, 6101316385333513094676086784, 231583086154862808032341917696, 231582991707533150639437643776, 6101580837856553794808053760, 1400899461876245991933345792,
    37331648199165680393507569664, 397933564559213491380195164160, 37309556968758816193197899776, 1393305896571791602429722624
  ]
def positiveScales : Array ℕ := #[
    1, 18, 24, 24, 18, 16,
    20, 25, 21, 16
  ]
def negativeArguments : Array ℕ := #[
    15800661783, 427723206239, 4532279375835, 106880118169, 15733828683, 15800661783,
    606323517495, 606323067827, 15801423103, 606323517495, 16150852167041, 344371322548905,
    32282488815413, 603018123609, 427723206239, 16150852167041, 16150848157521, 427740771535,
    606323067827, 16150848157521, 344371172438255, 32282480921703, 603017698897, 4532279375835,
    344371322548905, 344371172438255, 4532477646425, 15801423103, 427740771535, 4532477646425,
    213769003495, 15734578187, 106880118169, 32282488815413, 32282480921703, 213769003495,
    15733828683, 603018123609, 603017698897, 15734578187, 3, 3
  ]
def negativeCoefficients : Array ℕ := #[
    8894981814765754616119296, 240786759029459276233965568, 2551446463518686274146795520, 240672630179611489612070912, 8857358124233752729092096, 8894981814765754616119296,
    341329795932056301537853440, 341329542791476646483329024, 8895410399824293329371136, 341329795932056301537853440, 9092121475150226927273377792, 96931909994270840298594631680,
    9086712787480386976694140928, 339469024597893512070955008, 240786759029459276233965568, 9092121475150226927273377792, 9092119217991129685454487552, 240796647412024307791953920,
    341329542791476646483329024, 9092119217991129685454487552, 96931867741879127527160545280, 9086710565598548566021767168, 339468785506292894598692864, 2551446463518686274146795520,
    96931909994270840298594631680, 96931867741879127527160545280, 2551558079938091590195609600, 8895410399824293329371136, 240796647412024307791953920, 2551558079938091590195609600,
    240682501120861064270970880, 8857780057475641816121344, 240672630179611489612070912, 9086712787480386976694140928, 9086710565598548566021767168, 240682501120861064270970880,
    8857358124233752729092096, 339469024597893512070955008, 339468785506292894598692864, 8857780057475641816121344, 475368975085586025561263702016, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    33, 38, 42, 36, 33, 33,
    39, 39, 33, 39, 43, 48,
    44, 39, 38, 43, 43, 38,
    39, 43, 48, 44, 39, 42,
    48, 48, 42, 33, 38, 42,
    37, 33, 36, 44, 44, 37,
    33, 39, 39, 33, 1, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 18301179105897211, 24547444640589199, 24547444052209779, 18301241636022086, 16178411983782348,
    20914385861797380, 25328442343102129, 21913531885519264, 16170570594498659
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    33879265936289605, 38637886526926510, 42043373932222718, 36637202551777044, 33873150731640864, 33879265936289605,
    39141296825156426, 39141295755209416, 33879335447693887, 39141296825156426, 43876675524205982, 48290958336026911,
    44875817043689029, 39133410406496469, 38637886526926510, 43876675524205982, 43876675166050537, 38637945772823715,
    39141295755209416, 43876675166050537, 48290957707159397, 44875816690921362, 39133409390390836, 42043373932222718,
    48290958336026911, 48290957707159397, 42043437043455879, 33879335447693887, 38637945772823715, 42043437043455879,
    37637261721222102, 33873219454901135, 36637202551777044, 44875817043689029, 44875816690921362, 37637261721222102,
    33873150731640864, 39133410406496469, 39133409390390836, 33873219454901135, 1584962500724866, 1584962500724866
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
noncomputable def positiveFloor : ℝ := 289718823 / 1000000000000
noncomputable def negativeCeiling : ℝ := 289713891 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8894981814765754616119296, coefficient := (-8894981814765754616119296) }, { argument := 240786759029459276233965568, coefficient := (-240786759029459276233965568) }, { argument := 2551446463518686274146795520, coefficient := (-2551446463518686274146795520) }, { argument := 240672630179611489612070912, coefficient := (-240672630179611489612070912) }, { argument := 8857358124233752729092096, coefficient := (-8857358124233752729092096) }, { argument := 8894981814765754616119296, coefficient := (-8894981814765754616119296) }, { argument := 341329795932056301537853440, coefficient := (-341329795932056301537853440) }, { argument := 341329542791476646483329024, coefficient := (-341329542791476646483329024) }, { argument := 8895410399824293329371136, coefficient := (-8895410399824293329371136) }, { argument := 341329795932056301537853440, coefficient := (-341329795932056301537853440) }, { argument := 9092121475150226927273377792, coefficient := (-9092121475150226927273377792) }, { argument := 96931909994270840298594631680, coefficient := (-96931909994270840298594631680) }, { argument := 9086712787480386976694140928, coefficient := (-9086712787480386976694140928) }, { argument := 339469024597893512070955008, coefficient := (-339469024597893512070955008) }, { argument := 240786759029459276233965568, coefficient := (-240786759029459276233965568) }, { argument := 9092121475150226927273377792, coefficient := (-9092121475150226927273377792) }, { argument := 9092119217991129685454487552, coefficient := (-9092119217991129685454487552) }, { argument := 240796647412024307791953920, coefficient := (-240796647412024307791953920) }, { argument := 341329542791476646483329024, coefficient := (-341329542791476646483329024) }, { argument := 9092119217991129685454487552, coefficient := (-9092119217991129685454487552) }, { argument := 96931867741879127527160545280, coefficient := (-96931867741879127527160545280) }, { argument := 9086710565598548566021767168, coefficient := (-9086710565598548566021767168) }, { argument := 339468785506292894598692864, coefficient := (-339468785506292894598692864) }, { argument := 2551446463518686274146795520, coefficient := (-2551446463518686274146795520) }, { argument := 96931909994270840298594631680, coefficient := (-96931909994270840298594631680) }, { argument := 96931867741879127527160545280, coefficient := (-96931867741879127527160545280) }, { argument := 2551558079938091590195609600, coefficient := (-2551558079938091590195609600) }, { argument := 8895410399824293329371136, coefficient := (-8895410399824293329371136) }, { argument := 240796647412024307791953920, coefficient := (-240796647412024307791953920) }, { argument := 2551558079938091590195609600, coefficient := (-2551558079938091590195609600) }, { argument := 240682501120861064270970880, coefficient := (-240682501120861064270970880) }, { argument := 8857780057475641816121344, coefficient := (-8857780057475641816121344) }, { argument := 240672630179611489612070912, coefficient := (-240672630179611489612070912) }, { argument := 9086712787480386976694140928, coefficient := (-9086712787480386976694140928) }, { argument := 9086710565598548566021767168, coefficient := (-9086710565598548566021767168) }, { argument := 240682501120861064270970880, coefficient := (-240682501120861064270970880) }, { argument := 8857358124233752729092096, coefficient := (-8857358124233752729092096) }, { argument := 339469024597893512070955008, coefficient := (-339469024597893512070955008) }, { argument := 339468785506292894598692864, coefficient := (-339468785506292894598692864) }, { argument := 8857780057475641816121344, coefficient := (-8857780057475641816121344) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 6101316385333513094676086784, coefficient := 6101316385333513094676086784 }, { argument := 231583086154862808032341917696, coefficient := 231583086154862808032341917696 }, { argument := 231582991707533150639437643776, coefficient := 231582991707533150639437643776 }, { argument := 6101580837856553794808053760, coefficient := 6101580837856553794808053760 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 1400899461876245991933345792, coefficient := 1400899461876245991933345792 }, { argument := 37331648199165680393507569664, coefficient := 37331648199165680393507569664 }, { argument := 397933564559213491380195164160, coefficient := 397933564559213491380195164160 }, { argument := 37309556968758816193197899776, coefficient := 37309556968758816193197899776 }, { argument := 1393305896571791602429722624, coefficient := 1393305896571791602429722624 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk1
