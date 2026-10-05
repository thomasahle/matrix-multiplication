import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 5, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk5

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
def constantNumerator : ℤ := 399183475610516468079523790848
def positiveArguments : Array ℕ := #[
    9, 378999, 10713263, 3031961, 1098013, 20422515,
    20422527, 1097983, 106365, 10041, 28205277, 1284761,
    25693
  ]
def positiveCoefficients : Array ℕ := #[
    1426106925256758076683791106048, 114545419177031210646116499456, 404735632906940031128131600384, 114544248030143458974103502848, 20740879155820591000103944192, 771540802655220579371078123520,
    771541256002402934857018638336, 20740312471842646642678300672, 2009178043801719252619100160, 48555296619001966172898852864, 532782618979416392576079495168, 48536898279184706035146293248,
    1941308192709916711607861248
  ]
def positiveScales : Array ℕ := #[
    3, 18, 23, 21, 20, 24,
    24, 20, 16, 13, 24, 20,
    14
  ]
def negativeArguments : Array ℕ := #[
    161284995215, 243496259881, 42760881246937, 973602893403, 38966680103, 59918176401,
    4485564751357, 4485566609173, 29958230643, 161284995215, 569681101865, 20161024105,
    569681101865, 1721395826189, 75540722993825, 13766060244313, 137593368117, 4485564751357,
    333661839508387, 333662037120355, 35042518379, 243496259881, 1721395826189, 486972067745,
    20161024105, 486972067745, 42760685049829, 3894240987451, 9742114281, 4485566609173,
    333662037120355, 333662234730787, 560680526261, 42760881246937, 75540722993825, 42760685049829,
    29958230643, 35042518379, 560680526261, 29957373123, 973602893403, 13766060244313,
    3894240987451, 38966680103, 137593368117, 9742114281, 1, 5,
    1
  ]
def negativeCoefficients : Array ℕ := #[
    181590761087681557598044160, 4386438661064724218751483904, 48144472212434875887741042688, 4384717627936587538275237888, 175490325991736120692441088, 134923738456131623555432448,
    5050296935689404185489440768, 5050299027404265516225789952, 134919876360494174781308928, 181590761087681557598044160, 641403899519806893467893760, 181594361293371175243612160,
    641403899519806893467893760, 15504955202763814999045439488, 170102585963144064504797593600, 15499205946661956481881997312, 619665441380372684872876032, 5050296935689404185489440768,
    187834917009715741682768543744, 187835028255363922776566005760, 5050159126841221040715071488, 4386438661064724218751483904, 15504955202763814999045439488, 4386254445672443868652503040,
    181594361293371175243612160, 4386254445672443868652503040, 48144251314129255895501111296, 4384525564993808997415911424, 175498328982849550238613504, 5050299027404265516225789952,
    187835028255363922776566005760, 187835139500147412741908332544, 5050161218285866393809190912, 48144472212434875887741042688, 170102585963144064504797593600, 48144251314129255895501111296,
    134919876360494174781308928, 5050159126841221040715071488, 5050161218285866393809190912, 134916014433741712033579008, 4384717627936587538275237888, 15499205946661956481881997312,
    4384525564993808997415911424, 175490325991736120692441088, 619665441380372684872876032, 175498328982849550238613504, 633825300114114700748351602688, 1584563250285286751870879006720,
    633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    37, 37, 45, 39, 35, 35,
    42, 42, 34, 37, 39, 34,
    39, 40, 46, 43, 37, 42,
    48, 48, 35, 37, 40, 38,
    34, 38, 45, 41, 33, 42,
    48, 48, 39, 45, 46, 45,
    34, 35, 39, 34, 39, 43,
    41, 35, 37, 33, 0, 2,
    0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 18531834516244887, 23352894621138954, 21531819765620577, 20066463704654995, 24283657206950472,
    24283658054658769, 20066424286685901, 16698663976462904, 13293615336407685, 24749461769712197, 20293068573736175,
    14649087733486068
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    37230821270625075, 37825108657414251, 45281356818995543, 39824542500350970, 35181521970373765, 35802274665849126,
    42028426776566315, 42028427374096731, 34802233369142481, 37230821270625075, 39051363591977869, 34230849873112207,
    39051363591977869, 40646716014558045, 46102319825291218, 43646180962290308, 37001619978806145, 42028426776566315,
    48245380025131756, 48245380879570856, 35028387408810909, 37825108657414251, 40646716014558045, 38825048067892812,
    34230849873112207, 38825048067892812, 45281350199551886, 41824479304872225, 33181587760965171, 42028427374096731,
    48245380879570856, 48245381734002809, 39028388006280438, 45281356818995543, 46102319825291218, 45281350199551886,
    34802233369142481, 35028387408810909, 39028388006280438, 34802192073059632, 39824542500350970, 43646180962290308,
    41824479304872225, 35181521970373765, 37001619978806145, 33181587760965171, 0, 2321928094887363,
    0
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
noncomputable def positiveFloor : ℝ := 215896897 / 250000000000
noncomputable def negativeCeiling : ℝ := 843750243 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 181590761087681557598044160, coefficient := (-181590761087681557598044160) }, { argument := 4386438661064724218751483904, coefficient := (-4386438661064724218751483904) }, { argument := 48144472212434875887741042688, coefficient := (-48144472212434875887741042688) }, { argument := 4384717627936587538275237888, coefficient := (-4384717627936587538275237888) }, { argument := 175490325991736120692441088, coefficient := (-175490325991736120692441088) }, { argument := 134923738456131623555432448, coefficient := (-134923738456131623555432448) }, { argument := 5050296935689404185489440768, coefficient := (-5050296935689404185489440768) }, { argument := 5050299027404265516225789952, coefficient := (-5050299027404265516225789952) }, { argument := 134919876360494174781308928, coefficient := (-134919876360494174781308928) }, { argument := 181590761087681557598044160, coefficient := (-181590761087681557598044160) }, { argument := 641403899519806893467893760, coefficient := (-641403899519806893467893760) }, { argument := 181594361293371175243612160, coefficient := (-181594361293371175243612160) }, { argument := 641403899519806893467893760, coefficient := (-641403899519806893467893760) }, { argument := 15504955202763814999045439488, coefficient := (-15504955202763814999045439488) }, { argument := 170102585963144064504797593600, coefficient := (-170102585963144064504797593600) }, { argument := 15499205946661956481881997312, coefficient := (-15499205946661956481881997312) }, { argument := 619665441380372684872876032, coefficient := (-619665441380372684872876032) }, { argument := 5050296935689404185489440768, coefficient := (-5050296935689404185489440768) }, { argument := 187834917009715741682768543744, coefficient := (-187834917009715741682768543744) }, { argument := 187835028255363922776566005760, coefficient := (-187835028255363922776566005760) }, { argument := 5050159126841221040715071488, coefficient := (-5050159126841221040715071488) }, { argument := 4386438661064724218751483904, coefficient := (-4386438661064724218751483904) }, { argument := 15504955202763814999045439488, coefficient := (-15504955202763814999045439488) }, { argument := 4386254445672443868652503040, coefficient := (-4386254445672443868652503040) }, { argument := 181594361293371175243612160, coefficient := (-181594361293371175243612160) }, { argument := 4386254445672443868652503040, coefficient := (-4386254445672443868652503040) }, { argument := 48144251314129255895501111296, coefficient := (-48144251314129255895501111296) }, { argument := 4384525564993808997415911424, coefficient := (-4384525564993808997415911424) }, { argument := 175498328982849550238613504, coefficient := (-175498328982849550238613504) }, { argument := 5050299027404265516225789952, coefficient := (-5050299027404265516225789952) }, { argument := 187835028255363922776566005760, coefficient := (-187835028255363922776566005760) }, { argument := 187835139500147412741908332544, coefficient := (-187835139500147412741908332544) }, { argument := 5050161218285866393809190912, coefficient := (-5050161218285866393809190912) }, { argument := 48144472212434875887741042688, coefficient := (-48144472212434875887741042688) }, { argument := 170102585963144064504797593600, coefficient := (-170102585963144064504797593600) }, { argument := 48144251314129255895501111296, coefficient := (-48144251314129255895501111296) }, { argument := 134919876360494174781308928, coefficient := (-134919876360494174781308928) }, { argument := 5050159126841221040715071488, coefficient := (-5050159126841221040715071488) }, { argument := 5050161218285866393809190912, coefficient := (-5050161218285866393809190912) }, { argument := 134916014433741712033579008, coefficient := (-134916014433741712033579008) }, { argument := 4384717627936587538275237888, coefficient := (-4384717627936587538275237888) }, { argument := 15499205946661956481881997312, coefficient := (-15499205946661956481881997312) }, { argument := 4384525564993808997415911424, coefficient := (-4384525564993808997415911424) }, { argument := 175490325991736120692441088, coefficient := (-175490325991736120692441088) }, { argument := 619665441380372684872876032, coefficient := (-619665441380372684872876032) }, { argument := 175498328982849550238613504, coefficient := (-175498328982849550238613504) }, { argument := 1426106925256758076683791106048, coefficient := 1426106925256758076683791106048 }, { argument := 114545419177031210646116499456, coefficient := 114545419177031210646116499456 }, { argument := 404735632906940031128131600384, coefficient := 404735632906940031128131600384 }, { argument := 114544248030143458974103502848, coefficient := 114544248030143458974103502848 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 20740879155820591000103944192, coefficient := 20740879155820591000103944192 }, { argument := 771540802655220579371078123520, coefficient := 771540802655220579371078123520 }, { argument := 771541256002402934857018638336, coefficient := 771541256002402934857018638336 }, { argument := 20740312471842646642678300672, coefficient := 20740312471842646642678300672 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }, { argument := 2009178043801719252619100160, coefficient := 2009178043801719252619100160 }, { argument := 48555296619001966172898852864, coefficient := 48555296619001966172898852864 }, { argument := 532782618979416392576079495168, coefficient := 532782618979416392576079495168 }, { argument := 48536898279184706035146293248, coefficient := 48536898279184706035146293248 }, { argument := 1941308192709916711607861248, coefficient := 1941308192709916711607861248 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk5
