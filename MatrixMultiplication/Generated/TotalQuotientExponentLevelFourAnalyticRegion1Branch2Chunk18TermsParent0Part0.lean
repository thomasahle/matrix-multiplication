import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 18, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk18

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
def constantNumerator : ℤ := 81533848726153405014355214336000000
def positiveArguments : Array ℕ := #[
    26915, 3, 57, 87, 897, 27,
    87, 27, 27, 2313, 27, 897,
    2313, 3, 27, 27, 57, 177
  ]
def positiveCoefficients : Array ℕ := #[
    2132425994071424646330235423293440, 3713820117856140824697372672, 4410161389954167229328130048, 3365649481807127622381993984, 34701006726218315830766075904, 4178047632588158427784544256,
    3365649481807127622381993984, 4178047632588158427784544256, 4178047632588158427784544256, 178959706929192785990104645632, 4178047632588158427784544256, 34701006726218315830766075904,
    178959706929192785990104645632, 3713820117856140824697372672, 4178047632588158427784544256, 4178047632588158427784544256, 4410161389954167229328130048, 448748312480793208129832934703104
  ]
def positiveScales : Array ℕ := #[
    14, 1, 5, 6, 9, 4,
    6, 4, 4, 11, 4, 9,
    11, 1, 4, 4, 5, 7
  ]
def negativeArguments : Array ℕ := #[
    626750037, 161, 11552859845, 515, 145, 11552441663,
    73, 73, 5269, 143, 515, 5269,
    627586467, 145, 143, 161, 17064569722345421, 29743846258927667,
    17064569659430861, 4252005433804721, 4252004162271311, 78276183, 161, 17064564618455091,
    29743837498546125, 17064564555540531, 7411615648184399, 7411613465708465, 2886185381, 515,
    145, 4252005418731441, 4252004147198031, 23088641073, 73, 73,
    5269, 143, 515, 5269, 627051503, 145,
    143, 161, 3, 177
  ]
def negativeCoefficients : Array ℕ := #[
    2959743367866110003860840906752, 3114192911327284754043109376, 109113676226637209117409924874240, 39846195014498177598315560960, 2804707901505939685318328320, 109109726609316130329460417232896,
    2824050714619773752113627136, 2824050714619773752113627136, 101917282296791697944429461504, 2766022275278271551727730688, 39846195014498177598315560960, 101917282296791697944429461504,
    2963693296863376661206932652032, 2804707901505939685318328320, 2766022275278271551727730688, 3114192911327284754043109376, 76851989842792686404608056098816, 267908749856543925169455747825664,
    76851989559450697432429343277056, 76597320349041062766567923646464, 76597297443131496906023474561024, 2957190584049365711138737618944, 3114192911327284754043109376, 76851966856914098076730194395136,
    267908670950041828820313440256000, 76851966573572109104551481573376, 267031595771012772118471200735232, 267031517139030347258669427589120, 109037000852662055555408129425408, 39846195014498177598315560960,
    2804707901505939685318328320, 76597320077504990001563323858944, 76597297171595424141018874773504, 109033024738142641385879327735808, 2824050714619773752113627136, 2824050714619773752113627136,
    101917282296791697944429461504, 2766022275278271551727730688, 39846195014498177598315560960, 101917282296791697944429461504, 2961167000800234784324832985088, 2804707901505939685318328320,
    2766022275278271551727730688, 3114192911327284754043109376, 475368975085586025561263702016, 448748312480793208129832934703104
  ]
def negativeScales : Array ℕ := #[
    29, 7, 33, 9, 7, 33,
    6, 6, 12, 7, 9, 12,
    29, 7, 7, 7, 53, 54,
    53, 51, 51, 26, 7, 53,
    54, 53, 52, 52, 31, 9,
    7, 51, 51, 34, 6, 6,
    12, 7, 9, 12, 29, 7,
    7, 7, 1, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14716122804900257, 1584962500720924, 5832890014087662, 6442943495848725, 9808964174871270, 4754887502147955,
    6442943495848725, 4754887502147955, 4754887502147955, 11175549550636190, 4754887502147955, 9808964174871270,
    11175549550636190, 1584962500720924, 4754887502147955, 4754887502147955, 5832890014087662, 7467605550082991
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    29223314935327184, 7330916878114618, 33427530975708694, 9008428622070581, 7179909090014935, 33427478753139995,
    6189824558880018, 6189824558880018, 12363313464373479, 7159871336778390, 9008428622070581, 12363313464373479,
    29225239002095652, 7179909090014935, 7159871336778390, 7330916878114618, 53921853562429442, 54723440736657045,
    53921853557110437, 51917064869769364, 51917064438341079, 26222070071412422, 7330916878114618, 53921853130929597,
    54723440311743576, 53921853125610590, 52718709491398807, 52718709066572720, 31426516821750260, 9008428622070581,
    7179909090014935, 51917064864655036, 51917064433226750, 34426464211854111, 6189824558880018, 6189824558880018,
    12363313464373479, 7159871336778390, 9008428622070581, 12363313464373479, 29224008703037149, 7179909090014935,
    7159871336778390, 7330916878114618, 1584962500724866, 7467605550083086
  ]

abbrev PositiveTerm := Fin 18
abbrev NegativeTerm := Fin 46
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
noncomputable def positiveFloor : ℝ := 1306661641 / 3125000000
noncomputable def negativeCeiling : ℝ := 1301573286199 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2959743367866110003860840906752, coefficient := (-2959743367866110003860840906752) }, { argument := 3114192911327284754043109376, coefficient := (-3114192911327284754043109376) }, { argument := 109113676226637209117409924874240, coefficient := (-109113676226637209117409924874240) }, { argument := 39846195014498177598315560960, coefficient := (-39846195014498177598315560960) }, { argument := 2804707901505939685318328320, coefficient := (-2804707901505939685318328320) }, { argument := 109109726609316130329460417232896, coefficient := (-109109726609316130329460417232896) }, { argument := 2824050714619773752113627136, coefficient := (-2824050714619773752113627136) }, { argument := 2824050714619773752113627136, coefficient := (-2824050714619773752113627136) }, { argument := 101917282296791697944429461504, coefficient := (-101917282296791697944429461504) }, { argument := 2766022275278271551727730688, coefficient := (-2766022275278271551727730688) }, { argument := 39846195014498177598315560960, coefficient := (-39846195014498177598315560960) }, { argument := 101917282296791697944429461504, coefficient := (-101917282296791697944429461504) }, { argument := 2963693296863376661206932652032, coefficient := (-2963693296863376661206932652032) }, { argument := 2804707901505939685318328320, coefficient := (-2804707901505939685318328320) }, { argument := 2766022275278271551727730688, coefficient := (-2766022275278271551727730688) }, { argument := 3114192911327284754043109376, coefficient := (-3114192911327284754043109376) }, { argument := 76851989842792686404608056098816, coefficient := (-76851989842792686404608056098816) }, { argument := 267908749856543925169455747825664, coefficient := (-267908749856543925169455747825664) }, { argument := 76851989559450697432429343277056, coefficient := (-76851989559450697432429343277056) }, { argument := 76597320349041062766567923646464, coefficient := (-76597320349041062766567923646464) }, { argument := 76597297443131496906023474561024, coefficient := (-76597297443131496906023474561024) }, { argument := 2957190584049365711138737618944, coefficient := (-2957190584049365711138737618944) }, { argument := 3114192911327284754043109376, coefficient := (-3114192911327284754043109376) }, { argument := 76851966856914098076730194395136, coefficient := (-76851966856914098076730194395136) }, { argument := 267908670950041828820313440256000, coefficient := (-267908670950041828820313440256000) }, { argument := 76851966573572109104551481573376, coefficient := (-76851966573572109104551481573376) }, { argument := 267031595771012772118471200735232, coefficient := (-267031595771012772118471200735232) }, { argument := 267031517139030347258669427589120, coefficient := (-267031517139030347258669427589120) }, { argument := 109037000852662055555408129425408, coefficient := (-109037000852662055555408129425408) }, { argument := 39846195014498177598315560960, coefficient := (-39846195014498177598315560960) }, { argument := 2804707901505939685318328320, coefficient := (-2804707901505939685318328320) }, { argument := 76597320077504990001563323858944, coefficient := (-76597320077504990001563323858944) }, { argument := 76597297171595424141018874773504, coefficient := (-76597297171595424141018874773504) }, { argument := 109033024738142641385879327735808, coefficient := (-109033024738142641385879327735808) }, { argument := 2824050714619773752113627136, coefficient := (-2824050714619773752113627136) }, { argument := 2824050714619773752113627136, coefficient := (-2824050714619773752113627136) }, { argument := 101917282296791697944429461504, coefficient := (-101917282296791697944429461504) }, { argument := 2766022275278271551727730688, coefficient := (-2766022275278271551727730688) }, { argument := 39846195014498177598315560960, coefficient := (-39846195014498177598315560960) }, { argument := 101917282296791697944429461504, coefficient := (-101917282296791697944429461504) }, { argument := 2961167000800234784324832985088, coefficient := (-2961167000800234784324832985088) }, { argument := 2804707901505939685318328320, coefficient := (-2804707901505939685318328320) }, { argument := 2766022275278271551727730688, coefficient := (-2766022275278271551727730688) }, { argument := 3114192911327284754043109376, coefficient := (-3114192911327284754043109376) }, { argument := 2132425994071424646330235423293440, coefficient := 2132425994071424646330235423293440 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 34701006726218315830766075904, coefficient := 34701006726218315830766075904 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 178959706929192785990104645632, coefficient := 178959706929192785990104645632 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 34701006726218315830766075904, coefficient := 34701006726218315830766075904 }, { argument := 178959706929192785990104645632, coefficient := 178959706929192785990104645632 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 448748312480793208129832934703104, coefficient := 448748312480793208129832934703104 }, { argument := 448748312480793208129832934703104, coefficient := (-448748312480793208129832934703104) }] }

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

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-89499831640631757464836330143875072)
def positiveArguments : Array ℕ := #[
    89133167503, 89133141105, 64988301015, 226556015421, 16247075195, 1252173069,
    47, 23097245017, 1163, 37, 46192811695, 19,
    19, 643, 35, 1163, 643, 626925769,
    37, 35, 47
  ]
def positiveCoefficients : Array ℕ := #[
    841838965456346133893095595442176, 841838716134285304307306893148160, 306898574491879344153929648701440, 1069880533716628873366909816406016, 306898573382123220679563023482880, 5913220131797619574174881153024,
    1818224432700402278758088704, 218147311429817457545195672305664, 44991383302778039365865046016, 1431368170423720942852112384, 218139385697976964587717362974720, 1470053796651389076442710016,
    1470053796651389076442710016, 24874857664390609898754277376, 1353996917968384675670917120, 44991383302778039365865046016, 24874857664390609898754277376, 5921146477545755304707068264448,
    1431368170423720942852112384, 1353996917968384675670917120, 1818224432700402278758088704
  ]
def positiveScales : Array ℕ := #[
    36, 36, 35, 37, 33, 30,
    5, 34, 10, 5, 35, 4,
    4, 9, 5, 10, 9, 29,
    5, 5, 5
  ]
def negativeArguments : Array ℕ := #[
    21251, 21251, 2829
  ]
def negativeCoefficients : Array ℕ := #[
    1683677681590631438200402488590336, 1683677681590631438200402488590336, 448272943505707622104271671001088
  ]
def negativeScales : Array ℕ := #[
    14, 14, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    36375243324370622, 36375242897096798, 35919460980684258, 37721076840951610, 33919460975467421, 30221786832017244,
    5554588851677541, 34427001729634317, 10183635381473218, 5209453365628949, 35426949312661266, 4247927513443585,
    4247927513443585, 9328674927327946, 5129283016944966, 10183635381473218, 9328674927327946, 29223719390267404,
    5209453365628949, 5129283016944966, 5554588851677541
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    14375243110733730, 14375243110733730, 11466076461396337
  ]

abbrev PositiveTerm := Fin 21
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
noncomputable def positiveFloor : ℝ := 333730088327 / 200000000000
noncomputable def negativeCeiling : ℝ := 644542353927 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 841838965456346133893095595442176, coefficient := 841838965456346133893095595442176 }, { argument := 841838716134285304307306893148160, coefficient := 841838716134285304307306893148160 }, { argument := 1683677681590631438200402488590336, coefficient := (-1683677681590631438200402488590336) }, { argument := 306898574491879344153929648701440, coefficient := 306898574491879344153929648701440 }, { argument := 1069880533716628873366909816406016, coefficient := 1069880533716628873366909816406016 }, { argument := 306898573382123220679563023482880, coefficient := 306898573382123220679563023482880 }, { argument := 1683677681590631438200402488590336, coefficient := (-1683677681590631438200402488590336) }, { argument := 5913220131797619574174881153024, coefficient := 5913220131797619574174881153024 }, { argument := 1818224432700402278758088704, coefficient := 1818224432700402278758088704 }, { argument := 218147311429817457545195672305664, coefficient := 218147311429817457545195672305664 }, { argument := 44991383302778039365865046016, coefficient := 44991383302778039365865046016 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 218139385697976964587717362974720, coefficient := 218139385697976964587717362974720 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 24874857664390609898754277376, coefficient := 24874857664390609898754277376 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 44991383302778039365865046016, coefficient := 44991383302778039365865046016 }, { argument := 24874857664390609898754277376, coefficient := 24874857664390609898754277376 }, { argument := 5921146477545755304707068264448, coefficient := 5921146477545755304707068264448 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 1818224432700402278758088704, coefficient := 1818224432700402278758088704 }, { argument := 448272943505707622104271671001088, coefficient := (-448272943505707622104271671001088) }] }

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

end TermShard1


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk18
