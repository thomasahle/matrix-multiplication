import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 9, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk9

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
def constantNumerator : ℤ := (-29681052810867932161193132687360)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2313, 1093527, 244933, 244357, 243013, 244357,
    41509413, 8489083, 8488651, 8487643, 8488651, 4883,
    19475, 9671, 19475, 12593, 50225, 24941,
    50225, 10537, 42025, 20869, 42025, 294779,
    1175675, 583823, 1175675, 4374111, 2121243, 1060569,
    2120893, 1060569, 10537, 42025, 20869, 42025,
    9509, 37925, 18833, 37925, 244933, 8489083,
    4883, 12593, 10537, 294779, 2121243, 10537,
    9509, 4883, 4883, 9509, 294779, 9509,
    61233, 12593, 4883, 19475, 9671, 19475,
    4883, 19475, 9671, 19475
  ]
def negativeCoefficients : Array ℕ := #[
    174765338798039830068461568, 20656141011651978086389383168, 289165847437177702781550592, 288485826663644473870778368, 286899111525400273078976512, 288485826663644473870778368,
    196022660674793528338780520448, 10022140257374624099904520192, 10021630241794474178221441024, 10020440205440791027627589632, 10021630241794474178221441024, 184474524286819820627820544,
    183936174507772681073459200, 182680025023329355446616064, 183936174507772681073459200, 237875044475109768704294912, 237180856602127930857881600, 235561084898503642549583872,
    237180856602127930857881600, 3184612840319836903469744128, 3175319223081549441689190400, 3153634116192212030867898368, 3175319223081549441689190400, 5568217877815324585792372736,
    5551968214747770136612044800, 5514052334256809755191279616, 5551968214747770136612044800, 20656155178751426695325024256, 10017286845221854822036144128, 10016790996741153509288706048,
    10015634016952850446211350528, 10016790996741153509288706048, 3184612840319836903469744128, 3175319223081549441689190400, 3153634116192212030867898368, 3175319223081549441689190400,
    179619931542429825348141056, 179095748862831294729420800, 177872655943768056619073536, 179095748862831294729420800, 289165847437177702781550592, 10022140257374624099904520192,
    184474524286819820627820544, 237875044475109768704294912, 3184612840319836903469744128, 5568217877815324585792372736, 10017286845221854822036144128, 3184612840319836903469744128,
    179619931542429825348141056, 184474524286819820627820544, 184474524286819820627820544, 179619931542429825348141056, 5568217877815324585792372736, 179619931542429825348141056,
    289164666845556985370247168, 237875044475109768704294912, 184474524286819820627820544, 183936174507772681073459200, 182680025023329355446616064, 183936174507772681073459200,
    184474524286819820627820544, 183936174507772681073459200, 182680025023329355446616064, 183936174507772681073459200
  ]
def negativeScales : Array ℕ := #[
    11, 20, 17, 17, 17, 17,
    25, 23, 23, 23, 23, 12,
    14, 13, 14, 13, 15, 14,
    15, 13, 15, 14, 15, 18,
    20, 19, 20, 22, 21, 20,
    21, 20, 13, 15, 14, 15,
    13, 15, 14, 15, 17, 23,
    12, 13, 13, 18, 21, 13,
    13, 12, 12, 13, 18, 13,
    15, 13, 12, 14, 13, 14,
    12, 14, 13, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11175549550636191, 20060557411370184, 17902027641308033, 17898630912199072, 17890673971111195, 17898630912199072,
    25306935194611818, 23017177290027901, 23017103871012407, 23016932545444774, 23017103871012407, 12253552062637464,
    14249335707836394, 13239449359519281, 14249335707836394, 13620334393318917, 15616118038516796, 14606231690197617,
    15616118038516796, 13363176553811964, 15358960199010894, 14349073850693780, 15358960199010894, 18169274225209704,
    20165057870408634, 19155171522091521, 20165057870408634, 22060558400848185, 21016478468275638, 20016407054143185,
    21016240407418816, 20016407054143185, 13363176553811964, 15358960199010894, 14349073850693780, 15358960199010894,
    13215077914822828, 15210861560021759, 14200975211704646, 15210861560021759, 17902027641308033, 23017177290027901,
    12253552062637464, 13620334393318917, 13363176553811964, 18169274225209704, 21016478468275638, 13363176553811964,
    13215077914822828, 12253552062637464, 12253552062637464, 13215077914822828, 18169274225209704, 13215077914822828,
    15902021751133566, 13620334393318917, 12253552062637464, 14249335707836394, 13239449359519281, 14249335707836394,
    12253552062637464, 14249335707836394, 13239449359519281, 14249335707836394
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 69307 / 625000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 174765338798039830068461568, coefficient := (-174765338798039830068461568) }, { argument := 20656141011651978086389383168, coefficient := (-20656141011651978086389383168) }, { argument := 289165847437177702781550592, coefficient := (-289165847437177702781550592) }, { argument := 288485826663644473870778368, coefficient := (-288485826663644473870778368) }, { argument := 286899111525400273078976512, coefficient := (-286899111525400273078976512) }, { argument := 288485826663644473870778368, coefficient := (-288485826663644473870778368) }, { argument := 196022660674793528338780520448, coefficient := (-196022660674793528338780520448) }, { argument := 10022140257374624099904520192, coefficient := (-10022140257374624099904520192) }, { argument := 10021630241794474178221441024, coefficient := (-10021630241794474178221441024) }, { argument := 10020440205440791027627589632, coefficient := (-10020440205440791027627589632) }, { argument := 10021630241794474178221441024, coefficient := (-10021630241794474178221441024) }, { argument := 184474524286819820627820544, coefficient := (-184474524286819820627820544) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }, { argument := 182680025023329355446616064, coefficient := (-182680025023329355446616064) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }, { argument := 237875044475109768704294912, coefficient := (-237875044475109768704294912) }, { argument := 237180856602127930857881600, coefficient := (-237180856602127930857881600) }, { argument := 235561084898503642549583872, coefficient := (-235561084898503642549583872) }, { argument := 237180856602127930857881600, coefficient := (-237180856602127930857881600) }, { argument := 3184612840319836903469744128, coefficient := (-3184612840319836903469744128) }, { argument := 3175319223081549441689190400, coefficient := (-3175319223081549441689190400) }, { argument := 3153634116192212030867898368, coefficient := (-3153634116192212030867898368) }, { argument := 3175319223081549441689190400, coefficient := (-3175319223081549441689190400) }, { argument := 5568217877815324585792372736, coefficient := (-5568217877815324585792372736) }, { argument := 5551968214747770136612044800, coefficient := (-5551968214747770136612044800) }, { argument := 5514052334256809755191279616, coefficient := (-5514052334256809755191279616) }, { argument := 5551968214747770136612044800, coefficient := (-5551968214747770136612044800) }, { argument := 20656155178751426695325024256, coefficient := (-20656155178751426695325024256) }, { argument := 10017286845221854822036144128, coefficient := (-10017286845221854822036144128) }, { argument := 10016790996741153509288706048, coefficient := (-10016790996741153509288706048) }, { argument := 10015634016952850446211350528, coefficient := (-10015634016952850446211350528) }, { argument := 10016790996741153509288706048, coefficient := (-10016790996741153509288706048) }, { argument := 3184612840319836903469744128, coefficient := (-3184612840319836903469744128) }, { argument := 3175319223081549441689190400, coefficient := (-3175319223081549441689190400) }, { argument := 3153634116192212030867898368, coefficient := (-3153634116192212030867898368) }, { argument := 3175319223081549441689190400, coefficient := (-3175319223081549441689190400) }, { argument := 179619931542429825348141056, coefficient := (-179619931542429825348141056) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 177872655943768056619073536, coefficient := (-177872655943768056619073536) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 289165847437177702781550592, coefficient := (-289165847437177702781550592) }, { argument := 10022140257374624099904520192, coefficient := (-10022140257374624099904520192) }, { argument := 184474524286819820627820544, coefficient := (-184474524286819820627820544) }, { argument := 237875044475109768704294912, coefficient := (-237875044475109768704294912) }, { argument := 3184612840319836903469744128, coefficient := (-3184612840319836903469744128) }, { argument := 5568217877815324585792372736, coefficient := (-5568217877815324585792372736) }, { argument := 10017286845221854822036144128, coefficient := (-10017286845221854822036144128) }, { argument := 3184612840319836903469744128, coefficient := (-3184612840319836903469744128) }, { argument := 179619931542429825348141056, coefficient := (-179619931542429825348141056) }, { argument := 184474524286819820627820544, coefficient := (-184474524286819820627820544) }, { argument := 184474524286819820627820544, coefficient := (-184474524286819820627820544) }, { argument := 179619931542429825348141056, coefficient := (-179619931542429825348141056) }, { argument := 5568217877815324585792372736, coefficient := (-5568217877815324585792372736) }, { argument := 179619931542429825348141056, coefficient := (-179619931542429825348141056) }, { argument := 289164666845556985370247168, coefficient := (-289164666845556985370247168) }, { argument := 237875044475109768704294912, coefficient := (-237875044475109768704294912) }, { argument := 184474524286819820627820544, coefficient := (-184474524286819820627820544) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }, { argument := 182680025023329355446616064, coefficient := (-182680025023329355446616064) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }, { argument := 184474524286819820627820544, coefficient := (-184474524286819820627820544) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }, { argument := 182680025023329355446616064, coefficient := (-182680025023329355446616064) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }] }

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
def constantNumerator : ℤ := (-10025887152947326259724294291456)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    9509, 37925, 18833, 37925, 294779, 1175675,
    583823, 1175675, 9509, 37925, 18833, 37925,
    244357, 8488651, 19475, 50225, 42025, 1175675,
    1060569, 42025, 37925, 19475, 19475, 37925,
    1175675, 37925, 61089, 50225, 2313, 61233,
    61089, 60753, 61089, 12593, 50225, 24941,
    50225, 243013, 8487643, 9671, 24941, 20869,
    583823, 2120893, 20869, 18833, 9671, 9671,
    18833, 583823, 18833, 60753, 24941, 244357,
    8488651, 19475, 50225, 42025, 1175675, 1060569,
    42025, 37925, 19475, 19475
  ]
def negativeCoefficients : Array ℕ := #[
    179619931542429825348141056, 179095748862831294729420800, 177872655943768056619073536, 179095748862831294729420800, 5568217877815324585792372736, 5551968214747770136612044800,
    5514052334256809755191279616, 5551968214747770136612044800, 179619931542429825348141056, 179095748862831294729420800, 177872655943768056619073536, 179095748862831294729420800,
    288485826663644473870778368, 10021630241794474178221441024, 183936174507772681073459200, 237180856602127930857881600, 3175319223081549441689190400, 5551968214747770136612044800,
    10016790996741153509288706048, 3175319223081549441689190400, 179095748862831294729420800, 183936174507772681073459200, 183936174507772681073459200, 179095748862831294729420800,
    5551968214747770136612044800, 179095748862831294729420800, 288484646072023756459474944, 237180856602127930857881600, 174765338798039830068461568, 289164666845556985370247168,
    288484646072023756459474944, 286897930933779555667673088, 288484646072023756459474944, 237875044475109768704294912, 237180856602127930857881600, 235561084898503642549583872,
    237180856602127930857881600, 286899111525400273078976512, 10020440205440791027627589632, 182680025023329355446616064, 235561084898503642549583872, 3153634116192212030867898368,
    5514052334256809755191279616, 10015634016952850446211350528, 3153634116192212030867898368, 177872655943768056619073536, 182680025023329355446616064, 182680025023329355446616064,
    177872655943768056619073536, 5514052334256809755191279616, 177872655943768056619073536, 286897930933779555667673088, 235561084898503642549583872, 288485826663644473870778368,
    10021630241794474178221441024, 183936174507772681073459200, 237180856602127930857881600, 3175319223081549441689190400, 5551968214747770136612044800, 10016790996741153509288706048,
    3175319223081549441689190400, 179095748862831294729420800, 183936174507772681073459200, 183936174507772681073459200
  ]
def negativeScales : Array ℕ := #[
    13, 15, 14, 15, 18, 20,
    19, 20, 13, 15, 14, 15,
    17, 23, 14, 15, 15, 20,
    20, 15, 15, 14, 14, 15,
    20, 15, 15, 15, 11, 15,
    15, 15, 15, 13, 15, 14,
    15, 17, 23, 13, 14, 14,
    19, 21, 14, 14, 13, 13,
    14, 19, 14, 15, 14, 17,
    23, 14, 15, 15, 20, 20,
    15, 15, 14, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    13215077914822828, 15210861560021759, 14200975211704646, 15210861560021759, 18169274225209704, 20165057870408634,
    19155171522091521, 20165057870408634, 13215077914822828, 15210861560021759, 14200975211704646, 15210861560021759,
    17898630912199072, 23017103871012407, 14249335707836394, 15616118038516796, 15358960199010894, 20165057870408634,
    20016407054143185, 15358960199010894, 15210861560021759, 14249335707836394, 14249335707836394, 15210861560021759,
    20165057870408634, 15210861560021759, 15898625008140242, 15616118038516796, 11175549550636191, 15902021751133566,
    15898625008140242, 15890668034399555, 15898625008140242, 13620334393318917, 15616118038516796, 14606231690197617,
    15616118038516796, 17890673971111195, 23016932545444774, 13239449359519281, 14606231690197617, 14349073850693780,
    19155171522091521, 21016240407418816, 14349073850693780, 14200975211704646, 13239449359519281, 13239449359519281,
    14200975211704646, 19155171522091521, 14200975211704646, 15890668034399555, 14606231690197617, 17898630912199072,
    23017103871012407, 14249335707836394, 15616118038516796, 15358960199010894, 20165057870408634, 20016407054143185,
    15358960199010894, 15210861560021759, 14249335707836394, 14249335707836394
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 8143043 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 179619931542429825348141056, coefficient := (-179619931542429825348141056) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 177872655943768056619073536, coefficient := (-177872655943768056619073536) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 5568217877815324585792372736, coefficient := (-5568217877815324585792372736) }, { argument := 5551968214747770136612044800, coefficient := (-5551968214747770136612044800) }, { argument := 5514052334256809755191279616, coefficient := (-5514052334256809755191279616) }, { argument := 5551968214747770136612044800, coefficient := (-5551968214747770136612044800) }, { argument := 179619931542429825348141056, coefficient := (-179619931542429825348141056) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 177872655943768056619073536, coefficient := (-177872655943768056619073536) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 288485826663644473870778368, coefficient := (-288485826663644473870778368) }, { argument := 10021630241794474178221441024, coefficient := (-10021630241794474178221441024) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }, { argument := 237180856602127930857881600, coefficient := (-237180856602127930857881600) }, { argument := 3175319223081549441689190400, coefficient := (-3175319223081549441689190400) }, { argument := 5551968214747770136612044800, coefficient := (-5551968214747770136612044800) }, { argument := 10016790996741153509288706048, coefficient := (-10016790996741153509288706048) }, { argument := 3175319223081549441689190400, coefficient := (-3175319223081549441689190400) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 5551968214747770136612044800, coefficient := (-5551968214747770136612044800) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 288484646072023756459474944, coefficient := (-288484646072023756459474944) }, { argument := 237180856602127930857881600, coefficient := (-237180856602127930857881600) }, { argument := 174765338798039830068461568, coefficient := (-174765338798039830068461568) }, { argument := 289164666845556985370247168, coefficient := (-289164666845556985370247168) }, { argument := 288484646072023756459474944, coefficient := (-288484646072023756459474944) }, { argument := 286897930933779555667673088, coefficient := (-286897930933779555667673088) }, { argument := 288484646072023756459474944, coefficient := (-288484646072023756459474944) }, { argument := 237875044475109768704294912, coefficient := (-237875044475109768704294912) }, { argument := 237180856602127930857881600, coefficient := (-237180856602127930857881600) }, { argument := 235561084898503642549583872, coefficient := (-235561084898503642549583872) }, { argument := 237180856602127930857881600, coefficient := (-237180856602127930857881600) }, { argument := 286899111525400273078976512, coefficient := (-286899111525400273078976512) }, { argument := 10020440205440791027627589632, coefficient := (-10020440205440791027627589632) }, { argument := 182680025023329355446616064, coefficient := (-182680025023329355446616064) }, { argument := 235561084898503642549583872, coefficient := (-235561084898503642549583872) }, { argument := 3153634116192212030867898368, coefficient := (-3153634116192212030867898368) }, { argument := 5514052334256809755191279616, coefficient := (-5514052334256809755191279616) }, { argument := 10015634016952850446211350528, coefficient := (-10015634016952850446211350528) }, { argument := 3153634116192212030867898368, coefficient := (-3153634116192212030867898368) }, { argument := 177872655943768056619073536, coefficient := (-177872655943768056619073536) }, { argument := 182680025023329355446616064, coefficient := (-182680025023329355446616064) }, { argument := 182680025023329355446616064, coefficient := (-182680025023329355446616064) }, { argument := 177872655943768056619073536, coefficient := (-177872655943768056619073536) }, { argument := 5514052334256809755191279616, coefficient := (-5514052334256809755191279616) }, { argument := 177872655943768056619073536, coefficient := (-177872655943768056619073536) }, { argument := 286897930933779555667673088, coefficient := (-286897930933779555667673088) }, { argument := 235561084898503642549583872, coefficient := (-235561084898503642549583872) }, { argument := 288485826663644473870778368, coefficient := (-288485826663644473870778368) }, { argument := 10021630241794474178221441024, coefficient := (-10021630241794474178221441024) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }, { argument := 237180856602127930857881600, coefficient := (-237180856602127930857881600) }, { argument := 3175319223081549441689190400, coefficient := (-3175319223081549441689190400) }, { argument := 5551968214747770136612044800, coefficient := (-5551968214747770136612044800) }, { argument := 10016790996741153509288706048, coefficient := (-10016790996741153509288706048) }, { argument := 3175319223081549441689190400, coefficient := (-3175319223081549441689190400) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk9
