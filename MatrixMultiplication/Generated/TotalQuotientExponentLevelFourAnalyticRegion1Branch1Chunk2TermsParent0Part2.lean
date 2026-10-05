import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 2, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-128355026543631629513026418245632)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    9, 35, 35, 35, 35, 35,
    15994035, 722901285, 2009925, 9, 9, 9,
    9, 502212699, 22699100349, 63111645, 40778427, 8087782725,
    8087782725, 40778427, 15994035, 722901285, 2009925, 79410621,
    15749892675, 15749892675, 79410621, 902503, 36975715, 761358605,
    36975715, 902503, 35, 35, 35, 35,
    489417471, 22120779321, 61503705, 79410621, 15749892675, 15749892675,
    79410621, 15994035, 722901285, 2009925, 2496068979, 495057437325,
    495057437325, 2496068979, 9112369, 373335445, 7687265915, 373335445,
    9112369, 79410621, 15749892675, 15749892675, 79410621, 18544981,
    759791305, 15644691335, 759791305, 18544981
  ]
def negativeCoefficients : Array ℕ := #[
    174085318024506601157689344, 169249614746048084458864640, 169249614746048084458864640, 169249614746048084458864640, 169249614746048084458864640, 169249614746048084458864640,
    18439866896934571773788160, 833448437184423098748764160, 18538286041175335265894400, 174085318024506601157689344, 174085318024506601157689344, 174085318024506601157689344,
    174085318024506601157689344, 579011820563745553696948224, 26170280927590885300711194624, 582102181692905527349084160, 94028650824680946221973504, 18649157256480529778422579200,
    18649157256480529778422579200, 94028650824680946221973504, 18439866896934571773788160, 833448437184423098748764160, 18538286041175335265894400, 91554212645084079216132096,
    18158389960257357942148300800, 18158389960257357942148300800, 91554212645084079216132096, 8324120933377545731047424, 1364163103094846746662010880, 14044587334751521393533255680,
    1364163103094846746662010880, 8324120933377545731047424, 169249614746048084458864640, 169249614746048084458864640, 169249614746048084458864640, 169249614746048084458864640,
    564259927046197896277917696, 25503522177843346821712183296, 567271552859965259136368640, 91554212645084079216132096, 18158389960257357942148300800, 18158389960257357942148300800,
    91554212645084079216132096, 590075740701906296761221120, 26670349989901539159960453120, 593225153317610728508620800, 2877771602871156327793557504, 570762365507548845586985779200,
    570762365507548845586985779200, 2877771602871156327793557504, 168093538848204633149538304, 27547293630237873013239316480, 283610053921111367495219937280, 27547293630237873013239316480,
    168093538848204633149538304, 91554212645084079216132096, 18158389960257357942148300800, 18158389960257357942148300800, 91554212645084079216132096, 171047259179403117118619648,
    28031351505529592826570997760, 288593617168926423473570447360, 28031351505529592826570997760, 171047259179403117118619648
  ]
def negativeScales : Array ℕ := #[
    3, 5, 5, 5, 5, 5,
    23, 29, 20, 3, 3, 3,
    3, 28, 34, 25, 25, 32,
    32, 25, 23, 29, 20, 26,
    33, 33, 26, 19, 25, 29,
    25, 19, 5, 5, 5, 5,
    28, 34, 25, 26, 33, 33,
    26, 23, 29, 20, 31, 38,
    38, 31, 23, 28, 32, 28,
    23, 26, 33, 33, 26, 24,
    29, 33, 29, 24
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    3169925001442313, 5129283016944967, 5129283016944967, 5129283016944967, 5129283016944967, 5129283016944967,
    23931030621834616, 29429223414070299, 20938710246423341, 3169925001442313, 3169925001442313, 3169925001442313,
    3169925001442313, 28903723272967495, 34401916068074550, 25911402897174510, 25281302789662460, 32913097099844375,
    32913097099844375, 25281302789662460, 23931030621834616, 29429223414070299, 20938710246423341, 26242828641847825,
    33874622949267724, 33874622949267724, 26242828641847825, 19783572202551266, 25140074709222989, 29504000891929928,
    25140074709222989, 19783572202551266, 5129283016944967, 5129283016944967, 5129283016944967, 5129283016944967,
    28866490364465229, 34364683161875569, 25874169988353088, 26242828641847825, 33874622949267724, 33874622949267724,
    26242828641847825, 23931030621834616, 29429223414070299, 20938710246423341, 31217010657692093, 38848804964053774,
    38848804964053774, 31217010657692093, 23119394738636579, 28475897245768850, 32839823429899859, 28475897245768850,
    23119394738636579, 26242828641847825, 33874622949267724, 33874622949267724, 26242828641847825, 24144525453960261,
    29501027961092694, 33864954146097142, 29501027961092694, 24144525453960261
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
noncomputable def negativeCeiling : ℝ := 451300813 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 174085318024506601157689344, coefficient := (-174085318024506601157689344) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 18439866896934571773788160, coefficient := (-18439866896934571773788160) }, { argument := 833448437184423098748764160, coefficient := (-833448437184423098748764160) }, { argument := 18538286041175335265894400, coefficient := (-18538286041175335265894400) }, { argument := 174085318024506601157689344, coefficient := (-174085318024506601157689344) }, { argument := 174085318024506601157689344, coefficient := (-174085318024506601157689344) }, { argument := 174085318024506601157689344, coefficient := (-174085318024506601157689344) }, { argument := 174085318024506601157689344, coefficient := (-174085318024506601157689344) }, { argument := 579011820563745553696948224, coefficient := (-579011820563745553696948224) }, { argument := 26170280927590885300711194624, coefficient := (-26170280927590885300711194624) }, { argument := 582102181692905527349084160, coefficient := (-582102181692905527349084160) }, { argument := 94028650824680946221973504, coefficient := (-94028650824680946221973504) }, { argument := 18649157256480529778422579200, coefficient := (-18649157256480529778422579200) }, { argument := 18649157256480529778422579200, coefficient := (-18649157256480529778422579200) }, { argument := 94028650824680946221973504, coefficient := (-94028650824680946221973504) }, { argument := 18439866896934571773788160, coefficient := (-18439866896934571773788160) }, { argument := 833448437184423098748764160, coefficient := (-833448437184423098748764160) }, { argument := 18538286041175335265894400, coefficient := (-18538286041175335265894400) }, { argument := 91554212645084079216132096, coefficient := (-91554212645084079216132096) }, { argument := 18158389960257357942148300800, coefficient := (-18158389960257357942148300800) }, { argument := 18158389960257357942148300800, coefficient := (-18158389960257357942148300800) }, { argument := 91554212645084079216132096, coefficient := (-91554212645084079216132096) }, { argument := 8324120933377545731047424, coefficient := (-8324120933377545731047424) }, { argument := 1364163103094846746662010880, coefficient := (-1364163103094846746662010880) }, { argument := 14044587334751521393533255680, coefficient := (-14044587334751521393533255680) }, { argument := 1364163103094846746662010880, coefficient := (-1364163103094846746662010880) }, { argument := 8324120933377545731047424, coefficient := (-8324120933377545731047424) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 564259927046197896277917696, coefficient := (-564259927046197896277917696) }, { argument := 25503522177843346821712183296, coefficient := (-25503522177843346821712183296) }, { argument := 567271552859965259136368640, coefficient := (-567271552859965259136368640) }, { argument := 91554212645084079216132096, coefficient := (-91554212645084079216132096) }, { argument := 18158389960257357942148300800, coefficient := (-18158389960257357942148300800) }, { argument := 18158389960257357942148300800, coefficient := (-18158389960257357942148300800) }, { argument := 91554212645084079216132096, coefficient := (-91554212645084079216132096) }, { argument := 590075740701906296761221120, coefficient := (-590075740701906296761221120) }, { argument := 26670349989901539159960453120, coefficient := (-26670349989901539159960453120) }, { argument := 593225153317610728508620800, coefficient := (-593225153317610728508620800) }, { argument := 2877771602871156327793557504, coefficient := (-2877771602871156327793557504) }, { argument := 570762365507548845586985779200, coefficient := (-570762365507548845586985779200) }, { argument := 570762365507548845586985779200, coefficient := (-570762365507548845586985779200) }, { argument := 2877771602871156327793557504, coefficient := (-2877771602871156327793557504) }, { argument := 168093538848204633149538304, coefficient := (-168093538848204633149538304) }, { argument := 27547293630237873013239316480, coefficient := (-27547293630237873013239316480) }, { argument := 283610053921111367495219937280, coefficient := (-283610053921111367495219937280) }, { argument := 27547293630237873013239316480, coefficient := (-27547293630237873013239316480) }, { argument := 168093538848204633149538304, coefficient := (-168093538848204633149538304) }, { argument := 91554212645084079216132096, coefficient := (-91554212645084079216132096) }, { argument := 18158389960257357942148300800, coefficient := (-18158389960257357942148300800) }, { argument := 18158389960257357942148300800, coefficient := (-18158389960257357942148300800) }, { argument := 91554212645084079216132096, coefficient := (-91554212645084079216132096) }, { argument := 171047259179403117118619648, coefficient := (-171047259179403117118619648) }, { argument := 28031351505529592826570997760, coefficient := (-28031351505529592826570997760) }, { argument := 288593617168926423473570447360, coefficient := (-288593617168926423473570447360) }, { argument := 28031351505529592826570997760, coefficient := (-28031351505529592826570997760) }, { argument := 171047259179403117118619648, coefficient := (-171047259179403117118619648) }] }

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

end TermShard4


end Parent0

namespace Parent0

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-16278802931026658187374520958976)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1179116049, 35, 10517089405, 395, 35, 21034173685,
    35, 35, 1451, 9, 395, 1451,
    1179116049, 35, 9, 35, 13206433, 2765735,
    499186795, 18253851, 902503, 9112369, 18544981, 3314413,
    2765735, 902503, 195812199, 20077319865, 4671213, 378747,
    81178107, 146827587, 20077319865, 81178107, 2398731, 2398731,
    4671213, 4671213, 146827587, 4671213, 195812199, 378747,
    3314413, 182875555, 30952845, 1524727135, 1205955, 2009925,
    61503705, 2009925, 1205955, 985265235, 63111645, 182875555,
    61503705, 2009925, 63111645, 2009925, 61503705, 2009925,
    3314413, 6438699, 1277018325, 1277018325
  ]
def negativeCoefficients : Array ℕ := #[
    1359428249319160704688717824, 169249614746048084458864640, 48501514163589316086983557120, 1910102794991114096035758080, 169249614746048084458864640, 48501502346143893866802053120,
    169249614746048084458864640, 169249614746048084458864640, 7016605457043307729994645504, 174085318024506601157689344, 1910102794991114096035758080, 7016605457043307729994645504,
    1359428249319160704688717824, 169249614746048084458864640, 174085318024506601157689344, 169249614746048084458864640, 30451961209699031859593216, 204075222882804346954711040,
    1151046381542539354009763840, 168362058878313586237636608, 8324120933377545731047424, 168093538848204633149538304, 171047259179403117118619648, 30570064182787948050120704,
    204075222882804346954711040, 8324120933377545731047424, 225756095091455336827060224, 23147573827228737806259978240, 86168670724785015732830208, 111786383642964344734482432,
    1497471764217209868005670912, 2708490920349323602629230592, 23147573827228737806259978240, 1497471764217209868005670912, 88497553717346772914798592, 88497553717346772914798592,
    86168670724785015732830208, 86168670724785015732830208, 2708490920349323602629230592, 86168670724785015732830208, 225756095091455336827060224, 111786383642964344734482432,
    30570064182787948050120704, 1686729280211297580288573440, 570979210068200326189547520, 14063125620792696728799150080, 355935091990566437105172480, 18538286041175335265894400,
    567271552859965259136368640, 593225153317610728508620800, 355935091990566437105172480, 9087467817384149347341434880, 582102181692905527349084160, 1686729280211297580288573440,
    567271552859965259136368640, 18538286041175335265894400, 582102181692905527349084160, 18538286041175335265894400, 567271552859965259136368640, 593225153317610728508620800,
    30570064182787948050120704, 118773032620649616280387584, 23556830218712248141165363200, 23556830218712248141165363200
  ]
def negativeScales : Array ℕ := #[
    30, 5, 33, 8, 5, 34,
    5, 5, 10, 3, 8, 10,
    30, 5, 3, 5, 23, 21,
    28, 24, 19, 23, 24, 21,
    21, 19, 27, 34, 22, 18,
    26, 27, 34, 26, 21, 21,
    22, 22, 27, 22, 27, 18,
    21, 27, 24, 30, 20, 20,
    25, 20, 20, 29, 25, 27,
    25, 20, 25, 20, 25, 20,
    21, 22, 30, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30135058569825227, 5129283016944967, 33292016444191326, 8625708843075807, 5129283016944967, 34292016092677104,
    5129283016944967, 5129283016944967, 10502831804067043, 3169925001442313, 8625708843075807, 10502831804067043,
    30135058569825227, 5129283016944967, 3169925001442313, 5129283016944967, 23654737517791008, 21399231500034915,
    28895004534150419, 24121697524506000, 19783572202551266, 23119394738636579, 24144525453960261, 21660321953422281,
    21399231500034915, 19783572202551266, 27544895406005764, 34224847644679210, 22155365800597485, 18530874935690428,
    26274587362296483, 27129547816441754, 34224847644679210, 26274587362296483, 21193839948412121, 21193839948412121,
    22155365800597485, 22155365800597485, 27129547816441754, 22155365800597485, 27544895406005764, 18530874935690428,
    21660321953422281, 27446287001833352, 24883568686870500, 30505903935216217, 20201744643653310, 20938710246423341,
    25874169988353088, 20938710246423341, 20201744643653310, 29875936914617886, 25911402897174510, 27446287001833352,
    25874169988353088, 20938710246423341, 25911402897174510, 20938710246423341, 25874169988353088, 20938710246423341,
    21660321953422281, 22618337776949349, 30250132081608682, 30250132081608682
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
noncomputable def negativeCeiling : ℝ := 93786211 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1359428249319160704688717824, coefficient := (-1359428249319160704688717824) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 48501514163589316086983557120, coefficient := (-48501514163589316086983557120) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 48501502346143893866802053120, coefficient := (-48501502346143893866802053120) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 174085318024506601157689344, coefficient := (-174085318024506601157689344) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 1359428249319160704688717824, coefficient := (-1359428249319160704688717824) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 174085318024506601157689344, coefficient := (-174085318024506601157689344) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 30451961209699031859593216, coefficient := (-30451961209699031859593216) }, { argument := 204075222882804346954711040, coefficient := (-204075222882804346954711040) }, { argument := 1151046381542539354009763840, coefficient := (-1151046381542539354009763840) }, { argument := 168362058878313586237636608, coefficient := (-168362058878313586237636608) }, { argument := 8324120933377545731047424, coefficient := (-8324120933377545731047424) }, { argument := 168093538848204633149538304, coefficient := (-168093538848204633149538304) }, { argument := 171047259179403117118619648, coefficient := (-171047259179403117118619648) }, { argument := 30570064182787948050120704, coefficient := (-30570064182787948050120704) }, { argument := 204075222882804346954711040, coefficient := (-204075222882804346954711040) }, { argument := 8324120933377545731047424, coefficient := (-8324120933377545731047424) }, { argument := 225756095091455336827060224, coefficient := (-225756095091455336827060224) }, { argument := 23147573827228737806259978240, coefficient := (-23147573827228737806259978240) }, { argument := 86168670724785015732830208, coefficient := (-86168670724785015732830208) }, { argument := 111786383642964344734482432, coefficient := (-111786383642964344734482432) }, { argument := 1497471764217209868005670912, coefficient := (-1497471764217209868005670912) }, { argument := 2708490920349323602629230592, coefficient := (-2708490920349323602629230592) }, { argument := 23147573827228737806259978240, coefficient := (-23147573827228737806259978240) }, { argument := 1497471764217209868005670912, coefficient := (-1497471764217209868005670912) }, { argument := 88497553717346772914798592, coefficient := (-88497553717346772914798592) }, { argument := 88497553717346772914798592, coefficient := (-88497553717346772914798592) }, { argument := 86168670724785015732830208, coefficient := (-86168670724785015732830208) }, { argument := 86168670724785015732830208, coefficient := (-86168670724785015732830208) }, { argument := 2708490920349323602629230592, coefficient := (-2708490920349323602629230592) }, { argument := 86168670724785015732830208, coefficient := (-86168670724785015732830208) }, { argument := 225756095091455336827060224, coefficient := (-225756095091455336827060224) }, { argument := 111786383642964344734482432, coefficient := (-111786383642964344734482432) }, { argument := 30570064182787948050120704, coefficient := (-30570064182787948050120704) }, { argument := 1686729280211297580288573440, coefficient := (-1686729280211297580288573440) }, { argument := 570979210068200326189547520, coefficient := (-570979210068200326189547520) }, { argument := 14063125620792696728799150080, coefficient := (-14063125620792696728799150080) }, { argument := 355935091990566437105172480, coefficient := (-355935091990566437105172480) }, { argument := 18538286041175335265894400, coefficient := (-18538286041175335265894400) }, { argument := 567271552859965259136368640, coefficient := (-567271552859965259136368640) }, { argument := 593225153317610728508620800, coefficient := (-593225153317610728508620800) }, { argument := 355935091990566437105172480, coefficient := (-355935091990566437105172480) }, { argument := 9087467817384149347341434880, coefficient := (-9087467817384149347341434880) }, { argument := 582102181692905527349084160, coefficient := (-582102181692905527349084160) }, { argument := 1686729280211297580288573440, coefficient := (-1686729280211297580288573440) }, { argument := 567271552859965259136368640, coefficient := (-567271552859965259136368640) }, { argument := 18538286041175335265894400, coefficient := (-18538286041175335265894400) }, { argument := 582102181692905527349084160, coefficient := (-582102181692905527349084160) }, { argument := 18538286041175335265894400, coefficient := (-18538286041175335265894400) }, { argument := 567271552859965259136368640, coefficient := (-567271552859965259136368640) }, { argument := 593225153317610728508620800, coefficient := (-593225153317610728508620800) }, { argument := 30570064182787948050120704, coefficient := (-30570064182787948050120704) }, { argument := 118773032620649616280387584, coefficient := (-118773032620649616280387584) }, { argument := 23556830218712248141165363200, coefficient := (-23556830218712248141165363200) }, { argument := 23556830218712248141165363200, coefficient := (-23556830218712248141165363200) }] }

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

end TermShard5


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2
