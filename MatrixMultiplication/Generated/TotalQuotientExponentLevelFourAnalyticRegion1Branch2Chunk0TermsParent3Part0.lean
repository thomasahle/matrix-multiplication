import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 0, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0

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
def constantNumerator : ℤ := (-44037814099365635647114403905536)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    386995, 724026571, 670428981, 724026571, 670428981, 47,
    47, 47, 47, 86590261, 181656087, 1055854159,
    292607709, 9064675, 292607709, 195434393, 5434553, 181656087,
    1087761, 10585297, 10946877537, 10008986527, 10946877537, 10008986527,
    1163, 1163, 1163, 1163, 3017763785, 19046313093,
    51996447833, 30679390551, 950414825, 30679390551, 20490943627, 1527890189,
    19046313093, 114049779, 37, 37, 37, 37,
    1976902443, 9574210773, 1976902443, 45047275, 3818103705, 45047275,
    39899015, 1867531315, 508390675, 1909052535, 1867531315, 45047275,
    45047275, 19305975, 45047275, 508390675, 19305975, 90093185,
    39899015, 3095959, 10946882887, 10008991417
  ]
def negativeCoefficients : Array ℕ := #[
    14620257736305106795794268160, 1669491607225312238309998592, 1545903979013110447485222912, 1669491607225312238309998592, 1545903979013110447485222912, 227278054087550284844761088,
    227278054087550284844761088, 227278054087550284844761088, 227278054087550284844761088, 99831773996419582038900736, 209435209145032295067942912, 1217316965639677039486173184,
    337353720119842439360937984, 10450858739772070612172800, 337353720119842439360937984, 225320514429485842398445568, 100249808346010464863387648, 209435209145032295067942912,
    10032824390181187787685888, 49987651764020606871600627712, 50483562082819740711883112448, 46158303225193999258938769408, 50483562082819740711883112448, 46158303225193999258938769408,
    5623922912847254920733130752, 5623922912847254920733130752, 5623922912847254920733130752, 5623922912847254920733130752, 3479244763550253467209564160, 21958903948394649376436256768,
    59947822869833787962197803008, 35370929114480004085397323776, 1095753690039653162496819200, 35370929114480004085397323776, 23624449557254922183431421952, 3523074911151839593709436928,
    21958903948394649376436256768, 1051923542438067035996946432, 178921021302965117856514048, 178921021302965117856514048, 178921021302965117856514048, 178921021302965117856514048,
    2279213339044511541381562368, 22076626979660486894363344896, 2279213339044511541381562368, 415487776571507220886323200, 17607895473254308029734584320, 207743888285753610443161600,
    184001729624524626392514560, 8612468054360813964372213760, 2344538167796362175001395200, 17607901768205723183119073280, 8612468054360813964372213760, 207743888285753610443161600,
    207743888285753610443161600, 178066189959217380379852800, 207743888285753610443161600, 2344538167796362175001395200, 178066189959217380379852800, 415481481620092067501834240,
    184001729624524626392514560, 14620253013938623926149054464, 50483586755339939298408398848, 46158325776338629368865619968
  ]
def negativeScales : Array ℕ := #[
    18, 29, 29, 29, 29, 5,
    5, 5, 5, 26, 27, 29,
    28, 23, 28, 27, 22, 27,
    20, 23, 33, 33, 33, 33,
    10, 10, 10, 10, 31, 34,
    35, 34, 29, 34, 34, 30,
    34, 26, 5, 5, 5, 5,
    30, 33, 30, 25, 31, 25,
    25, 30, 28, 30, 30, 25,
    25, 24, 25, 28, 24, 26,
    25, 21, 33, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    18561955401217177, 29431467402742372, 29320509273651198, 29431467402742372, 29320509273651198, 5554588851679165,
    5554588851679165, 5554588851679165, 5554588851679165, 26367701435155295, 27436634468026464, 29975763444629539,
    28124392538109008, 23111823864605952, 28124392538109008, 27542109137584778, 22373729945661599, 27436634468026464,
    20052930175552383, 23335558412953920, 33349800366253634, 33220576848472731, 33349800366253634, 33220576848472731,
    10183635381473219, 10183635381473219, 10183635381473219, 10183635381473219, 31490832737536203, 34148792702642880,
    35597694016964206, 34836550774062400, 29823982100267645, 34836550774062400, 34254267372200177, 30508893713146912,
    34148792702642880, 26765088410480454, 5209453365628950, 5209453365628950, 5209453365628950, 5209453365628950,
    30880594535169351, 33156506420835116, 30880594535169351, 25424936501373755, 31830209144042922, 25424936501373755,
    25249849794815646, 30798485289121883, 28921362333867493, 30830209659816870, 30798485289121883, 25424936501373755,
    25424936501373755, 24202544080037289, 25424936501373755, 28921362333867493, 24202544080037289, 26424914643296335,
    25249849794815646, 21561954935224311, 33349801071332919, 33220577553317024
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
noncomputable def negativeCeiling : ℝ := 131188861 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 14620257736305106795794268160, coefficient := (-14620257736305106795794268160) }, { argument := 1669491607225312238309998592, coefficient := (-1669491607225312238309998592) }, { argument := 1545903979013110447485222912, coefficient := (-1545903979013110447485222912) }, { argument := 1669491607225312238309998592, coefficient := (-1669491607225312238309998592) }, { argument := 1545903979013110447485222912, coefficient := (-1545903979013110447485222912) }, { argument := 227278054087550284844761088, coefficient := (-227278054087550284844761088) }, { argument := 227278054087550284844761088, coefficient := (-227278054087550284844761088) }, { argument := 227278054087550284844761088, coefficient := (-227278054087550284844761088) }, { argument := 227278054087550284844761088, coefficient := (-227278054087550284844761088) }, { argument := 99831773996419582038900736, coefficient := (-99831773996419582038900736) }, { argument := 209435209145032295067942912, coefficient := (-209435209145032295067942912) }, { argument := 1217316965639677039486173184, coefficient := (-1217316965639677039486173184) }, { argument := 337353720119842439360937984, coefficient := (-337353720119842439360937984) }, { argument := 10450858739772070612172800, coefficient := (-10450858739772070612172800) }, { argument := 337353720119842439360937984, coefficient := (-337353720119842439360937984) }, { argument := 225320514429485842398445568, coefficient := (-225320514429485842398445568) }, { argument := 100249808346010464863387648, coefficient := (-100249808346010464863387648) }, { argument := 209435209145032295067942912, coefficient := (-209435209145032295067942912) }, { argument := 10032824390181187787685888, coefficient := (-10032824390181187787685888) }, { argument := 49987651764020606871600627712, coefficient := (-49987651764020606871600627712) }, { argument := 50483562082819740711883112448, coefficient := (-50483562082819740711883112448) }, { argument := 46158303225193999258938769408, coefficient := (-46158303225193999258938769408) }, { argument := 50483562082819740711883112448, coefficient := (-50483562082819740711883112448) }, { argument := 46158303225193999258938769408, coefficient := (-46158303225193999258938769408) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 3479244763550253467209564160, coefficient := (-3479244763550253467209564160) }, { argument := 21958903948394649376436256768, coefficient := (-21958903948394649376436256768) }, { argument := 59947822869833787962197803008, coefficient := (-59947822869833787962197803008) }, { argument := 35370929114480004085397323776, coefficient := (-35370929114480004085397323776) }, { argument := 1095753690039653162496819200, coefficient := (-1095753690039653162496819200) }, { argument := 35370929114480004085397323776, coefficient := (-35370929114480004085397323776) }, { argument := 23624449557254922183431421952, coefficient := (-23624449557254922183431421952) }, { argument := 3523074911151839593709436928, coefficient := (-3523074911151839593709436928) }, { argument := 21958903948394649376436256768, coefficient := (-21958903948394649376436256768) }, { argument := 1051923542438067035996946432, coefficient := (-1051923542438067035996946432) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 2279213339044511541381562368, coefficient := (-2279213339044511541381562368) }, { argument := 22076626979660486894363344896, coefficient := (-22076626979660486894363344896) }, { argument := 2279213339044511541381562368, coefficient := (-2279213339044511541381562368) }, { argument := 415487776571507220886323200, coefficient := (-415487776571507220886323200) }, { argument := 17607895473254308029734584320, coefficient := (-17607895473254308029734584320) }, { argument := 207743888285753610443161600, coefficient := (-207743888285753610443161600) }, { argument := 184001729624524626392514560, coefficient := (-184001729624524626392514560) }, { argument := 8612468054360813964372213760, coefficient := (-8612468054360813964372213760) }, { argument := 2344538167796362175001395200, coefficient := (-2344538167796362175001395200) }, { argument := 17607901768205723183119073280, coefficient := (-17607901768205723183119073280) }, { argument := 8612468054360813964372213760, coefficient := (-8612468054360813964372213760) }, { argument := 207743888285753610443161600, coefficient := (-207743888285753610443161600) }, { argument := 207743888285753610443161600, coefficient := (-207743888285753610443161600) }, { argument := 178066189959217380379852800, coefficient := (-178066189959217380379852800) }, { argument := 207743888285753610443161600, coefficient := (-207743888285753610443161600) }, { argument := 2344538167796362175001395200, coefficient := (-2344538167796362175001395200) }, { argument := 178066189959217380379852800, coefficient := (-178066189959217380379852800) }, { argument := 415481481620092067501834240, coefficient := (-415481481620092067501834240) }, { argument := 184001729624524626392514560, coefficient := (-184001729624524626392514560) }, { argument := 14620253013938623926149054464, coefficient := (-14620253013938623926149054464) }, { argument := 50483586755339939298408398848, coefficient := (-50483586755339939298408398848) }, { argument := 46158325776338629368865619968, coefficient := (-46158325776338629368865619968) }] }

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

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-259874292273265597937559583850496)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    10946882887, 10008991417, 5154563265, 205300218375, 345251481285, 330693166125,
    10244521875, 330693166125, 220871891625, 10718907405, 205300218375, 1229342625,
    19, 19, 19, 19, 2028586167, 9824516937,
    2028586167, 3818103705, 969883551, 3771769365, 3340710009, 156366781389,
    42567111405, 1939767453, 156366781389, 3771769365, 3771769365, 1616472585,
    3771769365, 42567111405, 1616472585, 3818102301, 3340710009, 64604655,
    312882705, 64604655, 45047275, 3771769365, 1885885365, 22522955,
    11861455, 803674075, 1098279135, 4981522725, 1126992315, 35891475,
    1098279135, 624511665, 1126992315, 17594001045, 21534885, 401837125,
    1098279135, 35891475, 21534885, 35891475, 552728715, 624511665,
    11861455, 19, 19, 19
  ]
def negativeCoefficients : Array ℕ := #[
    50483586755339939298408398848, 46158325776338629368865619968, 11885613670149963379931873280, 236695036665019252693008384000, 398047857270844870017322844160, 381263262652036999846821888000,
    11811129574102757120409600000, 381263262652036999846821888000, 254647953617655443516030976000, 12358058853114073664748257280, 236695036665019252693008384000, 11338684391138646835593216000,
    183756724581423634555338752, 183756724581423634555338752, 183756724581423634555338752, 183756724581423634555338752, 2338800615882276548999380992, 22653793698082983283758465024,
    2338800615882276548999380992, 17607895473254308029734584320, 35782387293195251327887736832, 17394216045303247173278760960, 15406305640125733210618331136, 721114499478143189955070918656,
    196306152511279503812717445120, 35782393768002421199940354048, 721114499478143189955070918656, 17394216045303247173278760960, 17394216045303247173278760960, 14909328038831354719953223680,
    17394216045303247173278760960, 196306152511279503812717445120, 14909328038831354719953223680, 17607888998447138157681967104, 15406305640125733210618331136, 74484096047206259522273280,
    721458398028120486743900160, 74484096047206259522273280, 207743888285753610443161600, 17394216045303247173278760960, 17394222340254662326663249920, 207737593334338457058672640,
    109402612363411264781680640, 3706292495050063928413388800, 2532459265605012823757291520, 11486609350680400803083059200, 2598667350980307276665978880, 82760106719118066135859200,
    2532459265605012823757291520, 1440025856912654350763950080, 2598667350980307276665978880, 40569004313711676019798179840, 1588994049007066869808496640, 3706293302095117153206272000,
    2532459265605012823757291520, 82760106719118066135859200, 1588994049007066869808496640, 82760106719118066135859200, 2549011286948836436984463360, 1440025856912654350763950080,
    109402612363411264781680640, 183756724581423634555338752, 183756724581423634555338752, 183756724581423634555338752
  ]
def negativeScales : Array ℕ := #[
    33, 33, 32, 37, 38, 38,
    33, 38, 37, 33, 37, 30,
    4, 4, 4, 4, 30, 33,
    30, 31, 29, 31, 31, 37,
    35, 30, 37, 31, 31, 30,
    31, 35, 30, 31, 31, 25,
    28, 25, 25, 31, 30, 24,
    23, 29, 30, 32, 30, 25,
    30, 29, 30, 34, 24, 28,
    30, 25, 24, 25, 29, 29,
    23, 4, 4, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33349801071332919, 33220577553317024, 32263203050326417, 37578944205786182, 38328856648071798, 38266702275865631,
    33254133602362575, 38266702275865631, 37684418875390310, 33319438806001223, 37578944205786182, 30195239913309007,
    4247927513443586, 4247927513443586, 4247927513443586, 4247927513443586, 30917827444288710, 33193739327034091,
    30917827444288710, 31830209144042922, 29853236301560627, 31812594316054369, 31637507608678382, 37186143102342797,
    35309020141340518, 30853236562615643, 37186143102342797, 31812594316054369, 31812594316054369, 30590201893888873,
    31812594316054369, 35309020141340518, 30590201893888873, 31830208613532382, 31637507608678382, 25945134793892351,
    28221046673029826, 25945134793892351, 25424936501373755, 31812594316054369, 30812594838164344, 24424892784887741,
    23499777654916429, 29582035303151097, 30032597625543036, 32213939658933169, 30069830531742012, 25097137877737747,
    30032597625543036, 29218153278699113, 30069830531742012, 34034364551717224, 24360172283571542, 28582035617297854,
    30032597625543036, 25097137877737747, 24360172283571542, 25097137877737747, 29041996323545286, 29218153278699113,
    23499777654916429, 4247927513443586, 4247927513443586, 4247927513443586
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
noncomputable def negativeCeiling : ℝ := 75149889 / 40000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 50483586755339939298408398848, coefficient := (-50483586755339939298408398848) }, { argument := 46158325776338629368865619968, coefficient := (-46158325776338629368865619968) }, { argument := 11885613670149963379931873280, coefficient := (-11885613670149963379931873280) }, { argument := 236695036665019252693008384000, coefficient := (-236695036665019252693008384000) }, { argument := 398047857270844870017322844160, coefficient := (-398047857270844870017322844160) }, { argument := 381263262652036999846821888000, coefficient := (-381263262652036999846821888000) }, { argument := 11811129574102757120409600000, coefficient := (-11811129574102757120409600000) }, { argument := 381263262652036999846821888000, coefficient := (-381263262652036999846821888000) }, { argument := 254647953617655443516030976000, coefficient := (-254647953617655443516030976000) }, { argument := 12358058853114073664748257280, coefficient := (-12358058853114073664748257280) }, { argument := 236695036665019252693008384000, coefficient := (-236695036665019252693008384000) }, { argument := 11338684391138646835593216000, coefficient := (-11338684391138646835593216000) }, { argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }, { argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }, { argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }, { argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }, { argument := 2338800615882276548999380992, coefficient := (-2338800615882276548999380992) }, { argument := 22653793698082983283758465024, coefficient := (-22653793698082983283758465024) }, { argument := 2338800615882276548999380992, coefficient := (-2338800615882276548999380992) }, { argument := 17607895473254308029734584320, coefficient := (-17607895473254308029734584320) }, { argument := 35782387293195251327887736832, coefficient := (-35782387293195251327887736832) }, { argument := 17394216045303247173278760960, coefficient := (-17394216045303247173278760960) }, { argument := 15406305640125733210618331136, coefficient := (-15406305640125733210618331136) }, { argument := 721114499478143189955070918656, coefficient := (-721114499478143189955070918656) }, { argument := 196306152511279503812717445120, coefficient := (-196306152511279503812717445120) }, { argument := 35782393768002421199940354048, coefficient := (-35782393768002421199940354048) }, { argument := 721114499478143189955070918656, coefficient := (-721114499478143189955070918656) }, { argument := 17394216045303247173278760960, coefficient := (-17394216045303247173278760960) }, { argument := 17394216045303247173278760960, coefficient := (-17394216045303247173278760960) }, { argument := 14909328038831354719953223680, coefficient := (-14909328038831354719953223680) }, { argument := 17394216045303247173278760960, coefficient := (-17394216045303247173278760960) }, { argument := 196306152511279503812717445120, coefficient := (-196306152511279503812717445120) }, { argument := 14909328038831354719953223680, coefficient := (-14909328038831354719953223680) }, { argument := 17607888998447138157681967104, coefficient := (-17607888998447138157681967104) }, { argument := 15406305640125733210618331136, coefficient := (-15406305640125733210618331136) }, { argument := 74484096047206259522273280, coefficient := (-74484096047206259522273280) }, { argument := 721458398028120486743900160, coefficient := (-721458398028120486743900160) }, { argument := 74484096047206259522273280, coefficient := (-74484096047206259522273280) }, { argument := 207743888285753610443161600, coefficient := (-207743888285753610443161600) }, { argument := 17394216045303247173278760960, coefficient := (-17394216045303247173278760960) }, { argument := 17394222340254662326663249920, coefficient := (-17394222340254662326663249920) }, { argument := 207737593334338457058672640, coefficient := (-207737593334338457058672640) }, { argument := 109402612363411264781680640, coefficient := (-109402612363411264781680640) }, { argument := 3706292495050063928413388800, coefficient := (-3706292495050063928413388800) }, { argument := 2532459265605012823757291520, coefficient := (-2532459265605012823757291520) }, { argument := 11486609350680400803083059200, coefficient := (-11486609350680400803083059200) }, { argument := 2598667350980307276665978880, coefficient := (-2598667350980307276665978880) }, { argument := 82760106719118066135859200, coefficient := (-82760106719118066135859200) }, { argument := 2532459265605012823757291520, coefficient := (-2532459265605012823757291520) }, { argument := 1440025856912654350763950080, coefficient := (-1440025856912654350763950080) }, { argument := 2598667350980307276665978880, coefficient := (-2598667350980307276665978880) }, { argument := 40569004313711676019798179840, coefficient := (-40569004313711676019798179840) }, { argument := 1588994049007066869808496640, coefficient := (-1588994049007066869808496640) }, { argument := 3706293302095117153206272000, coefficient := (-3706293302095117153206272000) }, { argument := 2532459265605012823757291520, coefficient := (-2532459265605012823757291520) }, { argument := 82760106719118066135859200, coefficient := (-82760106719118066135859200) }, { argument := 1588994049007066869808496640, coefficient := (-1588994049007066869808496640) }, { argument := 82760106719118066135859200, coefficient := (-82760106719118066135859200) }, { argument := 2549011286948836436984463360, coefficient := (-2549011286948836436984463360) }, { argument := 1440025856912654350763950080, coefficient := (-1440025856912654350763950080) }, { argument := 109402612363411264781680640, coefficient := (-109402612363411264781680640) }, { argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }, { argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }, { argument := 183756724581423634555338752, coefficient := (-183756724581423634555338752) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0
