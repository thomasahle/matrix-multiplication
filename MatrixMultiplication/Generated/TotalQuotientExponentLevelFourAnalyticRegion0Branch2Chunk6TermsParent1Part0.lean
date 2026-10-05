import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 6, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk6

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 10554791703093118058054482395136
def positiveArguments : Array ℕ := #[
    5, 25165461, 25166187, 6383223, 183061171, 51085717,
    3744329, 138858099, 34721645, 232729, 124781, 1660753,
    21724553, 3313325, 61465
  ]
def positiveCoefficients : Array ℕ := #[
    3169126500570573503741758013440, 237681059104726449418206707712, 237687915980859576143056994304, 482302693566122005278467555328, 1728963876490537386347469996032, 482490955428328086554556760064,
    35364187540873631586706259968, 1311477665185189998356550647808, 1311746660624787219087213199360, 35169012134136629150024204288, 1178523224197914398820401152, 31370737214100847590325092352,
    410365203770100798144540311552, 31293469853708134455338598400, 1161041023478330972239298560
  ]
def positiveScales : Array ℕ := #[
    2, 24, 24, 22, 27, 25,
    21, 27, 25, 17, 16, 20,
    24, 21, 15
  ]
def negativeArguments : Array ℕ := #[
    1046722714779, 13931184662259, 182236172810805, 27793741914879, 515597680395, 2811869008467,
    208555692552399, 104299450922175, 5592511774989, 2811869008467, 40320183987507, 11251756386689,
    1046722714779, 1046755074917, 1046755074917, 13931627141389, 182241345373643, 27794627288321,
    515613901045, 40320183987507, 1495266605186077, 373892915037035, 10024589439553, 208555692552399,
    1495266605186077, 417274329981509, 13931184662259, 13931627141389, 11251756386689, 417274329981509,
    52170086040555, 5594666965617, 104299450922175, 373892915037035, 52170086040555, 182236172810805,
    182241345373643, 5592511774989, 10024589439553, 5594666965617, 27793741914879, 27794627288321,
    515597680395, 515613901045, 3, 17, 17, 3
  ]
def negativeCoefficients : Array ℕ := #[
    294626251764933647897985024, 7842559756722400196252663808, 102589844995520839081430876160, 7823242858192550022164250624, 290255690162501761357578240, 3165883054686656815492497408,
    117406417408122483027883327488, 117430742077013666349396787200, 3148304243238196446461165568, 3165883054686656815492497408, 11349122848852897796657774592, 3167087866897261181202857984,
    294626251764933647897985024, 294635360334023551512215552, 294635360334023551512215552, 7842808850328023598909882368, 102592756889529559990839279616, 7823492068661517205505048576,
    290264821576663724762071040, 11349122848852897796657774592, 420880132870972683684268736512, 420965998209314836658876579840, 11286684316128275033931907072, 117406417408122483027883327488,
    420880132870972683684268736512, 117452282313499832466123259904, 7842559756722400196252663808, 7842808850328023598909882368, 3167087866897261181202857984, 117452282313499832466123259904,
    117476590026065106535333232640, 3149517507701843094619029504, 117430742077013666349396787200, 420965998209314836658876579840, 117476590026065106535333232640, 102589844995520839081430876160,
    102592756889529559990839279616, 3148304243238196446461165568, 11286684316128275033931907072, 3149517507701843094619029504, 7823242858192550022164250624, 7823492068661517205505048576,
    290255690162501761357578240, 290264821576663724762071040, 475368975085586025561263702016, 2693757525484987478180494311424, 2693757525484987478180494311424, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    39, 43, 47, 44, 38, 41,
    47, 46, 42, 41, 45, 43,
    39, 39, 39, 43, 47, 44,
    38, 45, 50, 48, 43, 47,
    50, 48, 43, 43, 43, 48,
    45, 42, 46, 48, 45, 47,
    47, 42, 43, 42, 44, 44,
    38, 38, 1, 4, 4, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 24584941690670084, 24584983310471596, 22605853619024765, 27447750573465502, 25606416650215363,
    21836275773878748, 27049036084951223, 25049331963869599, 17828291468304222, 16929038750393939, 20663406089839329,
    24372823156955803, 21659848291875664, 15907477510015004
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    39929016457353342, 43663383178776485, 47372802682486640, 44659825313463947, 38907454821972254, 41354666526360062,
    47567426019722372, 46567724891326724, 42346633527518859, 41354666526360062, 45196567455638876, 43355215455652154,
    39929016457353342, 39929061058558796, 39929061058558796, 43663429000601761, 47372843631134407, 44659871269979434,
    38907500208299974, 45196567455638876, 50409324162374720, 48409618461994726, 43188608385363048, 47567426019722372,
    50409324162374720, 48567989499571854, 43663383178776485, 43663429000601761, 43355215455652154, 48567989499571854,
    45568288046243887, 42347189392932606, 46567724891326724, 48409618461994726, 45568288046243887, 47372802682486640,
    47372843631134407, 42346633527518859, 43188608385363048, 42347189392932606, 44659825313463947, 44659871269979434,
    38907454821972254, 38907500208299974, 1584962500724866, 4087462841250340, 4087462841250340, 1584962500724866
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
noncomputable def positiveFloor : ℝ := 64269387 / 31250000000
noncomputable def negativeCeiling : ℝ := 1061129267 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 294626251764933647897985024, coefficient := (-294626251764933647897985024) }, { argument := 7842559756722400196252663808, coefficient := (-7842559756722400196252663808) }, { argument := 102589844995520839081430876160, coefficient := (-102589844995520839081430876160) }, { argument := 7823242858192550022164250624, coefficient := (-7823242858192550022164250624) }, { argument := 290255690162501761357578240, coefficient := (-290255690162501761357578240) }, { argument := 3165883054686656815492497408, coefficient := (-3165883054686656815492497408) }, { argument := 117406417408122483027883327488, coefficient := (-117406417408122483027883327488) }, { argument := 117430742077013666349396787200, coefficient := (-117430742077013666349396787200) }, { argument := 3148304243238196446461165568, coefficient := (-3148304243238196446461165568) }, { argument := 3165883054686656815492497408, coefficient := (-3165883054686656815492497408) }, { argument := 11349122848852897796657774592, coefficient := (-11349122848852897796657774592) }, { argument := 3167087866897261181202857984, coefficient := (-3167087866897261181202857984) }, { argument := 294626251764933647897985024, coefficient := (-294626251764933647897985024) }, { argument := 294635360334023551512215552, coefficient := (-294635360334023551512215552) }, { argument := 294635360334023551512215552, coefficient := (-294635360334023551512215552) }, { argument := 7842808850328023598909882368, coefficient := (-7842808850328023598909882368) }, { argument := 102592756889529559990839279616, coefficient := (-102592756889529559990839279616) }, { argument := 7823492068661517205505048576, coefficient := (-7823492068661517205505048576) }, { argument := 290264821576663724762071040, coefficient := (-290264821576663724762071040) }, { argument := 11349122848852897796657774592, coefficient := (-11349122848852897796657774592) }, { argument := 420880132870972683684268736512, coefficient := (-420880132870972683684268736512) }, { argument := 420965998209314836658876579840, coefficient := (-420965998209314836658876579840) }, { argument := 11286684316128275033931907072, coefficient := (-11286684316128275033931907072) }, { argument := 117406417408122483027883327488, coefficient := (-117406417408122483027883327488) }, { argument := 420880132870972683684268736512, coefficient := (-420880132870972683684268736512) }, { argument := 117452282313499832466123259904, coefficient := (-117452282313499832466123259904) }, { argument := 7842559756722400196252663808, coefficient := (-7842559756722400196252663808) }, { argument := 7842808850328023598909882368, coefficient := (-7842808850328023598909882368) }, { argument := 3167087866897261181202857984, coefficient := (-3167087866897261181202857984) }, { argument := 117452282313499832466123259904, coefficient := (-117452282313499832466123259904) }, { argument := 117476590026065106535333232640, coefficient := (-117476590026065106535333232640) }, { argument := 3149517507701843094619029504, coefficient := (-3149517507701843094619029504) }, { argument := 117430742077013666349396787200, coefficient := (-117430742077013666349396787200) }, { argument := 420965998209314836658876579840, coefficient := (-420965998209314836658876579840) }, { argument := 117476590026065106535333232640, coefficient := (-117476590026065106535333232640) }, { argument := 102589844995520839081430876160, coefficient := (-102589844995520839081430876160) }, { argument := 102592756889529559990839279616, coefficient := (-102592756889529559990839279616) }, { argument := 3148304243238196446461165568, coefficient := (-3148304243238196446461165568) }, { argument := 11286684316128275033931907072, coefficient := (-11286684316128275033931907072) }, { argument := 3149517507701843094619029504, coefficient := (-3149517507701843094619029504) }, { argument := 7823242858192550022164250624, coefficient := (-7823242858192550022164250624) }, { argument := 7823492068661517205505048576, coefficient := (-7823492068661517205505048576) }, { argument := 290255690162501761357578240, coefficient := (-290255690162501761357578240) }, { argument := 290264821576663724762071040, coefficient := (-290264821576663724762071040) }, { argument := 3169126500570573503741758013440, coefficient := 3169126500570573503741758013440 }, { argument := 237681059104726449418206707712, coefficient := 237681059104726449418206707712 }, { argument := 237687915980859576143056994304, coefficient := 237687915980859576143056994304 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 482302693566122005278467555328, coefficient := 482302693566122005278467555328 }, { argument := 1728963876490537386347469996032, coefficient := 1728963876490537386347469996032 }, { argument := 482490955428328086554556760064, coefficient := 482490955428328086554556760064 }, { argument := 2693757525484987478180494311424, coefficient := (-2693757525484987478180494311424) }, { argument := 35364187540873631586706259968, coefficient := 35364187540873631586706259968 }, { argument := 1311477665185189998356550647808, coefficient := 1311477665185189998356550647808 }, { argument := 1311746660624787219087213199360, coefficient := 1311746660624787219087213199360 }, { argument := 35169012134136629150024204288, coefficient := 35169012134136629150024204288 }, { argument := 2693757525484987478180494311424, coefficient := (-2693757525484987478180494311424) }, { argument := 1178523224197914398820401152, coefficient := 1178523224197914398820401152 }, { argument := 31370737214100847590325092352, coefficient := 31370737214100847590325092352 }, { argument := 410365203770100798144540311552, coefficient := 410365203770100798144540311552 }, { argument := 31293469853708134455338598400, coefficient := 31293469853708134455338598400 }, { argument := 1161041023478330972239298560, coefficient := 1161041023478330972239298560 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk6
