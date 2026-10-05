import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 18, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2902751742335424096783023650897920)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    71878599, 12317263, 12317263, 13648859, 654028459, 15603275415,
    12271727629, 6586202805, 644076615, 6586202805, 13151628945, 654081575,
    15603275415, 644076615, 1350758117, 4916034209, 8546970355, 22042186705,
    18443462345, 515967105115, 19214296707, 18443462345, 16644100165, 8546970355,
    8546970355, 16644100165, 515967105115, 16644100165, 1350758091, 22042186705,
    11674525797, 176189113089, 307155819729, 46615070799, 97201208775, 11664145053,
    307155819729, 610423591107, 97201208775, 9420741154473, 602647494405, 352378227861,
    307155819729, 11664145053, 602647494405, 11664145053, 307155819729, 307155819729,
    11674525797, 11746579, 2060239597, 515059961, 2936583, 10813275,
    5112238725, 194056505775, 20448968925, 10813275, 4617182781, 2393881637,
    9928723055, 25048176153, 1109359783, 19857440197
  ]
def negativeCoefficients : Array ℕ := #[
    2651852240259590606152531968, 113606699124785966433173504, 113606699124785966433173504, 125888504435573638480003072, 754043475005977528562089984, 17989351768256824661287895040,
    14148338682152094817954299904, 15186749695172871951073935360, 742569780047884906125066240, 15186749695172871951073935360, 15162795831300359534747320320, 754104713584616225846067200,
    17989351768256824661287895040, 742569780047884906125066240, 99668357159139292582969868288, 90684824911024173274307231744, 78831887372133736271147171840, 101651644243014554665426616320,
    1360887318845256078786119598080, 2379478284627299881658047528960, 88610303477587300722438832128, 1360887318845256078786119598080, 76757364020235480053485404160, 78831887372133736271147171840,
    78831887372133736271147171840, 76757364020235480053485404160, 2379478284627299881658047528960, 76757364020235480053485404160, 99668355240677908917176500224, 101651644243014554665426616320,
    53839247389794757456573759488, 812528869431663185352726675456, 1416506199322832531117379158016, 107487035125875552892798107648, 896522910963818057669227315200, 53791374657829083460153638912,
    1416506199322832531117379158016, 1407540970213194350540686884864, 896522910963818057669227315200, 21722750132653311537325377847296, 1389610511993917989387302338560, 812528873312396969859373596672,
    1416506199322832531117379158016, 53791374657829083460153638912, 1389610511993917989387302338560, 53791374657829083460153638912, 1416506199322832531117379158016, 1416506199322832531117379158016,
    53839247389794757456573759488, 108343068277305535555960832, 19002356288190752458199269376, 19002358566363645561328893952, 108340790104412432426336256, 797878866094566607002009600,
    94304159403782224173701529600, 894927674467441157210741145600, 94304224082678632617816883200, 797878866094566607002009600, 21292997275661384129156481024, 22079660950245935042523037696,
    91576306587162322251745853440, 231028647503792832518106906624, 20464076002666964185753059328, 91576279318262895290601177088
  ]
def negativeScales : Array ℕ := #[
    26, 23, 23, 23, 29, 33,
    33, 32, 29, 32, 33, 29,
    33, 29, 30, 32, 32, 34,
    34, 38, 34, 34, 33, 32,
    32, 33, 38, 33, 30, 34,
    33, 37, 38, 35, 36, 33,
    38, 39, 36, 43, 39, 38,
    38, 33, 39, 33, 38, 38,
    33, 23, 30, 28, 21, 23,
    32, 37, 34, 23, 32, 31,
    33, 34, 30, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    26099058953478839, 23554178376819980, 23554178376819980, 23702277015883969, 29284778172750203, 33861129860161949,
    33514619316565838, 32616799790657132, 29262657070895659, 32616799790657132, 33614522449945534, 29284895334438199,
    33861129860161949, 29262657070895659, 30331122205446674, 32194847808952926, 32992765993505475, 34359548303089869,
    34102390463592743, 38908488140071985, 34161461119867504, 34102390463592743, 33954291835809118, 32992765993505475,
    32992765993505475, 33954291835809118, 38908488140071985, 33954291835809118, 30331122177677031, 34359548303089869,
    33442644899732751, 37358333825126234, 38160179762288691, 35440077407012451, 36500255203886586, 33441361514832778,
    38160179762288691, 39151019763003215, 36500255203886586, 43098977703562934, 39132523419385825, 38358333832016716,
    38160179762288691, 33441361514832778, 39132523419385825, 33441361514832778, 38160179762288691, 38160179762288691,
    33442644899732751, 23485737320716763, 30940164989197410, 28940165162160646, 21485706984273985, 23366300200298554,
    32251308061032546, 37497685844274430, 34251309050510546, 23366300200298554, 32104365699655476, 31156704675467918,
    33208961036928189, 34543986508350486, 30047080184293419, 34208960607333315
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
noncomputable def negativeCeiling : ℝ := 1133427637 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2651852240259590606152531968, coefficient := (-2651852240259590606152531968) }, { argument := 113606699124785966433173504, coefficient := (-113606699124785966433173504) }, { argument := 113606699124785966433173504, coefficient := (-113606699124785966433173504) }, { argument := 125888504435573638480003072, coefficient := (-125888504435573638480003072) }, { argument := 754043475005977528562089984, coefficient := (-754043475005977528562089984) }, { argument := 17989351768256824661287895040, coefficient := (-17989351768256824661287895040) }, { argument := 14148338682152094817954299904, coefficient := (-14148338682152094817954299904) }, { argument := 15186749695172871951073935360, coefficient := (-15186749695172871951073935360) }, { argument := 742569780047884906125066240, coefficient := (-742569780047884906125066240) }, { argument := 15186749695172871951073935360, coefficient := (-15186749695172871951073935360) }, { argument := 15162795831300359534747320320, coefficient := (-15162795831300359534747320320) }, { argument := 754104713584616225846067200, coefficient := (-754104713584616225846067200) }, { argument := 17989351768256824661287895040, coefficient := (-17989351768256824661287895040) }, { argument := 742569780047884906125066240, coefficient := (-742569780047884906125066240) }, { argument := 99668357159139292582969868288, coefficient := (-99668357159139292582969868288) }, { argument := 90684824911024173274307231744, coefficient := (-90684824911024173274307231744) }, { argument := 78831887372133736271147171840, coefficient := (-78831887372133736271147171840) }, { argument := 101651644243014554665426616320, coefficient := (-101651644243014554665426616320) }, { argument := 1360887318845256078786119598080, coefficient := (-1360887318845256078786119598080) }, { argument := 2379478284627299881658047528960, coefficient := (-2379478284627299881658047528960) }, { argument := 88610303477587300722438832128, coefficient := (-88610303477587300722438832128) }, { argument := 1360887318845256078786119598080, coefficient := (-1360887318845256078786119598080) }, { argument := 76757364020235480053485404160, coefficient := (-76757364020235480053485404160) }, { argument := 78831887372133736271147171840, coefficient := (-78831887372133736271147171840) }, { argument := 78831887372133736271147171840, coefficient := (-78831887372133736271147171840) }, { argument := 76757364020235480053485404160, coefficient := (-76757364020235480053485404160) }, { argument := 2379478284627299881658047528960, coefficient := (-2379478284627299881658047528960) }, { argument := 76757364020235480053485404160, coefficient := (-76757364020235480053485404160) }, { argument := 99668355240677908917176500224, coefficient := (-99668355240677908917176500224) }, { argument := 101651644243014554665426616320, coefficient := (-101651644243014554665426616320) }, { argument := 53839247389794757456573759488, coefficient := (-53839247389794757456573759488) }, { argument := 812528869431663185352726675456, coefficient := (-812528869431663185352726675456) }, { argument := 1416506199322832531117379158016, coefficient := (-1416506199322832531117379158016) }, { argument := 107487035125875552892798107648, coefficient := (-107487035125875552892798107648) }, { argument := 896522910963818057669227315200, coefficient := (-896522910963818057669227315200) }, { argument := 53791374657829083460153638912, coefficient := (-53791374657829083460153638912) }, { argument := 1416506199322832531117379158016, coefficient := (-1416506199322832531117379158016) }, { argument := 1407540970213194350540686884864, coefficient := (-1407540970213194350540686884864) }, { argument := 896522910963818057669227315200, coefficient := (-896522910963818057669227315200) }, { argument := 21722750132653311537325377847296, coefficient := (-21722750132653311537325377847296) }, { argument := 1389610511993917989387302338560, coefficient := (-1389610511993917989387302338560) }, { argument := 812528873312396969859373596672, coefficient := (-812528873312396969859373596672) }, { argument := 1416506199322832531117379158016, coefficient := (-1416506199322832531117379158016) }, { argument := 53791374657829083460153638912, coefficient := (-53791374657829083460153638912) }, { argument := 1389610511993917989387302338560, coefficient := (-1389610511993917989387302338560) }, { argument := 53791374657829083460153638912, coefficient := (-53791374657829083460153638912) }, { argument := 1416506199322832531117379158016, coefficient := (-1416506199322832531117379158016) }, { argument := 1416506199322832531117379158016, coefficient := (-1416506199322832531117379158016) }, { argument := 53839247389794757456573759488, coefficient := (-53839247389794757456573759488) }, { argument := 108343068277305535555960832, coefficient := (-108343068277305535555960832) }, { argument := 19002356288190752458199269376, coefficient := (-19002356288190752458199269376) }, { argument := 19002358566363645561328893952, coefficient := (-19002358566363645561328893952) }, { argument := 108340790104412432426336256, coefficient := (-108340790104412432426336256) }, { argument := 797878866094566607002009600, coefficient := (-797878866094566607002009600) }, { argument := 94304159403782224173701529600, coefficient := (-94304159403782224173701529600) }, { argument := 894927674467441157210741145600, coefficient := (-894927674467441157210741145600) }, { argument := 94304224082678632617816883200, coefficient := (-94304224082678632617816883200) }, { argument := 797878866094566607002009600, coefficient := (-797878866094566607002009600) }, { argument := 21292997275661384129156481024, coefficient := (-21292997275661384129156481024) }, { argument := 22079660950245935042523037696, coefficient := (-22079660950245935042523037696) }, { argument := 91576306587162322251745853440, coefficient := (-91576306587162322251745853440) }, { argument := 231028647503792832518106906624, coefficient := (-231028647503792832518106906624) }, { argument := 20464076002666964185753059328, coefficient := (-20464076002666964185753059328) }, { argument := 91576279318262895290601177088, coefficient := (-91576279318262895290601177088) }] }

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

end TermShard2


end Parent2

namespace Parent2

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-540077511563436042838180588683264)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1109359783, 2160332209, 40812762543, 2160332209, 25048176153, 40812762543,
    288574047, 2160332209, 2160332209, 2393881637, 1297593, 613468647,
    23286780693, 2453876271, 1297593, 872507607, 17016247221, 34032481959,
    109063971, 20127401, 2352502425, 644076615, 277585363, 12546353413,
    34883365, 22874917, 4012045531, 1003011503, 5718609, 277585363,
    12546353413, 34883365, 432150459, 75795130437, 18948784881, 108035343,
    34169949, 16154674371, 613218558249, 64618741803, 34169949, 22874917,
    4012045531, 1003011503, 5718609, 67907367, 32104859193, 1218674856267,
    128419524849, 67907367, 2250151197, 43884005991, 87767979789, 281270241,
    198681457, 8980040407, 24967735, 265225389, 46518041427, 11629511751,
    66304953, 10813275, 5112238725, 194056505775
  ]
def negativeCoefficients : Array ℕ := #[
    20464076002666964185753059328, 19925547686807307233496399872, 752862585571800419254809919488, 19925547686807307233496399872, 231028647503792832518106906624, 752862585571800419254809919488,
    21293006365294526449538039808, 19925547686807307233496399872, 19925547686807307233496399872, 22079660950245935042523037696, 47872731965673996420120576, 5658249564226933450422091776,
    53695660468046469432644468736, 5658253444960717957069012992, 47872731965673996420120576, 2011865566086719061689892864, 78473589395189594211729014784, 78473560611351310197187411968,
    2011875160699480399870427136, 742570030231851405810860032, 2712250635422256182643916800, 742569780047884906125066240, 320034134366797790118412288, 14464960654245209780506329088,
    321742253292398596503633920, 105491934901586968830803968, 18502294280606785288246657024, 18502296498827760151820238848, 105489716680612105257222144, 320034134366797790118412288,
    14464960654245209780506329088, 321742253292398596503633920, 3985884459254556281769295872, 699086686602386103593752068096, 699086770415167802493099835392, 3985800646472857382421528576,
    1260648608429415239063175168, 149000571857975914194448416768, 1413985725658557028392971010048, 149000674050632239536150675456, 1260648608429415239063175168, 105491934901586968830803968,
    18502294280606785288246657024, 18502296498827760151820238848, 105489716680612105257222144, 1252669819768469572993155072, 148057530263938091952711401472, 1405036448913882616820863598592,
    148057631809805453209972506624, 1252669819768469572993155072, 2594247703638137737442230272, 101189628430639213588808466432, 101189591314637215780583768064, 2594260075638803673517129728,
    229064124341920569367724032, 10353281697468722493345759232, 230286708822600275858554880, 1223136218183265125092294656, 214526601253521915909670699008, 214526626972894840679213039616,
    1223110498810340355549954048, 797878866094566607002009600, 94304159403782224173701529600, 894927674467441157210741145600
  ]
def negativeScales : Array ℕ := #[
    30, 31, 35, 31, 34, 35,
    28, 31, 31, 31, 20, 29,
    34, 31, 20, 29, 33, 34,
    26, 24, 31, 29, 28, 33,
    25, 24, 31, 29, 22, 28,
    33, 25, 28, 36, 34, 26,
    25, 33, 39, 35, 25, 24,
    31, 29, 22, 26, 34, 40,
    36, 26, 31, 35, 36, 28,
    27, 33, 24, 27, 35, 33,
    25, 23, 32, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30047080184293419, 31008606036478784, 35248301316225270, 31008606036478784, 34543986508350486, 35248301316225270,
    28104366315518320, 31008606036478784, 31008606036478784, 31156704675467918, 20307406511244984, 29192414371978977,
    34438792155220641, 31192415361456978, 20307406511244984, 29700592468756294, 33986193866635986, 34986193337460228,
    26700599348971106, 24262657556963254, 31131549064095726, 29262657070895659, 28048356256107136, 33546549055883780,
    25056035879631821, 24447263172902002, 31901690837064168, 29901691010027392, 22447232836459224, 28048356256107136,
    33546549055883780, 25056035879631821, 28686958452701546, 36141386112308758, 34141386285271968, 26686928116258730,
    25026224758700931, 33911232624769567, 39157610402676557, 35911233614247661, 25026224758700931, 24447263172902002,
    31901690837064168, 29901691010027392, 22447232836459224, 26017064759415455, 34902072624682193, 40148450403391081,
    36902073614160274, 26017064759415455, 31067374799354514, 35352976178341977, 36352975649166382, 28067381679569314,
    27565881990810483, 33064074790583793, 24573561614335705, 27982643662676424, 35437071304432896, 33437071477396106,
    25982613326224817, 23366300200298554, 32251308061032546, 37497685844274430
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
noncomputable def negativeCeiling : ℝ := 191443837 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 20464076002666964185753059328, coefficient := (-20464076002666964185753059328) }, { argument := 19925547686807307233496399872, coefficient := (-19925547686807307233496399872) }, { argument := 752862585571800419254809919488, coefficient := (-752862585571800419254809919488) }, { argument := 19925547686807307233496399872, coefficient := (-19925547686807307233496399872) }, { argument := 231028647503792832518106906624, coefficient := (-231028647503792832518106906624) }, { argument := 752862585571800419254809919488, coefficient := (-752862585571800419254809919488) }, { argument := 21293006365294526449538039808, coefficient := (-21293006365294526449538039808) }, { argument := 19925547686807307233496399872, coefficient := (-19925547686807307233496399872) }, { argument := 19925547686807307233496399872, coefficient := (-19925547686807307233496399872) }, { argument := 22079660950245935042523037696, coefficient := (-22079660950245935042523037696) }, { argument := 47872731965673996420120576, coefficient := (-47872731965673996420120576) }, { argument := 5658249564226933450422091776, coefficient := (-5658249564226933450422091776) }, { argument := 53695660468046469432644468736, coefficient := (-53695660468046469432644468736) }, { argument := 5658253444960717957069012992, coefficient := (-5658253444960717957069012992) }, { argument := 47872731965673996420120576, coefficient := (-47872731965673996420120576) }, { argument := 2011865566086719061689892864, coefficient := (-2011865566086719061689892864) }, { argument := 78473589395189594211729014784, coefficient := (-78473589395189594211729014784) }, { argument := 78473560611351310197187411968, coefficient := (-78473560611351310197187411968) }, { argument := 2011875160699480399870427136, coefficient := (-2011875160699480399870427136) }, { argument := 742570030231851405810860032, coefficient := (-742570030231851405810860032) }, { argument := 2712250635422256182643916800, coefficient := (-2712250635422256182643916800) }, { argument := 742569780047884906125066240, coefficient := (-742569780047884906125066240) }, { argument := 320034134366797790118412288, coefficient := (-320034134366797790118412288) }, { argument := 14464960654245209780506329088, coefficient := (-14464960654245209780506329088) }, { argument := 321742253292398596503633920, coefficient := (-321742253292398596503633920) }, { argument := 105491934901586968830803968, coefficient := (-105491934901586968830803968) }, { argument := 18502294280606785288246657024, coefficient := (-18502294280606785288246657024) }, { argument := 18502296498827760151820238848, coefficient := (-18502296498827760151820238848) }, { argument := 105489716680612105257222144, coefficient := (-105489716680612105257222144) }, { argument := 320034134366797790118412288, coefficient := (-320034134366797790118412288) }, { argument := 14464960654245209780506329088, coefficient := (-14464960654245209780506329088) }, { argument := 321742253292398596503633920, coefficient := (-321742253292398596503633920) }, { argument := 3985884459254556281769295872, coefficient := (-3985884459254556281769295872) }, { argument := 699086686602386103593752068096, coefficient := (-699086686602386103593752068096) }, { argument := 699086770415167802493099835392, coefficient := (-699086770415167802493099835392) }, { argument := 3985800646472857382421528576, coefficient := (-3985800646472857382421528576) }, { argument := 1260648608429415239063175168, coefficient := (-1260648608429415239063175168) }, { argument := 149000571857975914194448416768, coefficient := (-149000571857975914194448416768) }, { argument := 1413985725658557028392971010048, coefficient := (-1413985725658557028392971010048) }, { argument := 149000674050632239536150675456, coefficient := (-149000674050632239536150675456) }, { argument := 1260648608429415239063175168, coefficient := (-1260648608429415239063175168) }, { argument := 105491934901586968830803968, coefficient := (-105491934901586968830803968) }, { argument := 18502294280606785288246657024, coefficient := (-18502294280606785288246657024) }, { argument := 18502296498827760151820238848, coefficient := (-18502296498827760151820238848) }, { argument := 105489716680612105257222144, coefficient := (-105489716680612105257222144) }, { argument := 1252669819768469572993155072, coefficient := (-1252669819768469572993155072) }, { argument := 148057530263938091952711401472, coefficient := (-148057530263938091952711401472) }, { argument := 1405036448913882616820863598592, coefficient := (-1405036448913882616820863598592) }, { argument := 148057631809805453209972506624, coefficient := (-148057631809805453209972506624) }, { argument := 1252669819768469572993155072, coefficient := (-1252669819768469572993155072) }, { argument := 2594247703638137737442230272, coefficient := (-2594247703638137737442230272) }, { argument := 101189628430639213588808466432, coefficient := (-101189628430639213588808466432) }, { argument := 101189591314637215780583768064, coefficient := (-101189591314637215780583768064) }, { argument := 2594260075638803673517129728, coefficient := (-2594260075638803673517129728) }, { argument := 229064124341920569367724032, coefficient := (-229064124341920569367724032) }, { argument := 10353281697468722493345759232, coefficient := (-10353281697468722493345759232) }, { argument := 230286708822600275858554880, coefficient := (-230286708822600275858554880) }, { argument := 1223136218183265125092294656, coefficient := (-1223136218183265125092294656) }, { argument := 214526601253521915909670699008, coefficient := (-214526601253521915909670699008) }, { argument := 214526626972894840679213039616, coefficient := (-214526626972894840679213039616) }, { argument := 1223110498810340355549954048, coefficient := (-1223110498810340355549954048) }, { argument := 797878866094566607002009600, coefficient := (-797878866094566607002009600) }, { argument := 94304159403782224173701529600, coefficient := (-94304159403782224173701529600) }, { argument := 894927674467441157210741145600, coefficient := (-894927674467441157210741145600) }] }

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

end TermShard3


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18
