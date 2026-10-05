import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 1, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-918494586287926940018499162996736)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    276206895, 1074137925, 97333077, 3987754185, 82110946695, 3987754185,
    97333077, 4770556805, 47681493985, 95362964665, 4770556805, 8191318047,
    2475668955, 64238915, 68603747659, 3987754185, 16402412615, 3987754185,
    4155763655, 2475668955, 123536375, 422707565, 4224942505, 8449882945,
    422707565, 7039860597, 51289054509, 14079730665, 611975451, 22514405,
    611975451, 22514405, 1126896215, 8395209565, 7211569365, 1505996675,
    280970235, 468283725, 14329481985, 468283725, 280970235, 229552681995,
    14704108965, 8395209565, 14329481985, 468283725, 14704108965, 468283725,
    14329481985, 468283725, 1126896215, 7792192965, 2148275325, 3652068495,
    24244821525, 2148275325, 7304136105, 2148275325, 2148275325, 89061357045,
    552413655, 24244821525, 89061357045, 7792192965
  ]
def negativeCoefficients : Array ℕ := #[
    81521886455343462139161477120, 79257389609361699301962547200, 224434795165708182884450304, 36780540439779606465588756480, 378669904833168035913431777280, 36780540439779606465588756480,
    224434795165708182884450304, 22000310117732130763801886720, 879568316593416382015351029760, 879568101642731063114800824320, 22000310117732130763801886720, 37775786909841837097104703488,
    22834015812056484311350640640, 1184998824577781620948336640, 158189471945365471890262458368, 36780540439779606465588756480, 37821388462536254909034004480, 36780540439779606465588756480,
    38330154287304397816059658240, 22834015812056484311350640640, 1139421946709405404758016000, 1949394567393986270210293760, 77936433115872337646929838080, 77936414069609081541817794560,
    1949394567393986270210293760, 64931253373725568022008037376, 236529015577515476666743259136, 64931297051003848547798876160, 1411119315498747511651172352, 51914683375855837181378560,
    1411119315498747511651172352, 51914683375855837181378560, 2598445759467121840677191680, 38716070572678373189626101760, 66514987222979552170915921920, 13890367619791269824718438400,
    41463888139000240314337198080, 2159577507239595849705062400, 66083071721531633000974909440, 69106480231667067190561996800, 41463888139000240314337198080, 1058624894048849885525421588480,
    67810733727323309680738959360, 38716070572678373189626101760, 66083071721531633000974909440, 2159577507239595849705062400, 67810733727323309680738959360, 2159577507239595849705062400,
    66083071721531633000974909440, 69106480231667067190561996800, 2598445759467121840677191680, 71870294699157504777749790720, 79257370240280421906933350400, 134737545733845222474739875840,
    894476035568879047235390668800, 79257370240280421906933350400, 134737529408476717241786695680, 79257370240280421906933350400, 79257370240280421906933350400, 3285784120532768348198865469440,
    81521866532859862532845731840, 894476035568879047235390668800, 3285784120532768348198865469440, 71870294699157504777749790720
  ]
def negativeScales : Array ℕ := #[
    28, 30, 26, 31, 36, 31,
    26, 32, 35, 36, 32, 32,
    31, 25, 35, 31, 33, 31,
    31, 31, 26, 28, 31, 32,
    28, 32, 35, 33, 29, 24,
    29, 24, 30, 32, 32, 30,
    28, 28, 33, 28, 28, 37,
    33, 32, 33, 28, 33, 28,
    33, 28, 30, 32, 31, 31,
    34, 31, 32, 31, 31, 36,
    29, 34, 36, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    28041174093387647, 30000532108890301, 26536426828052586, 31892929339029355, 36256855517890492, 31892929339029355,
    26536426828052586, 32151510517057940, 35472710388763228, 36472710036194451, 32151510517057940, 32931448473016643,
    31205171265101290, 25936944198394613, 35997568361186070, 31892929339029355, 33933188991768299, 31892929339029355,
    31952466473027938, 31205171265101290, 26880360664739007, 28655084690962677, 31976284578782611, 32976284226213741,
    28655084690962677, 32712899715047732, 35577931924993025, 33712900685504460, 29188898540397695, 24424345015535906,
    29188898540397695, 24424345015535906, 30069707506142770, 32966919206633430, 32747666103781051, 30488071438759692,
    28065842063593626, 28802807658443850, 33738267405738762, 28802807658443850, 28065842063593626, 37740034331919896,
    33775500312152842, 32966919206633430, 33738267405738762, 28802807658443850, 33775500312152842, 28802807658443850,
    33738267405738762, 28802807658443850, 30069707506142770, 32859382260658058, 31000531756321524, 31766066677805731,
    34496957582441267, 31000531756321524, 32766066503002712, 31000531756321524, 31000531756321524, 36374080543443304,
    29041173740818870, 34496957582441267, 36374080543443304, 32859382260658058
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
noncomputable def negativeCeiling : ℝ := 3045992027 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 81521886455343462139161477120, coefficient := (-81521886455343462139161477120) }, { argument := 79257389609361699301962547200, coefficient := (-79257389609361699301962547200) }, { argument := 224434795165708182884450304, coefficient := (-224434795165708182884450304) }, { argument := 36780540439779606465588756480, coefficient := (-36780540439779606465588756480) }, { argument := 378669904833168035913431777280, coefficient := (-378669904833168035913431777280) }, { argument := 36780540439779606465588756480, coefficient := (-36780540439779606465588756480) }, { argument := 224434795165708182884450304, coefficient := (-224434795165708182884450304) }, { argument := 22000310117732130763801886720, coefficient := (-22000310117732130763801886720) }, { argument := 879568316593416382015351029760, coefficient := (-879568316593416382015351029760) }, { argument := 879568101642731063114800824320, coefficient := (-879568101642731063114800824320) }, { argument := 22000310117732130763801886720, coefficient := (-22000310117732130763801886720) }, { argument := 37775786909841837097104703488, coefficient := (-37775786909841837097104703488) }, { argument := 22834015812056484311350640640, coefficient := (-22834015812056484311350640640) }, { argument := 1184998824577781620948336640, coefficient := (-1184998824577781620948336640) }, { argument := 158189471945365471890262458368, coefficient := (-158189471945365471890262458368) }, { argument := 36780540439779606465588756480, coefficient := (-36780540439779606465588756480) }, { argument := 37821388462536254909034004480, coefficient := (-37821388462536254909034004480) }, { argument := 36780540439779606465588756480, coefficient := (-36780540439779606465588756480) }, { argument := 38330154287304397816059658240, coefficient := (-38330154287304397816059658240) }, { argument := 22834015812056484311350640640, coefficient := (-22834015812056484311350640640) }, { argument := 1139421946709405404758016000, coefficient := (-1139421946709405404758016000) }, { argument := 1949394567393986270210293760, coefficient := (-1949394567393986270210293760) }, { argument := 77936433115872337646929838080, coefficient := (-77936433115872337646929838080) }, { argument := 77936414069609081541817794560, coefficient := (-77936414069609081541817794560) }, { argument := 1949394567393986270210293760, coefficient := (-1949394567393986270210293760) }, { argument := 64931253373725568022008037376, coefficient := (-64931253373725568022008037376) }, { argument := 236529015577515476666743259136, coefficient := (-236529015577515476666743259136) }, { argument := 64931297051003848547798876160, coefficient := (-64931297051003848547798876160) }, { argument := 1411119315498747511651172352, coefficient := (-1411119315498747511651172352) }, { argument := 51914683375855837181378560, coefficient := (-51914683375855837181378560) }, { argument := 1411119315498747511651172352, coefficient := (-1411119315498747511651172352) }, { argument := 51914683375855837181378560, coefficient := (-51914683375855837181378560) }, { argument := 2598445759467121840677191680, coefficient := (-2598445759467121840677191680) }, { argument := 38716070572678373189626101760, coefficient := (-38716070572678373189626101760) }, { argument := 66514987222979552170915921920, coefficient := (-66514987222979552170915921920) }, { argument := 13890367619791269824718438400, coefficient := (-13890367619791269824718438400) }, { argument := 41463888139000240314337198080, coefficient := (-41463888139000240314337198080) }, { argument := 2159577507239595849705062400, coefficient := (-2159577507239595849705062400) }, { argument := 66083071721531633000974909440, coefficient := (-66083071721531633000974909440) }, { argument := 69106480231667067190561996800, coefficient := (-69106480231667067190561996800) }, { argument := 41463888139000240314337198080, coefficient := (-41463888139000240314337198080) }, { argument := 1058624894048849885525421588480, coefficient := (-1058624894048849885525421588480) }, { argument := 67810733727323309680738959360, coefficient := (-67810733727323309680738959360) }, { argument := 38716070572678373189626101760, coefficient := (-38716070572678373189626101760) }, { argument := 66083071721531633000974909440, coefficient := (-66083071721531633000974909440) }, { argument := 2159577507239595849705062400, coefficient := (-2159577507239595849705062400) }, { argument := 67810733727323309680738959360, coefficient := (-67810733727323309680738959360) }, { argument := 2159577507239595849705062400, coefficient := (-2159577507239595849705062400) }, { argument := 66083071721531633000974909440, coefficient := (-66083071721531633000974909440) }, { argument := 69106480231667067190561996800, coefficient := (-69106480231667067190561996800) }, { argument := 2598445759467121840677191680, coefficient := (-2598445759467121840677191680) }, { argument := 71870294699157504777749790720, coefficient := (-71870294699157504777749790720) }, { argument := 79257370240280421906933350400, coefficient := (-79257370240280421906933350400) }, { argument := 134737545733845222474739875840, coefficient := (-134737545733845222474739875840) }, { argument := 894476035568879047235390668800, coefficient := (-894476035568879047235390668800) }, { argument := 79257370240280421906933350400, coefficient := (-79257370240280421906933350400) }, { argument := 134737529408476717241786695680, coefficient := (-134737529408476717241786695680) }, { argument := 79257370240280421906933350400, coefficient := (-79257370240280421906933350400) }, { argument := 79257370240280421906933350400, coefficient := (-79257370240280421906933350400) }, { argument := 3285784120532768348198865469440, coefficient := (-3285784120532768348198865469440) }, { argument := 81521866532859862532845731840, coefficient := (-81521866532859862532845731840) }, { argument := 894476035568879047235390668800, coefficient := (-894476035568879047235390668800) }, { argument := 3285784120532768348198865469440, coefficient := (-3285784120532768348198865469440) }, { argument := 71870294699157504777749790720, coefficient := (-71870294699157504777749790720) }] }

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


end Parent0

namespace Parent0

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-711788495290845100299985163911168)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2148275325, 552413655, 2148275325, 2899095045, 50975940885, 1322729005,
    113015217115, 82110946695, 6001687475, 82110946695, 85570391785, 50975940885,
    2543709625, 422707565, 4224942505, 8449882945, 422707565, 274280283,
    1998274851, 548560935, 4521852645, 4465390875, 4521852645, 4465390875,
    457133805, 3330458085, 914268225, 111, 111, 22514405,
    4465390875, 4465390875, 22514405, 97333077, 3987754185, 82110946695,
    3987754185, 97333077, 422707565, 4224942505, 8449882945, 422707565,
    101433851, 4155763655, 85570391785, 4155763655, 101433851, 17524247909,
    175154044993, 350308004377, 17524247909, 13988294433, 101912017401, 27976607685,
    108696231, 1086413787, 2172827043, 108696231, 457133805, 3330458085,
    914268225, 9, 9, 60426111
  ]
def negativeCoefficients : Array ℕ := #[
    79257370240280421906933350400, 81521866532859862532845731840, 79257370240280421906933350400, 13369716085118618964779335680, 235085033855535546459268055040, 12200021717053740934013911040,
    260595348319390567416442388480, 378669904833168035913431777280, 13838949107714136590201651200, 378669904833168035913431777280, 394623779386238312519449968640, 235085033855535546459268055040,
    11730790112551673975013376000, 1949394567393986270210293760, 77936433115872337646929838080, 77936414069609081541817794560, 1949394567393986270210293760, 40476625479725029416316698624,
    147446659061308349090956836864, 40476652707119282211614883840, 10426682310167701367071703040, 10296490332525369898303488000, 10426682310167701367071703040, 10296490332525369898303488000,
    2108157577069011948766494720, 7679513492776476515154001920, 2108158995162462615188275200, 1073526127817790707139084288, 1073526127817790707139084288, 51914683375855837181378560,
    10296490332525369898303488000, 10296490332525369898303488000, 51914683375855837181378560, 224434795165708182884450304, 36780540439779606465588756480, 378669904833168035913431777280,
    36780540439779606465588756480, 224434795165708182884450304, 1949394567393986270210293760, 77936433115872337646929838080, 77936414069609081541817794560, 1949394567393986270210293760,
    233890536225973459486769152, 38330154287304397816059658240, 394623779386238312519449968640, 38330154287304397816059658240, 233890536225973459486769152, 80816329065390687945003892736,
    3231021841460878912162719858688, 3231021051857222209062217711616, 80816329065390687945003892736, 64509621858311765632254738432, 234993112878960181363712458752, 64509665251971356024761221120,
    2005091555033814449359159296, 80163188347754404436842119168, 80163168757312198157298302976, 2005091555033814449359159296, 67461042466208382360527831040, 245744431768847248484928061440,
    67461087845198803686024806400, 1392682544196052809261514752, 1392682544196052809261514752, 139333125623320693463580672
  ]
def negativeScales : Array ℕ := #[
    31, 29, 31, 31, 35, 30,
    36, 36, 32, 36, 36, 35,
    31, 28, 31, 32, 28, 28,
    30, 29, 32, 32, 32, 32,
    28, 31, 29, 6, 6, 24,
    32, 32, 24, 26, 31, 36,
    31, 26, 28, 31, 32, 28,
    26, 31, 36, 31, 26, 34,
    37, 38, 34, 33, 36, 34,
    26, 30, 31, 26, 28, 31,
    29, 3, 3, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31000531756321524, 29041173740818870, 31000531756321524, 31432955486006646, 35569097447810268, 30300870372753804,
    36717726083575182, 36256855517890492, 32482721049629260, 36256855517890492, 36316392644867856, 35569097447810268,
    31244286844387436, 28655084690962677, 31976284578782611, 32976284226213741, 28655084690962677, 28031075674976223,
    30896107889088806, 29031076645432949, 32074266833295617, 32056139320204539, 32074266833295617, 32056139320204539,
    28768041269474333, 31633073479196219, 29768042239931066, 6794415866926375, 6794415866926375, 24424345015535906,
    32056139320204539, 32056139320204539, 24424345015535906, 26536426828052586, 31892929339029355, 36256855517890492,
    31892929339029355, 26536426828052586, 28655084690962677, 31976284578782611, 32976284226213741, 28655084690962677,
    26595963955034128, 31952466473027938, 36316392644867856, 31952466473027938, 26595963955034128, 34028633478060219,
    37349833349765402, 38349832997196625, 34028633478060219, 33703501017026303, 36568533226990051, 34703501987483031,
    26695726675501230, 30016926547140969, 31016926194572192, 26695726675501230, 28768041269474333, 31633073479196219,
    29768042239931066, 3169925001442313, 3169925001442313, 25848668759657764
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
noncomputable def negativeCeiling : ℝ := 492633743 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 79257370240280421906933350400, coefficient := (-79257370240280421906933350400) }, { argument := 81521866532859862532845731840, coefficient := (-81521866532859862532845731840) }, { argument := 79257370240280421906933350400, coefficient := (-79257370240280421906933350400) }, { argument := 13369716085118618964779335680, coefficient := (-13369716085118618964779335680) }, { argument := 235085033855535546459268055040, coefficient := (-235085033855535546459268055040) }, { argument := 12200021717053740934013911040, coefficient := (-12200021717053740934013911040) }, { argument := 260595348319390567416442388480, coefficient := (-260595348319390567416442388480) }, { argument := 378669904833168035913431777280, coefficient := (-378669904833168035913431777280) }, { argument := 13838949107714136590201651200, coefficient := (-13838949107714136590201651200) }, { argument := 378669904833168035913431777280, coefficient := (-378669904833168035913431777280) }, { argument := 394623779386238312519449968640, coefficient := (-394623779386238312519449968640) }, { argument := 235085033855535546459268055040, coefficient := (-235085033855535546459268055040) }, { argument := 11730790112551673975013376000, coefficient := (-11730790112551673975013376000) }, { argument := 1949394567393986270210293760, coefficient := (-1949394567393986270210293760) }, { argument := 77936433115872337646929838080, coefficient := (-77936433115872337646929838080) }, { argument := 77936414069609081541817794560, coefficient := (-77936414069609081541817794560) }, { argument := 1949394567393986270210293760, coefficient := (-1949394567393986270210293760) }, { argument := 40476625479725029416316698624, coefficient := (-40476625479725029416316698624) }, { argument := 147446659061308349090956836864, coefficient := (-147446659061308349090956836864) }, { argument := 40476652707119282211614883840, coefficient := (-40476652707119282211614883840) }, { argument := 10426682310167701367071703040, coefficient := (-10426682310167701367071703040) }, { argument := 10296490332525369898303488000, coefficient := (-10296490332525369898303488000) }, { argument := 10426682310167701367071703040, coefficient := (-10426682310167701367071703040) }, { argument := 10296490332525369898303488000, coefficient := (-10296490332525369898303488000) }, { argument := 2108157577069011948766494720, coefficient := (-2108157577069011948766494720) }, { argument := 7679513492776476515154001920, coefficient := (-7679513492776476515154001920) }, { argument := 2108158995162462615188275200, coefficient := (-2108158995162462615188275200) }, { argument := 1073526127817790707139084288, coefficient := (-1073526127817790707139084288) }, { argument := 1073526127817790707139084288, coefficient := (-1073526127817790707139084288) }, { argument := 51914683375855837181378560, coefficient := (-51914683375855837181378560) }, { argument := 10296490332525369898303488000, coefficient := (-10296490332525369898303488000) }, { argument := 10296490332525369898303488000, coefficient := (-10296490332525369898303488000) }, { argument := 51914683375855837181378560, coefficient := (-51914683375855837181378560) }, { argument := 224434795165708182884450304, coefficient := (-224434795165708182884450304) }, { argument := 36780540439779606465588756480, coefficient := (-36780540439779606465588756480) }, { argument := 378669904833168035913431777280, coefficient := (-378669904833168035913431777280) }, { argument := 36780540439779606465588756480, coefficient := (-36780540439779606465588756480) }, { argument := 224434795165708182884450304, coefficient := (-224434795165708182884450304) }, { argument := 1949394567393986270210293760, coefficient := (-1949394567393986270210293760) }, { argument := 77936433115872337646929838080, coefficient := (-77936433115872337646929838080) }, { argument := 77936414069609081541817794560, coefficient := (-77936414069609081541817794560) }, { argument := 1949394567393986270210293760, coefficient := (-1949394567393986270210293760) }, { argument := 233890536225973459486769152, coefficient := (-233890536225973459486769152) }, { argument := 38330154287304397816059658240, coefficient := (-38330154287304397816059658240) }, { argument := 394623779386238312519449968640, coefficient := (-394623779386238312519449968640) }, { argument := 38330154287304397816059658240, coefficient := (-38330154287304397816059658240) }, { argument := 233890536225973459486769152, coefficient := (-233890536225973459486769152) }, { argument := 80816329065390687945003892736, coefficient := (-80816329065390687945003892736) }, { argument := 3231021841460878912162719858688, coefficient := (-3231021841460878912162719858688) }, { argument := 3231021051857222209062217711616, coefficient := (-3231021051857222209062217711616) }, { argument := 80816329065390687945003892736, coefficient := (-80816329065390687945003892736) }, { argument := 64509621858311765632254738432, coefficient := (-64509621858311765632254738432) }, { argument := 234993112878960181363712458752, coefficient := (-234993112878960181363712458752) }, { argument := 64509665251971356024761221120, coefficient := (-64509665251971356024761221120) }, { argument := 2005091555033814449359159296, coefficient := (-2005091555033814449359159296) }, { argument := 80163188347754404436842119168, coefficient := (-80163188347754404436842119168) }, { argument := 80163168757312198157298302976, coefficient := (-80163168757312198157298302976) }, { argument := 2005091555033814449359159296, coefficient := (-2005091555033814449359159296) }, { argument := 67461042466208382360527831040, coefficient := (-67461042466208382360527831040) }, { argument := 245744431768847248484928061440, coefficient := (-245744431768847248484928061440) }, { argument := 67461087845198803686024806400, coefficient := (-67461087845198803686024806400) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 139333125623320693463580672, coefficient := (-139333125623320693463580672) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1
