import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
parent chunk 13, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-9451775295796898979274872934367232)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    25379309569, 485890233, 12900491357, 12935069789, 1966990879041, 1294384285894225,
    117711, 202428311410034975, 1231659, 54549, 50607080600819879, 54549,
    106227, 2006829, 106227, 1231659, 2006829, 5177565314005761,
    106227, 106227, 117711, 40219865337497439, 147210310552587875, 20107684408784159,
    13212638553, 207009, 124783858725, 2166021, 95931, 249567656541,
    95931, 186813, 3529251, 186813, 2166021, 3529251,
    13212638553, 186813, 186813, 207009, 44619958033, 2566119453621,
    714096253755, 5071212164791033, 5071211253351687, 40549733291, 145768846467, 20279856105,
    84917868661, 84917888907, 513, 7437, 215673, 190883,
    12395, 7437, 12395, 379287, 12395, 7437,
    6076029, 389203, 215673, 379287
  ]
def negativeCoefficients : Array ℕ := #[
    29260351774174429040915513344, 1120386597008262901127970816, 29746507810960130193819172864, 29826240246656901283607216128, 8858539389890211970428174336, 1457347146906864317960185446400,
    1111748962130137615498739712, 56978504239717014820695415193600, 11632690359849488708511203328, 1030401477096225107047612416, 56978507334040265973216623722496, 1030401477096225107047612416,
    1003285648751587604230569984, 37907928025803228938225319936, 1003285648751587604230569984, 11632690359849488708511203328, 37907928025803228938225319936, 1457355076177671897126814089216,
    1003285648751587604230569984, 1003285648751587604230569984, 1111748962130137615498739712, 11320885659177812163871044009984, 41436018734358109309575888896000, 11319620001335483829828198596608,
    30466270240702386925738131456, 1955144726504724772083990528, 1150927953215001837767019724800, 20457489943183583590830047232, 1812085356272671739980283904, 1150927672321818141373249880064,
    1812085356272671739980283904, 1764398899528654062612381696, 66665666528136712960327286784, 1764398899528654062612381696, 20457489943183583590830047232, 66665666528136712960327286784,
    30466270240702386925738131456, 1764398899528654062612381696, 1764398899528654062612381696, 1955144726504724772083990528, 823092946414411651737167331328, 2958534301469623396468676100096,
    823296927313327399684150394880, 1427419325979351410871944347648, 1427419069431982722346408476672, 46750659517266072689249878016, 168060037793538110041507233792, 46762164427573902542068776960,
    195807273809293475898586038272, 195807320493391040439033790464, 39691452509587505063953170432, 70240479066203102908514304, 1018486946459944992173457408, 1802838962699212974651867136,
    58533732555169252423761920, 1123847665059249646536228864, 58533732555169252423761920, 1791132216188179124167114752, 1873079441765416077560381440, 1123847665059249646536228864,
    28693235698543967538128093184, 1837959202232314526106124288, 1018486946459944992173457408, 1791132216188179124167114752
  ]
def negativeScales : Array ℕ := #[
    34, 28, 33, 33, 40, 50,
    16, 57, 20, 15, 55, 15,
    16, 20, 16, 20, 20, 52,
    16, 16, 16, 55, 57, 54,
    33, 17, 36, 21, 16, 37,
    16, 17, 21, 17, 21, 21,
    33, 17, 17, 17, 35, 41,
    39, 52, 52, 35, 37, 34,
    36, 36, 9, 12, 17, 17,
    13, 12, 13, 18, 13, 12,
    22, 18, 17, 18
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34562933770815492, 28856055193818461, 33586706965286289, 33590568786740794, 40839127407892487, 50201187421666793,
    16844889621395901, 57490188691034942, 20232171452706728, 15735265128813176, 55490188769383167, 15735265128813176,
    16696790980903244, 20936486268864749, 16696790980903244, 20232171452706728, 20936486268864749, 52201195271195696,
    16696790980903244, 16696790980903244, 16844889621395901, 55158757769476819, 57030656333815386, 54158596469343168,
    33621199549246831, 17659333966696159, 36860640373962964, 21046615799550651, 16549709475496009, 37860640021861630,
    16549709475496009, 17511235327680448, 21750930607656040, 17511235327680448, 21046615799550651, 21750930607656040,
    33621199549246831, 17511235327680448, 17511235327680448, 17659333966696159, 35376970105539247, 41222725468520778,
    39377327593443544, 52171252057148793, 52171251797855926, 35238973374265197, 37084891465414709, 34239328364659680,
    36305349110616287, 36305349454581589, 9002815015607055, 12860505058921762, 17718486052046604, 17542329096782676,
    13597470650979357, 12860505058921762, 13597470650979357, 18532930398780161, 13597470650979357, 12860505058921762,
    22534697324954393, 18570163304980772, 17718486052046604, 18532930398780161
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
noncomputable def negativeCeiling : ℝ := 128102518079 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 29260351774174429040915513344, coefficient := (-29260351774174429040915513344) }, { argument := 1120386597008262901127970816, coefficient := (-1120386597008262901127970816) }, { argument := 29746507810960130193819172864, coefficient := (-29746507810960130193819172864) }, { argument := 29826240246656901283607216128, coefficient := (-29826240246656901283607216128) }, { argument := 8858539389890211970428174336, coefficient := (-8858539389890211970428174336) }, { argument := 1457347146906864317960185446400, coefficient := (-1457347146906864317960185446400) }, { argument := 1111748962130137615498739712, coefficient := (-1111748962130137615498739712) }, { argument := 56978504239717014820695415193600, coefficient := (-56978504239717014820695415193600) }, { argument := 11632690359849488708511203328, coefficient := (-11632690359849488708511203328) }, { argument := 1030401477096225107047612416, coefficient := (-1030401477096225107047612416) }, { argument := 56978507334040265973216623722496, coefficient := (-56978507334040265973216623722496) }, { argument := 1030401477096225107047612416, coefficient := (-1030401477096225107047612416) }, { argument := 1003285648751587604230569984, coefficient := (-1003285648751587604230569984) }, { argument := 37907928025803228938225319936, coefficient := (-37907928025803228938225319936) }, { argument := 1003285648751587604230569984, coefficient := (-1003285648751587604230569984) }, { argument := 11632690359849488708511203328, coefficient := (-11632690359849488708511203328) }, { argument := 37907928025803228938225319936, coefficient := (-37907928025803228938225319936) }, { argument := 1457355076177671897126814089216, coefficient := (-1457355076177671897126814089216) }, { argument := 1003285648751587604230569984, coefficient := (-1003285648751587604230569984) }, { argument := 1003285648751587604230569984, coefficient := (-1003285648751587604230569984) }, { argument := 1111748962130137615498739712, coefficient := (-1111748962130137615498739712) }, { argument := 11320885659177812163871044009984, coefficient := (-11320885659177812163871044009984) }, { argument := 41436018734358109309575888896000, coefficient := (-41436018734358109309575888896000) }, { argument := 11319620001335483829828198596608, coefficient := (-11319620001335483829828198596608) }, { argument := 30466270240702386925738131456, coefficient := (-30466270240702386925738131456) }, { argument := 1955144726504724772083990528, coefficient := (-1955144726504724772083990528) }, { argument := 1150927953215001837767019724800, coefficient := (-1150927953215001837767019724800) }, { argument := 20457489943183583590830047232, coefficient := (-20457489943183583590830047232) }, { argument := 1812085356272671739980283904, coefficient := (-1812085356272671739980283904) }, { argument := 1150927672321818141373249880064, coefficient := (-1150927672321818141373249880064) }, { argument := 1812085356272671739980283904, coefficient := (-1812085356272671739980283904) }, { argument := 1764398899528654062612381696, coefficient := (-1764398899528654062612381696) }, { argument := 66665666528136712960327286784, coefficient := (-66665666528136712960327286784) }, { argument := 1764398899528654062612381696, coefficient := (-1764398899528654062612381696) }, { argument := 20457489943183583590830047232, coefficient := (-20457489943183583590830047232) }, { argument := 66665666528136712960327286784, coefficient := (-66665666528136712960327286784) }, { argument := 30466270240702386925738131456, coefficient := (-30466270240702386925738131456) }, { argument := 1764398899528654062612381696, coefficient := (-1764398899528654062612381696) }, { argument := 1764398899528654062612381696, coefficient := (-1764398899528654062612381696) }, { argument := 1955144726504724772083990528, coefficient := (-1955144726504724772083990528) }, { argument := 823092946414411651737167331328, coefficient := (-823092946414411651737167331328) }, { argument := 2958534301469623396468676100096, coefficient := (-2958534301469623396468676100096) }, { argument := 823296927313327399684150394880, coefficient := (-823296927313327399684150394880) }, { argument := 1427419325979351410871944347648, coefficient := (-1427419325979351410871944347648) }, { argument := 1427419069431982722346408476672, coefficient := (-1427419069431982722346408476672) }, { argument := 46750659517266072689249878016, coefficient := (-46750659517266072689249878016) }, { argument := 168060037793538110041507233792, coefficient := (-168060037793538110041507233792) }, { argument := 46762164427573902542068776960, coefficient := (-46762164427573902542068776960) }, { argument := 195807273809293475898586038272, coefficient := (-195807273809293475898586038272) }, { argument := 195807320493391040439033790464, coefficient := (-195807320493391040439033790464) }, { argument := 39691452509587505063953170432, coefficient := (-39691452509587505063953170432) }, { argument := 70240479066203102908514304, coefficient := (-70240479066203102908514304) }, { argument := 1018486946459944992173457408, coefficient := (-1018486946459944992173457408) }, { argument := 1802838962699212974651867136, coefficient := (-1802838962699212974651867136) }, { argument := 58533732555169252423761920, coefficient := (-58533732555169252423761920) }, { argument := 1123847665059249646536228864, coefficient := (-1123847665059249646536228864) }, { argument := 58533732555169252423761920, coefficient := (-58533732555169252423761920) }, { argument := 1791132216188179124167114752, coefficient := (-1791132216188179124167114752) }, { argument := 1873079441765416077560381440, coefficient := (-1873079441765416077560381440) }, { argument := 1123847665059249646536228864, coefficient := (-1123847665059249646536228864) }, { argument := 28693235698543967538128093184, coefficient := (-28693235698543967538128093184) }, { argument := 1837959202232314526106124288, coefficient := (-1837959202232314526106124288) }, { argument := 1018486946459944992173457408, coefficient := (-1018486946459944992173457408) }, { argument := 1791132216188179124167114752, coefficient := (-1791132216188179124167114752) }] }

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

end TermShard8


end Parent2

namespace Parent2

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-186268143290840032109769277833216)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    12395, 389203, 12395, 379287, 12395, 7437,
    497803653, 6765, 4737751521, 70785, 3135, 9475500729,
    3135, 6105, 115335, 6105, 70785, 115335,
    497803653, 6105, 6105, 6765, 7437, 215673,
    190883, 12395, 7437, 12395, 379287, 12395,
    7437, 6076029, 389203, 215673, 379287, 12395,
    389203, 12395, 379287, 12395, 7437, 25990732077,
    212421, 244844023401, 2222649, 98439, 489687927297, 98439,
    191697, 3621519, 191697, 2222649, 3621519, 25990732077,
    191697, 191697, 212421, 20739007357, 18637021701, 20744131695,
    497803653, 6765, 4737751521, 70785
  ]
def negativeCoefficients : Array ℕ := #[
    58533732555169252423761920, 1837959202232314526106124288, 58533732555169252423761920, 1791132216188179124167114752, 1873079441765416077560381440, 70240479066203102908514304,
    1147857073231089506929606656, 63893618513226299741306880, 43698044896357582140466003968, 668545422979855672902942720, 59218475695185350979747840, 43698034229527821517917782016,
    59218475695185350979747840, 57660094755838368059228160, 2178616553207082122886512640, 57660094755838368059228160, 668545422979855672902942720, 2178616553207082122886512640,
    1147857073231089506929606656, 57660094755838368059228160, 57660094755838368059228160, 63893618513226299741306880, 70240479066203102908514304, 1018486946459944992173457408,
    1802838962699212974651867136, 58533732555169252423761920, 1123847665059249646536228864, 58533732555169252423761920, 1791132216188179124167114752, 1873079441765416077560381440,
    1123847665059249646536228864, 28693235698543967538128093184, 1837959202232314526106124288, 1018486946459944992173457408, 1791132216188179124167114752, 58533732555169252423761920,
    1837959202232314526106124288, 58533732555169252423761920, 1791132216188179124167114752, 1873079441765416077560381440, 70240479066203102908514304, 29965273932048280972953649152,
    2006259621315305811877036032, 1129143759413899881186280341504, 20992326281567468129152401408, 1859460136828820020764082176, 1129143483854131065103784607744, 1859460136828820020764082176,
    1810526975333324757059764224, 68408559770702378658636496896, 1810526975333324757059764224, 20992326281567468129152401408, 68408559770702378658636496896, 29965273932048280972953649152,
    1810526975333324757059764224, 1810526975333324757059764224, 2006259621315305811877036032, 47820895132169817655674404864, 171896184807259028519185809408, 47832711051123965737713008640,
    1147857073231089506929606656, 63893618513226299741306880, 43698044896357582140466003968, 668545422979855672902942720
  ]
def negativeScales : Array ℕ := #[
    13, 18, 13, 18, 13, 12,
    28, 12, 32, 16, 11, 33,
    11, 12, 16, 12, 16, 16,
    28, 12, 12, 12, 12, 17,
    17, 13, 12, 13, 18, 13,
    12, 22, 18, 17, 18, 13,
    18, 13, 18, 13, 12, 34,
    17, 37, 21, 16, 38, 16,
    17, 21, 17, 21, 21, 34,
    17, 17, 17, 34, 34, 34,
    28, 12, 32, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    13597470650979357, 18570163304980772, 13597470650979357, 18532930398780161, 13597470650979357, 12860505058921762,
    28891001580004972, 12723874218989575, 32141555390086268, 16111156051745362, 11614249727697750, 33141555037919843,
    11614249727697750, 12575775579877617, 16815470860503971, 12575775579877617, 16111156051745362, 16815470860503971,
    28891001580004972, 12575775579877617, 12575775579877617, 12723874218989575, 12860505058921762, 17718486052046604,
    17542329096782676, 13597470650979357, 12860505058921762, 13597470650979357, 18532930398780161, 13597470650979357,
    12860505058921762, 22534697324954393, 18570163304980772, 17718486052046604, 18532930398780161, 13597470650979357,
    18570163304980772, 13597470650979357, 18532930398780161, 13597470650979357, 12860505058921762, 34597278219433225,
    17696566872934922, 37833072025557896, 21083848705749627, 16586942381697590, 38833071673478042, 16586942381697590,
    17548468233880300, 21788163514132048, 17548468233880300, 21083848705749627, 21788163514132048, 34597278219433225,
    17548468233880300, 17548468233880300, 17696566872934922, 34271627792137338, 34117452276649956, 34271984219217207,
    28891001580004972, 12723874218989575, 32141555390086268, 16111156051745362
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
noncomputable def negativeCeiling : ℝ := 129327053 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 58533732555169252423761920, coefficient := (-58533732555169252423761920) }, { argument := 1837959202232314526106124288, coefficient := (-1837959202232314526106124288) }, { argument := 58533732555169252423761920, coefficient := (-58533732555169252423761920) }, { argument := 1791132216188179124167114752, coefficient := (-1791132216188179124167114752) }, { argument := 1873079441765416077560381440, coefficient := (-1873079441765416077560381440) }, { argument := 70240479066203102908514304, coefficient := (-70240479066203102908514304) }, { argument := 1147857073231089506929606656, coefficient := (-1147857073231089506929606656) }, { argument := 63893618513226299741306880, coefficient := (-63893618513226299741306880) }, { argument := 43698044896357582140466003968, coefficient := (-43698044896357582140466003968) }, { argument := 668545422979855672902942720, coefficient := (-668545422979855672902942720) }, { argument := 59218475695185350979747840, coefficient := (-59218475695185350979747840) }, { argument := 43698034229527821517917782016, coefficient := (-43698034229527821517917782016) }, { argument := 59218475695185350979747840, coefficient := (-59218475695185350979747840) }, { argument := 57660094755838368059228160, coefficient := (-57660094755838368059228160) }, { argument := 2178616553207082122886512640, coefficient := (-2178616553207082122886512640) }, { argument := 57660094755838368059228160, coefficient := (-57660094755838368059228160) }, { argument := 668545422979855672902942720, coefficient := (-668545422979855672902942720) }, { argument := 2178616553207082122886512640, coefficient := (-2178616553207082122886512640) }, { argument := 1147857073231089506929606656, coefficient := (-1147857073231089506929606656) }, { argument := 57660094755838368059228160, coefficient := (-57660094755838368059228160) }, { argument := 57660094755838368059228160, coefficient := (-57660094755838368059228160) }, { argument := 63893618513226299741306880, coefficient := (-63893618513226299741306880) }, { argument := 70240479066203102908514304, coefficient := (-70240479066203102908514304) }, { argument := 1018486946459944992173457408, coefficient := (-1018486946459944992173457408) }, { argument := 1802838962699212974651867136, coefficient := (-1802838962699212974651867136) }, { argument := 58533732555169252423761920, coefficient := (-58533732555169252423761920) }, { argument := 1123847665059249646536228864, coefficient := (-1123847665059249646536228864) }, { argument := 58533732555169252423761920, coefficient := (-58533732555169252423761920) }, { argument := 1791132216188179124167114752, coefficient := (-1791132216188179124167114752) }, { argument := 1873079441765416077560381440, coefficient := (-1873079441765416077560381440) }, { argument := 1123847665059249646536228864, coefficient := (-1123847665059249646536228864) }, { argument := 28693235698543967538128093184, coefficient := (-28693235698543967538128093184) }, { argument := 1837959202232314526106124288, coefficient := (-1837959202232314526106124288) }, { argument := 1018486946459944992173457408, coefficient := (-1018486946459944992173457408) }, { argument := 1791132216188179124167114752, coefficient := (-1791132216188179124167114752) }, { argument := 58533732555169252423761920, coefficient := (-58533732555169252423761920) }, { argument := 1837959202232314526106124288, coefficient := (-1837959202232314526106124288) }, { argument := 58533732555169252423761920, coefficient := (-58533732555169252423761920) }, { argument := 1791132216188179124167114752, coefficient := (-1791132216188179124167114752) }, { argument := 1873079441765416077560381440, coefficient := (-1873079441765416077560381440) }, { argument := 70240479066203102908514304, coefficient := (-70240479066203102908514304) }, { argument := 29965273932048280972953649152, coefficient := (-29965273932048280972953649152) }, { argument := 2006259621315305811877036032, coefficient := (-2006259621315305811877036032) }, { argument := 1129143759413899881186280341504, coefficient := (-1129143759413899881186280341504) }, { argument := 20992326281567468129152401408, coefficient := (-20992326281567468129152401408) }, { argument := 1859460136828820020764082176, coefficient := (-1859460136828820020764082176) }, { argument := 1129143483854131065103784607744, coefficient := (-1129143483854131065103784607744) }, { argument := 1859460136828820020764082176, coefficient := (-1859460136828820020764082176) }, { argument := 1810526975333324757059764224, coefficient := (-1810526975333324757059764224) }, { argument := 68408559770702378658636496896, coefficient := (-68408559770702378658636496896) }, { argument := 1810526975333324757059764224, coefficient := (-1810526975333324757059764224) }, { argument := 20992326281567468129152401408, coefficient := (-20992326281567468129152401408) }, { argument := 68408559770702378658636496896, coefficient := (-68408559770702378658636496896) }, { argument := 29965273932048280972953649152, coefficient := (-29965273932048280972953649152) }, { argument := 1810526975333324757059764224, coefficient := (-1810526975333324757059764224) }, { argument := 1810526975333324757059764224, coefficient := (-1810526975333324757059764224) }, { argument := 2006259621315305811877036032, coefficient := (-2006259621315305811877036032) }, { argument := 47820895132169817655674404864, coefficient := (-47820895132169817655674404864) }, { argument := 171896184807259028519185809408, coefficient := (-171896184807259028519185809408) }, { argument := 47832711051123965737713008640, coefficient := (-47832711051123965737713008640) }, { argument := 1147857073231089506929606656, coefficient := (-1147857073231089506929606656) }, { argument := 63893618513226299741306880, coefficient := (-63893618513226299741306880) }, { argument := 43698044896357582140466003968, coefficient := (-43698044896357582140466003968) }, { argument := 668545422979855672902942720, coefficient := (-668545422979855672902942720) }] }

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

end TermShard9


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
