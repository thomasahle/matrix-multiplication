import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 1,
parent chunk 15, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-163371649572519561177774482566152192)
def positiveArguments : Array ℕ := #[
    4557, 681, 10215, 17933, 681, 5675,
    681, 17933, 35639, 5675, 550021, 35185,
    10215, 17933, 681, 35185, 681, 17933,
    17933, 681, 7083, 32267, 787, 337623,
    14953, 787, 14953, 29119, 550113, 29119,
    337623, 550113, 7083, 29119, 29119, 32267,
    7, 35, 29, 521, 195, 7,
    781, 781, 559, 29, 11, 11500781733,
    11500781403, 65908345077, 30029831735, 65904543059, 12644248063, 123647421137,
    247294841487, 12644304287
  ]
def positiveCoefficients : Array ℕ := #[
    352580797438967369544706818048, 210759291688335991801575899136, 3161389375325039877023638487040, 5549994681126181117441498677248, 210759291688335991801575899136, 3512654861472266530026264985600,
    210759291688335991801575899136, 5549994681126181117441498677248, 5514868132511458452141236027392, 3512654861472266530026264985600, 85111627293473018022536400601088, 5444615035282013121540710727680,
    3161389375325039877023638487040, 5549994681126181117441498677248, 210759291688335991801575899136, 5444615035282013121540710727680, 210759291688335991801575899136, 5549994681126181117441498677248,
    5549994681126181117441498677248, 210759291688335991801575899136, 548020581141146780444406054912, 624134550744083833283906895872, 487129405458797138172805382144, 6530578591931999133629172154368,
    578466168982321601580206391296, 487129405458797138172805382144, 578466168982321601580206391296, 563243375061734191012306223104, 21281465900981199973924435132416, 563243375061734191012306223104,
    6530578591931999133629172154368, 21281465900981199973924435132416, 548020581141146780444406054912, 563243375061734191012306223104, 563243375061734191012306223104, 624134550744083833283906895872,
    8665580274997661924293869568, 173311605499953238485877391360, 8975065284819006993018650624, 161241690116920780805610930176, 241398307660649153605329223680, 8665580274997661924293869568,
    241707792670470498674054004736, 241707792670470498674054004736, 173002120490131893417152610304, 8975065284819006993018650624, 1743019575313815427057966907392, 54310906182718673093865838215168,
    54310904624337733746882917695488, 311243359733031385952837374574592, 1134494966972633645651511979540480, 311225405210660918870081288536064, 59710773253800634174772869070848, 2335633749082546072046582689169408,
    2335633741649541228009761122811904, 59711038764133767037705363914752
  ]
def positiveScales : Array ℕ := #[
    12, 9, 13, 14, 9, 12,
    9, 14, 15, 12, 19, 15,
    13, 14, 9, 15, 9, 14,
    14, 9, 12, 14, 9, 18,
    13, 9, 13, 14, 19, 14,
    18, 19, 12, 14, 14, 14,
    2, 5, 4, 9, 7, 2,
    9, 9, 9, 4, 3, 33,
    33, 35, 34, 35, 33, 36,
    37, 33
  ]
def negativeArguments : Array ℕ := #[
    93, 227, 787, 1, 11, 1371,
    693, 60467
  ]
def negativeCoefficients : Array ℕ := #[
    29472876455306333584798349524992, 143878343125904037069875813810176, 62352563898726033686119088914432, 1267650600228229401496703205376, 1743019575313815427057966907392, 108621810807056406840748755910656,
    1756963731916325950474430642651136, 4790689302750021701268822044966912
  ]
def negativeScales : Array ℕ := #[
    6, 7, 9, 0, 3, 10,
    9, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12153868655223239, 9411510988012070, 13318401583620589, 14130329235468017, 9411510988012070, 12470404677065633,
    9411510988012070, 14130329235468017, 15121169236182541, 12470404677065633, 19069127176742261, 15102672892565152,
    13318401583620589, 14130329235468017, 9411510988012070, 15102672892565152, 9411510988012070, 14130329235468017,
    14130329235468017, 9411510988012070, 12790144826917094, 14977771829105505, 9620219825506876, 18365053663007031,
    13868147338800169, 9620219825506876, 13868147338800169, 14829673191064051, 19069368470882922, 14829673191064051,
    18365053663007031, 19069368470882922, 12790144826917094, 14829673191064051, 14829673191064051, 14977771829105505,
    2807354922011143, 5129283016944966, 4857980995002857, 9025139562278508, 7607330313749179, 2807354922011143,
    9609178738141526, 9609178738141526, 9126704472843189, 4857980995002857, 3459431618637292, 33421012876477355,
    33421012835081093, 35939742093975611, 34805677339948842, 35939658867630411, 33557762193226459, 36847441194008187,
    37847441189416903, 33557768608309842
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6539158811108986, 7826548488390402, 9620219825517287, 0, 3459431618637364, 10421012855779242,
    9436711542137242, 15883860385935856
  ]

abbrev PositiveTerm := Fin 56
abbrev NegativeTerm := Fin 8
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
noncomputable def positiveFloor : ℝ := 2979973080629 / 1000000000000
noncomputable def negativeCeiling : ℝ := 230464536547 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 352580797438967369544706818048, coefficient := 352580797438967369544706818048 }, { argument := 29472876455306333584798349524992, coefficient := (-29472876455306333584798349524992) }, { argument := 210759291688335991801575899136, coefficient := 210759291688335991801575899136 }, { argument := 3161389375325039877023638487040, coefficient := 3161389375325039877023638487040 }, { argument := 5549994681126181117441498677248, coefficient := 5549994681126181117441498677248 }, { argument := 210759291688335991801575899136, coefficient := 210759291688335991801575899136 }, { argument := 3512654861472266530026264985600, coefficient := 3512654861472266530026264985600 }, { argument := 210759291688335991801575899136, coefficient := 210759291688335991801575899136 }, { argument := 5549994681126181117441498677248, coefficient := 5549994681126181117441498677248 }, { argument := 5514868132511458452141236027392, coefficient := 5514868132511458452141236027392 }, { argument := 3512654861472266530026264985600, coefficient := 3512654861472266530026264985600 }, { argument := 85111627293473018022536400601088, coefficient := 85111627293473018022536400601088 }, { argument := 5444615035282013121540710727680, coefficient := 5444615035282013121540710727680 }, { argument := 3161389375325039877023638487040, coefficient := 3161389375325039877023638487040 }, { argument := 5549994681126181117441498677248, coefficient := 5549994681126181117441498677248 }, { argument := 210759291688335991801575899136, coefficient := 210759291688335991801575899136 }, { argument := 5444615035282013121540710727680, coefficient := 5444615035282013121540710727680 }, { argument := 210759291688335991801575899136, coefficient := 210759291688335991801575899136 }, { argument := 5549994681126181117441498677248, coefficient := 5549994681126181117441498677248 }, { argument := 5549994681126181117441498677248, coefficient := 5549994681126181117441498677248 }, { argument := 210759291688335991801575899136, coefficient := 210759291688335991801575899136 }, { argument := 143878343125904037069875813810176, coefficient := (-143878343125904037069875813810176) }, { argument := 548020581141146780444406054912, coefficient := 548020581141146780444406054912 }, { argument := 624134550744083833283906895872, coefficient := 624134550744083833283906895872 }, { argument := 487129405458797138172805382144, coefficient := 487129405458797138172805382144 }, { argument := 6530578591931999133629172154368, coefficient := 6530578591931999133629172154368 }, { argument := 578466168982321601580206391296, coefficient := 578466168982321601580206391296 }, { argument := 487129405458797138172805382144, coefficient := 487129405458797138172805382144 }, { argument := 578466168982321601580206391296, coefficient := 578466168982321601580206391296 }, { argument := 563243375061734191012306223104, coefficient := 563243375061734191012306223104 }, { argument := 21281465900981199973924435132416, coefficient := 21281465900981199973924435132416 }, { argument := 563243375061734191012306223104, coefficient := 563243375061734191012306223104 }, { argument := 6530578591931999133629172154368, coefficient := 6530578591931999133629172154368 }, { argument := 21281465900981199973924435132416, coefficient := 21281465900981199973924435132416 }, { argument := 548020581141146780444406054912, coefficient := 548020581141146780444406054912 }, { argument := 563243375061734191012306223104, coefficient := 563243375061734191012306223104 }, { argument := 563243375061734191012306223104, coefficient := 563243375061734191012306223104 }, { argument := 624134550744083833283906895872, coefficient := 624134550744083833283906895872 }, { argument := 62352563898726033686119088914432, coefficient := (-62352563898726033686119088914432) }, { argument := 8665580274997661924293869568, coefficient := 8665580274997661924293869568 }, { argument := 173311605499953238485877391360, coefficient := 173311605499953238485877391360 }, { argument := 8975065284819006993018650624, coefficient := 8975065284819006993018650624 }, { argument := 161241690116920780805610930176, coefficient := 161241690116920780805610930176 }, { argument := 241398307660649153605329223680, coefficient := 241398307660649153605329223680 }, { argument := 8665580274997661924293869568, coefficient := 8665580274997661924293869568 }, { argument := 241707792670470498674054004736, coefficient := 241707792670470498674054004736 }, { argument := 241707792670470498674054004736, coefficient := 241707792670470498674054004736 }, { argument := 173002120490131893417152610304, coefficient := 173002120490131893417152610304 }, { argument := 8975065284819006993018650624, coefficient := 8975065284819006993018650624 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 1743019575313815427057966907392, coefficient := 1743019575313815427057966907392 }, { argument := 1743019575313815427057966907392, coefficient := (-1743019575313815427057966907392) }, { argument := 54310906182718673093865838215168, coefficient := 54310906182718673093865838215168 }, { argument := 54310904624337733746882917695488, coefficient := 54310904624337733746882917695488 }, { argument := 108621810807056406840748755910656, coefficient := (-108621810807056406840748755910656) }, { argument := 311243359733031385952837374574592, coefficient := 311243359733031385952837374574592 }, { argument := 1134494966972633645651511979540480, coefficient := 1134494966972633645651511979540480 }, { argument := 311225405210660918870081288536064, coefficient := 311225405210660918870081288536064 }, { argument := 1756963731916325950474430642651136, coefficient := (-1756963731916325950474430642651136) }, { argument := 59710773253800634174772869070848, coefficient := 59710773253800634174772869070848 }, { argument := 2335633749082546072046582689169408, coefficient := 2335633749082546072046582689169408 }, { argument := 2335633741649541228009761122811904, coefficient := 2335633741649541228009761122811904 }, { argument := 59711038764133767037705363914752, coefficient := 59711038764133767037705363914752 }, { argument := 4790689302750021701268822044966912, coefficient := (-4790689302750021701268822044966912) }] }

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

end TermShard10


end Parent3

namespace Parent3

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-42031516994164066414795690988273664)
def positiveArguments : Array ℕ := #[
    80581237, 7052766163, 71209903385, 7052778655, 80581237, 45976029,
    8283911715, 258872265, 1436727, 1066269, 48193419, 133995
  ]
def positiveCoefficients : Array ℕ := #[
    761068265513950642141506043904, 133222986158673411611880211873792, 1345117043974838772866079355043840, 133223222125881827642312249835520, 761068265513950642141506043904, 217115658365042811564598493184,
    39119667029967200803629972848640, 39119670642577560198908561326080, 217112045754683416286010015744, 10070625974645867464724840448, 455173973160986268329991733248, 10124375949953889766547128320
  ]
def positiveScales : Array ℕ := #[
    26, 32, 36, 32, 26, 25,
    32, 27, 20, 20, 25, 17
  ]
def negativeArguments : Array ℕ := #[
    2545, 993, 3
  ]
def negativeCoefficients : Array ℕ := #[
    1613085388790421913404554828840960, 78673565376664487230389142683648, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    11, 9, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    26263940616633611, 32715542061411626, 36051358844150594, 32715544616739574, 26263940616633611, 25454378528497122,
    32947665031623026, 27947665164852553, 20454354523142324, 20024140018686312, 25522332818461723, 17031819642210997
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    11313449940963058, 9955649918992299, 1584962500724866
  ]

abbrev PositiveTerm := Fin 12
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
noncomputable def positiveFloor : ℝ := 179515842199 / 250000000000
noncomputable def negativeCeiling : ℝ := 229108153289 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 761068265513950642141506043904, coefficient := 761068265513950642141506043904 }, { argument := 133222986158673411611880211873792, coefficient := 133222986158673411611880211873792 }, { argument := 1345117043974838772866079355043840, coefficient := 1345117043974838772866079355043840 }, { argument := 133223222125881827642312249835520, coefficient := 133223222125881827642312249835520 }, { argument := 761068265513950642141506043904, coefficient := 761068265513950642141506043904 }, { argument := 1613085388790421913404554828840960, coefficient := (-1613085388790421913404554828840960) }, { argument := 217115658365042811564598493184, coefficient := 217115658365042811564598493184 }, { argument := 39119667029967200803629972848640, coefficient := 39119667029967200803629972848640 }, { argument := 39119670642577560198908561326080, coefficient := 39119670642577560198908561326080 }, { argument := 217112045754683416286010015744, coefficient := 217112045754683416286010015744 }, { argument := 78673565376664487230389142683648, coefficient := (-78673565376664487230389142683648) }, { argument := 10070625974645867464724840448, coefficient := 10070625974645867464724840448 }, { argument := 455173973160986268329991733248, coefficient := 455173973160986268329991733248 }, { argument := 10124375949953889766547128320, coefficient := 10124375949953889766547128320 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end TermShard11


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15
