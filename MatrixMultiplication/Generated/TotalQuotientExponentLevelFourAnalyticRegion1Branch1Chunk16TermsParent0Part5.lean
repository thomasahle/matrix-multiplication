import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 1,
parent chunk 16, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 206292494270785134830994199020568576
def positiveArguments : Array ℕ := #[
    6651, 141, 105, 111, 9, 1929,
    3489, 105, 1929, 57, 57, 111,
    111, 3489, 111, 141, 9, 31,
    95, 281, 627, 31, 313, 637,
    31, 95, 31, 1, 1, 1,
    1, 1643, 39803, 30157, 16801, 1643,
    16801, 33549, 1643, 39803, 1643, 2865,
    8595, 18145, 46795, 39155, 1095385, 33425,
    39155, 35335, 18145, 18145, 35335, 1095385,
    35335, 2865, 46795, 11151, 167265
  ]
def positiveCoefficients : Array ℕ := #[
    2107786035529488437338643254738944, 5454673298101206836274266112, 4061990753905154027012751360, 4294104511271162828556337152, 5570730176784211237046059008, 74624572993171829696262832128,
    134974149908334118097595138048, 4061990753905154027012751360, 74624572993171829696262832128, 4410161389954167229328130048, 4410161389954167229328130048, 4294104511271162828556337152,
    4294104511271162828556337152, 134974149908334118097595138048, 4294104511271162828556337152, 5454673298101206836274266112, 5570730176784211237046059008, 1199254413057712141308526592,
    29401075933027781528854200320, 21741321939949491077915869184, 24255887644747919761304715264, 1199254413057712141308526592, 24217202018520251627714117632, 24642743907024601097210691584,
    1199254413057712141308526592, 29401075933027781528854200320, 1199254413057712141308526592, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168,
    39614081257132168796771975168, 31780241946029371744675954688, 769901990369937360653278773248, 583321215073893952345826394112, 649957206251052312455630815232, 31780241946029371744675954688,
    649957206251052312455630815232, 648932037156019106915479977984, 31780241946029371744675954688, 769901990369937360653278773248, 31780241946029371744675954688, 886674553138153621896497725440,
    665005914853615216422373294080, 701950687901038284001394032640, 905146939661865155686008094720, 12117885559554766165918802247680, 21187827342697129256568393564160, 646533528329903682632862924800,
    12117885559554766165918802247680, 683478301377326750211883663360, 701950687901038284001394032640, 701950687901038284001394032640, 683478301377326750211883663360, 21187827342697129256568393564160,
    683478301377326750211883663360, 886674553138153621896497725440, 905146939661865155686008094720, 431383418064727357668754194432, 6470751270970910365031312916480
  ]
def positiveScales : Array ℕ := #[
    12, 7, 6, 6, 3, 10,
    11, 6, 10, 5, 5, 6,
    6, 11, 6, 7, 3, 4,
    6, 8, 9, 4, 8, 9,
    4, 6, 4, 0, 0, 0,
    0, 10, 15, 14, 14, 10,
    14, 15, 10, 15, 10, 11,
    13, 14, 15, 15, 20, 15,
    15, 15, 14, 14, 15, 20,
    15, 11, 15, 13, 17
  ]
def negativeArguments : Array ℕ := #[
    3, 1, 1, 53, 955
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 158456325028528675187087900672, 158456325028528675187087900672, 4199092613256009892457829367808, 75662895201122442401834472570880
  ]
def negativeScales : Array ℕ := #[
    1, 0, 0, 5, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12699355555584036, 7139551352398793, 6714245517659862, 6794415866314396, 3169925001442312, 10913637427705176,
    11768597882173550, 6714245517659862, 10913637427705176, 5832890014087662, 5832890014087662, 6794415866314396,
    6794415866314396, 11768597882173550, 6794415866314396, 7139551352398793, 3169925001442312, 4954196309696329,
    6569855608330797, 8134426320220925, 9292321632802038, 4954196309696329, 8290018846932618, 9315149562256300,
    4954196309696329, 6569855608330797, 4954196309696329, 0, 0, 0,
    0, 10682116764947138, 15280589552077470, 14880205296681195, 14036259484702606, 10682116764947138,
    14036259484702606, 15033982143991540, 10682116764947138, 15280589552077470, 10682116764947138, 11484319423644256,
    13069281924365423, 14147284436366696, 15514066767038291, 15256908927541194, 20063006598938935, 15028639939868077,
    15256908927541194, 15108810288552060, 14147284436366696, 14147284436366696, 15108810288552060, 20063006598938935,
    15108810288552060, 11484319423644256, 15514066767038291, 13444885473582911, 17351776069191432
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 0, 0, 5727920454700926, 9899356927240640
  ]

abbrev PositiveTerm := Fin 59
abbrev NegativeTerm := Fin 5
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
noncomputable def positiveFloor : ℝ := 340662491999 / 1000000000000
noncomputable def negativeCeiling : ℝ := 2328628403 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2107786035529488437338643254738944, coefficient := 2107786035529488437338643254738944 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 1199254413057712141308526592, coefficient := 1199254413057712141308526592 }, { argument := 29401075933027781528854200320, coefficient := 29401075933027781528854200320 }, { argument := 21741321939949491077915869184, coefficient := 21741321939949491077915869184 }, { argument := 24255887644747919761304715264, coefficient := 24255887644747919761304715264 }, { argument := 1199254413057712141308526592, coefficient := 1199254413057712141308526592 }, { argument := 24217202018520251627714117632, coefficient := 24217202018520251627714117632 }, { argument := 24642743907024601097210691584, coefficient := 24642743907024601097210691584 }, { argument := 1199254413057712141308526592, coefficient := 1199254413057712141308526592 }, { argument := 29401075933027781528854200320, coefficient := 29401075933027781528854200320 }, { argument := 1199254413057712141308526592, coefficient := 1199254413057712141308526592 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 31780241946029371744675954688, coefficient := 31780241946029371744675954688 }, { argument := 769901990369937360653278773248, coefficient := 769901990369937360653278773248 }, { argument := 583321215073893952345826394112, coefficient := 583321215073893952345826394112 }, { argument := 649957206251052312455630815232, coefficient := 649957206251052312455630815232 }, { argument := 31780241946029371744675954688, coefficient := 31780241946029371744675954688 }, { argument := 649957206251052312455630815232, coefficient := 649957206251052312455630815232 }, { argument := 648932037156019106915479977984, coefficient := 648932037156019106915479977984 }, { argument := 31780241946029371744675954688, coefficient := 31780241946029371744675954688 }, { argument := 769901990369937360653278773248, coefficient := 769901990369937360653278773248 }, { argument := 31780241946029371744675954688, coefficient := 31780241946029371744675954688 }, { argument := 4199092613256009892457829367808, coefficient := (-4199092613256009892457829367808) }, { argument := 886674553138153621896497725440, coefficient := 886674553138153621896497725440 }, { argument := 665005914853615216422373294080, coefficient := 665005914853615216422373294080 }, { argument := 701950687901038284001394032640, coefficient := 701950687901038284001394032640 }, { argument := 905146939661865155686008094720, coefficient := 905146939661865155686008094720 }, { argument := 12117885559554766165918802247680, coefficient := 12117885559554766165918802247680 }, { argument := 21187827342697129256568393564160, coefficient := 21187827342697129256568393564160 }, { argument := 646533528329903682632862924800, coefficient := 646533528329903682632862924800 }, { argument := 12117885559554766165918802247680, coefficient := 12117885559554766165918802247680 }, { argument := 683478301377326750211883663360, coefficient := 683478301377326750211883663360 }, { argument := 701950687901038284001394032640, coefficient := 701950687901038284001394032640 }, { argument := 701950687901038284001394032640, coefficient := 701950687901038284001394032640 }, { argument := 683478301377326750211883663360, coefficient := 683478301377326750211883663360 }, { argument := 21187827342697129256568393564160, coefficient := 21187827342697129256568393564160 }, { argument := 683478301377326750211883663360, coefficient := 683478301377326750211883663360 }, { argument := 886674553138153621896497725440, coefficient := 886674553138153621896497725440 }, { argument := 905146939661865155686008094720, coefficient := 905146939661865155686008094720 }, { argument := 75662895201122442401834472570880, coefficient := (-75662895201122442401834472570880) }, { argument := 431383418064727357668754194432, coefficient := 431383418064727357668754194432 }, { argument := 6470751270970910365031312916480, coefficient := 6470751270970910365031312916480 }] }

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


end Parent0

namespace Parent0

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 64104771052654383921399937061879808
def positiveArguments : Array ℕ := #[
    293643, 11151, 92925, 11151, 293643, 583569,
    92925, 9006291, 576135, 167265, 293643, 11151,
    576135, 11151, 293643, 293643, 11151, 6669,
    30381, 741, 317889, 14079, 741, 14079,
    27417, 517959, 27417, 317889, 517959, 6669,
    27417, 27417, 30381, 21, 105, 87,
    1563, 585, 21, 2343, 2343, 1677,
    87, 1, 150994953, 150994935, 3830818889, 27928976345,
    7661048725, 2427763131, 189802119309, 94901053107, 4855545495, 90082947,
    3545800707, 141146557815, 14183224695
  ]
def positiveCoefficients : Array ℕ := #[
    11359763342371153751943860453376, 431383418064727357668754194432, 7189723634412122627812569907200, 431383418064727357668754194432, 11359763342371153751943860453376, 11287866106027032525665734754304,
    7189723634412122627812569907200, 174207003661805731271898568851456, 11144071633338790073109483356160, 6470751270970910365031312916480, 11359763342371153751943860453376, 431383418064727357668754194432,
    11144071633338790073109483356160, 431383418064727357668754194432, 11359763342371153751943860453376, 11359763342371153751943860453376, 431383418064727357668754194432, 515988882624637565831391215616,
    587654005211392783307973328896, 458656784555233391850125524992, 6148867517943597659490745319424, 544654931659339652822024060928, 458656784555233391850125524992, 544654931659339652822024060928,
    530321907141988609326707638272, 20037568275256758806452358873088, 530321907141988609326707638272, 6148867517943597659490745319424, 20037568275256758806452358873088, 515988882624637565831391215616,
    530321907141988609326707638272, 530321907141988609326707638272, 587654005211392783307973328896, 3249592603124123221610201088, 64991852062482464432204021760, 3365649481807127622381993984,
    60465633793845292802104098816, 90524365372743432601998458880, 3249592603124123221610201088, 90640422251426437002770251776, 90640422251426437002770251776, 64875795183799460031432228864,
    3365649481807127622381993984, 158456325028528675187087900672, 2852214020518709536674809905152, 2852213680508322770060354519040, 36181061446715063618710156607488, 131890861792487168891858054021120,
    36178279722571229805588093337600, 22929574476362135457723530084352, 896315166602447105544428992856064, 896315104763058012366424919506944, 22929665301636700489609925099520, 850809379181845315388360884224,
    133956563309378331100499543064576, 1333091547595957170526960987668480, 133956769837354092921563318845440
  ]
def positiveScales : Array ℕ := #[
    18, 13, 16, 13, 18, 19,
    16, 23, 19, 17, 18, 13,
    19, 13, 18, 18, 13, 12,
    14, 9, 18, 13, 9, 13,
    14, 18, 14, 18, 18, 12,
    14, 14, 14, 4, 6, 6,
    10, 9, 4, 11, 11, 10,
    6, 0, 27, 27, 31, 34,
    32, 31, 37, 36, 32, 26,
    31, 37, 33
  ]
def negativeArguments : Array ℕ := #[
    3717, 741, 3, 1, 9, 1289,
    23205
  ]
def negativeCoefficients : Array ℕ := #[
    294491080065520542835202863398912, 58708068423069874156816067198976, 475368975085586025561263702016, 158456325028528675187087900672, 5704427701027032306735164424192, 204250202961773462316156303966208,
    1838489511143503953858187367546880
  ]
def negativeScales : Array ℕ := #[
    11, 9, 1, 0, 3, 10,
    14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    18163703721038860, 13444885473582911, 16503779162636462, 13444885473582911, 18163703721038860, 19154543721753384,
    16503779162636462, 23102501662313104, 19136047378135995, 17351776069191432, 18163703721038860, 13444885473582911,
    19136047378135995, 13444885473582911, 18163703721038860, 18163703721038860, 13444885473582911, 12703254733743294,
    14890881736694821, 9533329732305783, 18278163569805379, 13781257245722226, 9533329732305783, 13781257245722226,
    14742783097922878, 18982478376579973, 14742783097922878, 18278163569805379, 18982478376579973, 12703254733743294,
    14742783097922878, 14742783097922878, 14890881736694821, 4392317422778759, 6714245517659862, 6442943495848725,
    10610102062999199, 9192292814470766, 4392317422778759, 11194141238863135, 11194141238863135, 10711666973558447,
    6442943495848725, 0, 27169925087433635, 27169924915450984, 31835005674468581, 34701043645685732,
    32834894750859872, 31176980523355049, 37465705145179614, 36465705045643886, 32176986237936182, 26424750689151217,
    31723464305301799, 37038402989524979, 33723466529579948
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    11859922974952585, 9533329732306630, 1584962500724866, 0, 3169925001442313, 10332036548361652,
    14502148077057846
  ]

abbrev PositiveTerm := Fin 57
abbrev NegativeTerm := Fin 7
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
noncomputable def positiveFloor : ℝ := 337299131759 / 200000000000
noncomputable def negativeCeiling : ℝ := 395339595561 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 11359763342371153751943860453376, coefficient := 11359763342371153751943860453376 }, { argument := 431383418064727357668754194432, coefficient := 431383418064727357668754194432 }, { argument := 7189723634412122627812569907200, coefficient := 7189723634412122627812569907200 }, { argument := 431383418064727357668754194432, coefficient := 431383418064727357668754194432 }, { argument := 11359763342371153751943860453376, coefficient := 11359763342371153751943860453376 }, { argument := 11287866106027032525665734754304, coefficient := 11287866106027032525665734754304 }, { argument := 7189723634412122627812569907200, coefficient := 7189723634412122627812569907200 }, { argument := 174207003661805731271898568851456, coefficient := 174207003661805731271898568851456 }, { argument := 11144071633338790073109483356160, coefficient := 11144071633338790073109483356160 }, { argument := 6470751270970910365031312916480, coefficient := 6470751270970910365031312916480 }, { argument := 11359763342371153751943860453376, coefficient := 11359763342371153751943860453376 }, { argument := 431383418064727357668754194432, coefficient := 431383418064727357668754194432 }, { argument := 11144071633338790073109483356160, coefficient := 11144071633338790073109483356160 }, { argument := 431383418064727357668754194432, coefficient := 431383418064727357668754194432 }, { argument := 11359763342371153751943860453376, coefficient := 11359763342371153751943860453376 }, { argument := 11359763342371153751943860453376, coefficient := 11359763342371153751943860453376 }, { argument := 431383418064727357668754194432, coefficient := 431383418064727357668754194432 }, { argument := 294491080065520542835202863398912, coefficient := (-294491080065520542835202863398912) }, { argument := 515988882624637565831391215616, coefficient := 515988882624637565831391215616 }, { argument := 587654005211392783307973328896, coefficient := 587654005211392783307973328896 }, { argument := 458656784555233391850125524992, coefficient := 458656784555233391850125524992 }, { argument := 6148867517943597659490745319424, coefficient := 6148867517943597659490745319424 }, { argument := 544654931659339652822024060928, coefficient := 544654931659339652822024060928 }, { argument := 458656784555233391850125524992, coefficient := 458656784555233391850125524992 }, { argument := 544654931659339652822024060928, coefficient := 544654931659339652822024060928 }, { argument := 530321907141988609326707638272, coefficient := 530321907141988609326707638272 }, { argument := 20037568275256758806452358873088, coefficient := 20037568275256758806452358873088 }, { argument := 530321907141988609326707638272, coefficient := 530321907141988609326707638272 }, { argument := 6148867517943597659490745319424, coefficient := 6148867517943597659490745319424 }, { argument := 20037568275256758806452358873088, coefficient := 20037568275256758806452358873088 }, { argument := 515988882624637565831391215616, coefficient := 515988882624637565831391215616 }, { argument := 530321907141988609326707638272, coefficient := 530321907141988609326707638272 }, { argument := 530321907141988609326707638272, coefficient := 530321907141988609326707638272 }, { argument := 587654005211392783307973328896, coefficient := 587654005211392783307973328896 }, { argument := 58708068423069874156816067198976, coefficient := (-58708068423069874156816067198976) }, { argument := 3249592603124123221610201088, coefficient := 3249592603124123221610201088 }, { argument := 64991852062482464432204021760, coefficient := 64991852062482464432204021760 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 60465633793845292802104098816, coefficient := 60465633793845292802104098816 }, { argument := 90524365372743432601998458880, coefficient := 90524365372743432601998458880 }, { argument := 3249592603124123221610201088, coefficient := 3249592603124123221610201088 }, { argument := 90640422251426437002770251776, coefficient := 90640422251426437002770251776 }, { argument := 90640422251426437002770251776, coefficient := 90640422251426437002770251776 }, { argument := 64875795183799460031432228864, coefficient := 64875795183799460031432228864 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 2852214020518709536674809905152, coefficient := 2852214020518709536674809905152 }, { argument := 2852213680508322770060354519040, coefficient := 2852213680508322770060354519040 }, { argument := 5704427701027032306735164424192, coefficient := (-5704427701027032306735164424192) }, { argument := 36181061446715063618710156607488, coefficient := 36181061446715063618710156607488 }, { argument := 131890861792487168891858054021120, coefficient := 131890861792487168891858054021120 }, { argument := 36178279722571229805588093337600, coefficient := 36178279722571229805588093337600 }, { argument := 204250202961773462316156303966208, coefficient := (-204250202961773462316156303966208) }, { argument := 22929574476362135457723530084352, coefficient := 22929574476362135457723530084352 }, { argument := 896315166602447105544428992856064, coefficient := 896315166602447105544428992856064 }, { argument := 896315104763058012366424919506944, coefficient := 896315104763058012366424919506944 }, { argument := 22929665301636700489609925099520, coefficient := 22929665301636700489609925099520 }, { argument := 1838489511143503953858187367546880, coefficient := (-1838489511143503953858187367546880) }, { argument := 850809379181845315388360884224, coefficient := 850809379181845315388360884224 }, { argument := 133956563309378331100499543064576, coefficient := 133956563309378331100499543064576 }, { argument := 1333091547595957170526960987668480, coefficient := 1333091547595957170526960987668480 }, { argument := 133956769837354092921563318845440, coefficient := 133956769837354092921563318845440 }] }

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


end Parent0

namespace Parent0

namespace TermShard12

/-! Directed signed-log shard 12.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-156916049286786710388856378739392512)
def positiveArguments : Array ℕ := #[
    90082947, 75854829, 13538855955, 13538857335, 75853449, 6042191,
    273096041, 759305
  ]
def positiveCoefficients : Array ℕ := #[
    850809379181845315388360884224, 358214302033408366975578537984, 63935439578292101590185337159680, 63935446095157847950295732060160, 358207785167662006865183637504, 28533440261496624483387047936,
    1289659590622794426934976577536, 28685731858202687671883530240
  ]
def positiveScales : Array ℕ := #[
    26, 26, 33, 33, 26, 22,
    28, 19
  ]
def negativeArguments : Array ℕ := #[
    20229, 1623, 17
  ]
def negativeCoefficients : Array ℕ := #[
    1602706499501053285179800571346944, 128587307760651019914321831395328, 1346878762742493739090247155712
  ]
def negativeScales : Array ℕ := #[
    14, 10, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    26424750689151217, 26176737691125395, 33656386783960695, 33656386931012932, 26176711444447458, 22526640359215455,
    28024833158990942, 19534319982740128
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    14304137383049236, 10664447284578613, 4087462841250340
  ]

abbrev PositiveTerm := Fin 8
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
noncomputable def positiveFloor : ℝ := 2637472959 / 50000000000
noncomputable def negativeCeiling : ℝ := 146263256041 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 850809379181845315388360884224, coefficient := 850809379181845315388360884224 }, { argument := 1602706499501053285179800571346944, coefficient := (-1602706499501053285179800571346944) }, { argument := 358214302033408366975578537984, coefficient := 358214302033408366975578537984 }, { argument := 63935439578292101590185337159680, coefficient := 63935439578292101590185337159680 }, { argument := 63935446095157847950295732060160, coefficient := 63935446095157847950295732060160 }, { argument := 358207785167662006865183637504, coefficient := 358207785167662006865183637504 }, { argument := 128587307760651019914321831395328, coefficient := (-128587307760651019914321831395328) }, { argument := 28533440261496624483387047936, coefficient := 28533440261496624483387047936 }, { argument := 1289659590622794426934976577536, coefficient := 1289659590622794426934976577536 }, { argument := 28685731858202687671883530240, coefficient := 28685731858202687671883530240 }, { argument := 1346878762742493739090247155712, coefficient := (-1346878762742493739090247155712) }] }

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

end TermShard12


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16
