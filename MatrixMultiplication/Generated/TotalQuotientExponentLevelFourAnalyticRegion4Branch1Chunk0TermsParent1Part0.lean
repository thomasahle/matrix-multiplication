import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 0, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk0

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
def constantNumerator : ℤ := 475368975085586025561263702016
def positiveArguments : Array ℕ := #[
    1, 1559045, 10543307, 3115819, 58071, 2039083,
    8155897, 232703, 38367, 649691, 14101729, 324845,
    19179
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 29449527413142024088746721280, 99578719190809820938155065344, 29428078424576830160186114048, 4387720704427570675272646656, 154068755439828556340462092288,
    154060538522148363157790261248, 4395635390652860200650801152, 362366069696519355827748864, 12272316010488250674125471744, 133187064760221758259376160768, 12272297121022319195544616960,
    362281067099827702213902336
  ]
def positiveScales : Array ℕ := #[
    0, 20, 23, 21, 15, 20,
    22, 17, 15, 19, 23, 18,
    14
  ]
def negativeArguments : Array ℕ := #[
    59815879515, 1012897505095, 21985230088805, 506447973025, 29900924055, 3372241041,
    118411588893, 473621094687, 13513295913, 59815879515, 404515059669, 119544627573,
    404515059669, 6849891668137, 148678858077803, 3424940562415, 202210084953, 118411588893,
    4157859480889, 16630550922451, 474500731349, 1012897505095, 6849891668137, 2024319561929,
    119544627573, 2024319561929, 43938435151051, 1012158223055, 59758292601, 473621094687,
    16630550922451, 66518655874609, 1897901699591, 21985230088805, 148678858077803, 43938435151051,
    13513295913, 474500731349, 1897901699591, 54150686209, 506447973025, 3424940562415,
    1012158223055, 29900924055, 202210084953, 59758292601, 1, 1,
    1
  ]
def negativeCoefficients : Array ℕ := #[
    33673346586824060625223680, 1140421206627586768403169280, 12376584254449601835339612160, 1140419451298966504944435200, 33665447608032875060920320, 30374446991302187047452672,
    1066556775229726325899001856, 1066499892773589801423077376, 30429237219167023266791424, 33673346586824060625223680, 113860866999441397188132864, 33648821261994220100517888,
    113860866999441397188132864, 3856146195518757306047135744, 41849378114816528123867168768, 3856140260164572749454376960, 113834157905610892520718336, 1066556775229726325899001856,
    37450668817581168669268901888, 37448671468658191060170702848, 1068480658445192114892439552, 1140421206627586768403169280, 3856146195518757306047135744, 1139590603097781262612430848,
    33648821261994220100517888, 1139590603097781262612430848, 12367570010844749170481299456, 1139588849047620343373496320, 33640928036270083525312512, 1066499892773589801423077376,
    37448671468658191060170702848, 37446674226259418387220267008, 1068423673382982330081083392, 12376584254449601835339612160, 41849378114816528123867168768, 12367570010844749170481299456,
    30429237219167023266791424, 1068480658445192114892439552, 1068423673382982330081083392, 30484126279088632085086208, 1140419451298966504944435200, 3856140260164572749454376960,
    1139588849047620343373496320, 33665447608032875060920320, 113834157905610892520718336, 33640928036270083525312512, 158456325028528675187087900672, 316912650057057350374175801344,
    158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    35, 39, 44, 38, 34, 31,
    36, 38, 33, 35, 38, 36,
    38, 42, 47, 41, 37, 36,
    41, 43, 38, 39, 42, 40,
    36, 40, 45, 39, 35, 38,
    43, 45, 40, 44, 47, 45,
    33, 38, 40, 35, 38, 41,
    39, 34, 37, 35, 0, 0,
    0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 20572231139655986, 23329824116024454, 21571179998042343, 15825530257377616, 20959489069403038,
    22959412124390183, 17828130284410333, 15227578341406248, 19309394194481380, 23749368725176471, 18309391973893206,
    14227239879225015
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    35799809481705925, 39881625337267546, 44321599864846377, 38881623116679245, 34799471019520264, 31651060514910585,
    36785019328076366, 38784942383061785, 33653660541948290, 35799809481705925, 38557402457432366, 36798758340078620,
    38557402457432366, 42639218310521991, 47079192841214685, 41639216089933817, 37557063995251116, 36785019328076366,
    41918978146428850, 43918901201406791, 38787619355138911, 39881625337267546, 42639218310521991, 40880574195594098,
    36798758340078620, 40880574195594098, 45320548723232729, 39880571975005799, 35798419877893047, 38784942383061785,
    43918901201406791, 45918824256384743, 40787542410124291, 44321599864846377, 47079192841214685, 45320548723232729,
    33653660541948290, 38787619355138911, 40787542410124291, 35656260568986090, 38881623116679245, 41639216089933817,
    39880571975005799, 34799471019520264, 37557063995251116, 35798419877893047, 0, 0,
    0
  ]

abbrev PositiveTerm := Fin 13
abbrev NegativeTerm := Fin 49
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
noncomputable def positiveFloor : ℝ := 84941881 / 500000000000
noncomputable def negativeCeiling : ℝ := 169883763 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 33673346586824060625223680, coefficient := (-33673346586824060625223680) }, { argument := 1140421206627586768403169280, coefficient := (-1140421206627586768403169280) }, { argument := 12376584254449601835339612160, coefficient := (-12376584254449601835339612160) }, { argument := 1140419451298966504944435200, coefficient := (-1140419451298966504944435200) }, { argument := 33665447608032875060920320, coefficient := (-33665447608032875060920320) }, { argument := 30374446991302187047452672, coefficient := (-30374446991302187047452672) }, { argument := 1066556775229726325899001856, coefficient := (-1066556775229726325899001856) }, { argument := 1066499892773589801423077376, coefficient := (-1066499892773589801423077376) }, { argument := 30429237219167023266791424, coefficient := (-30429237219167023266791424) }, { argument := 33673346586824060625223680, coefficient := (-33673346586824060625223680) }, { argument := 113860866999441397188132864, coefficient := (-113860866999441397188132864) }, { argument := 33648821261994220100517888, coefficient := (-33648821261994220100517888) }, { argument := 113860866999441397188132864, coefficient := (-113860866999441397188132864) }, { argument := 3856146195518757306047135744, coefficient := (-3856146195518757306047135744) }, { argument := 41849378114816528123867168768, coefficient := (-41849378114816528123867168768) }, { argument := 3856140260164572749454376960, coefficient := (-3856140260164572749454376960) }, { argument := 113834157905610892520718336, coefficient := (-113834157905610892520718336) }, { argument := 1066556775229726325899001856, coefficient := (-1066556775229726325899001856) }, { argument := 37450668817581168669268901888, coefficient := (-37450668817581168669268901888) }, { argument := 37448671468658191060170702848, coefficient := (-37448671468658191060170702848) }, { argument := 1068480658445192114892439552, coefficient := (-1068480658445192114892439552) }, { argument := 1140421206627586768403169280, coefficient := (-1140421206627586768403169280) }, { argument := 3856146195518757306047135744, coefficient := (-3856146195518757306047135744) }, { argument := 1139590603097781262612430848, coefficient := (-1139590603097781262612430848) }, { argument := 33648821261994220100517888, coefficient := (-33648821261994220100517888) }, { argument := 1139590603097781262612430848, coefficient := (-1139590603097781262612430848) }, { argument := 12367570010844749170481299456, coefficient := (-12367570010844749170481299456) }, { argument := 1139588849047620343373496320, coefficient := (-1139588849047620343373496320) }, { argument := 33640928036270083525312512, coefficient := (-33640928036270083525312512) }, { argument := 1066499892773589801423077376, coefficient := (-1066499892773589801423077376) }, { argument := 37448671468658191060170702848, coefficient := (-37448671468658191060170702848) }, { argument := 37446674226259418387220267008, coefficient := (-37446674226259418387220267008) }, { argument := 1068423673382982330081083392, coefficient := (-1068423673382982330081083392) }, { argument := 12376584254449601835339612160, coefficient := (-12376584254449601835339612160) }, { argument := 41849378114816528123867168768, coefficient := (-41849378114816528123867168768) }, { argument := 12367570010844749170481299456, coefficient := (-12367570010844749170481299456) }, { argument := 30429237219167023266791424, coefficient := (-30429237219167023266791424) }, { argument := 1068480658445192114892439552, coefficient := (-1068480658445192114892439552) }, { argument := 1068423673382982330081083392, coefficient := (-1068423673382982330081083392) }, { argument := 30484126279088632085086208, coefficient := (-30484126279088632085086208) }, { argument := 1140419451298966504944435200, coefficient := (-1140419451298966504944435200) }, { argument := 3856140260164572749454376960, coefficient := (-3856140260164572749454376960) }, { argument := 1139588849047620343373496320, coefficient := (-1139588849047620343373496320) }, { argument := 33665447608032875060920320, coefficient := (-33665447608032875060920320) }, { argument := 113834157905610892520718336, coefficient := (-113834157905610892520718336) }, { argument := 33640928036270083525312512, coefficient := (-33640928036270083525312512) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 29449527413142024088746721280, coefficient := 29449527413142024088746721280 }, { argument := 99578719190809820938155065344, coefficient := 99578719190809820938155065344 }, { argument := 29428078424576830160186114048, coefficient := 29428078424576830160186114048 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 4387720704427570675272646656, coefficient := 4387720704427570675272646656 }, { argument := 154068755439828556340462092288, coefficient := 154068755439828556340462092288 }, { argument := 154060538522148363157790261248, coefficient := 154060538522148363157790261248 }, { argument := 4395635390652860200650801152, coefficient := 4395635390652860200650801152 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 362366069696519355827748864, coefficient := 362366069696519355827748864 }, { argument := 12272316010488250674125471744, coefficient := 12272316010488250674125471744 }, { argument := 133187064760221758259376160768, coefficient := 133187064760221758259376160768 }, { argument := 12272297121022319195544616960, coefficient := 12272297121022319195544616960 }, { argument := 362281067099827702213902336, coefficient := 362281067099827702213902336 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk0
