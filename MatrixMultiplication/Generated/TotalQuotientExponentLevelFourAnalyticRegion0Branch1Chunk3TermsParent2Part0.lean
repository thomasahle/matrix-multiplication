import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 3, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk3

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 25881470930998257176931272228864
def positiveArguments : Array ℕ := #[
    9, 461693, 8155861, 16315511, 232753, 19339
  ]
def positiveCoefficients : Array ℕ := #[
    713053462628379038341895553024, 4360567097151070215293894656, 154059858501374829928879489024, 154095644594582016100308877312, 4396579863949434129693540352, 1461213526595457100602671104
  ]
def positiveScales : Array ℕ := #[
    3, 18, 22, 23, 17, 14
  ]
def negativeArguments : Array ℕ := #[
    19735092973, 3793981620045, 3794404694455, 9824562537, 4949921475, 207071458537,
    2171358399593, 12949820051, 5059741371, 2794809310495, 134036412834379, 134051071433061,
    2782989748017, 207071458537, 8777573571647, 93150097918521, 1097866244679, 211753751143,
    19735092973, 2794809310495, 349438303541, 79641501061, 349438303541, 134067499654843,
    134082159284337, 695921707467, 2171358399593, 93150097918521, 247267121204917, 23300394625927,
    1108141670455, 3793981620045, 134036412834379, 134067499654843, 3825265754029, 79641501061,
    3825265754029, 3825689885811, 79297570395, 12949820051, 1097866244679, 23300394625927,
    2197071607963, 13242465089, 3794404694455, 134051071433061, 134082159284337, 3825689885811,
    5059741371, 211753751143, 1108141670455, 13242465089, 161548179, 9824562537,
    2782989748017, 695921707467, 79297570395, 1
  ]
def negativeCoefficients : Array ℕ := #[
    22219739339831223519281152, 1067910888142823296094699520, 1068029973002524920622612480, 22122948090355667410354176, 1393279031895200995737600, 58285433969143644550070272,
    611183054955926959589163008, 58320804756198577506615296, 1424190584564167659749376, 786668885582304678479134720, 37727896180936701999132442624, 37732022209659328801869398016,
    783341974509079484958769152, 58285433969143644550070272, 2470667316655408929604370432, 26219421642211024416880459776, 2472175005219495093460795392, 59603382171369971340279808,
    22219739339831223519281152, 786668885582304678479134720, 786865106808112936457863168, 22417089656346660114006016, 786865106808112936457863168, 37736646343002814743480107008,
    37740772661873225239281795072, 783538185606855130934673408, 611183054955926959589163008, 26219421642211024416880459776, 278398028729859867775973982208, 26233912138727586184139112448,
    623828301766857122077736960, 1067910888142823296094699520, 37727896180936701999132442624, 37736646343002814743480107008, 1076716589027382737999233024, 22417089656346660114006016,
    1076716589027382737999233024, 1076835971510843437026902016, 22320281780144229706629120, 58320804756198577506615296, 2472175005219495093460795392, 26233912138727586184139112448,
    2473682718732115818066214912, 59638760840287202148614144, 1068029973002524920622612480, 37732022209659328801869398016, 37740772661873225239281795072, 1076835971510843437026902016,
    1424190584564167659749376, 59603382171369971340279808, 623828301766857122077736960, 59638760840287202148614144, 1455096637493564374253568, 22122948090355667410354176,
    783341974509079484958769152, 783538185606855130934673408, 22320281780144229706629120, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    34, 41, 41, 33, 32, 37,
    40, 33, 32, 41, 46, 46,
    41, 37, 42, 46, 39, 37,
    34, 41, 38, 36, 38, 46,
    46, 39, 40, 46, 47, 44,
    40, 41, 46, 46, 41, 36,
    41, 41, 36, 33, 39, 44,
    40, 33, 41, 46, 46, 41,
    32, 37, 40, 33, 27, 33,
    41, 39, 36, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 18816574333383227, 22959405756343180, 23959740836640406, 17828440237455185, 14239225576001204
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    34200044264728410, 41786849828767261, 41787010697583060, 33193746023214841, 32204758492607464, 37591337758768726,
    40981735029935156, 33592212999428332, 32236416497342277, 41345886990164667, 46929618317653149, 46929776086229320,
    41339772732724885, 37591337758768726, 42996959344704383, 46404622519251106, 39997839460043069, 37623596570389253,
    34200044264728410, 41345886990164667, 38346246801128049, 36212801361705678, 38346246801128049, 46929952880526392,
    46930110623613493, 39340134052992272, 40981735029935156, 46404622519251106, 47813063748417540, 44405419622752043,
    40011279473282165, 41786849828767261, 46929618317653149, 46929952880526392, 41798697119422935, 36212801361705678,
    41798697119422935, 41798857071422628, 36206557612624038, 33592212999428332, 39997839460043069, 44405419622752043,
    40998719053350016, 33624452654160031, 41787010697583060, 46929776086229320, 46930110623613493, 41798857071422628,
    32236416497342277, 37623596570389253, 40011279473282165, 33624452654160031, 27267389247477006, 33193746023214841,
    41339772732724885, 39340134052992272, 36206557612624038, 0
  ]

abbrev PositiveTerm := Fin 6
abbrev NegativeTerm := Fin 58
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
noncomputable def positiveFloor : ℝ := 23281561 / 200000000000
noncomputable def negativeCeiling : ℝ := 401800053 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 22219739339831223519281152, coefficient := (-22219739339831223519281152) }, { argument := 1067910888142823296094699520, coefficient := (-1067910888142823296094699520) }, { argument := 1068029973002524920622612480, coefficient := (-1068029973002524920622612480) }, { argument := 22122948090355667410354176, coefficient := (-22122948090355667410354176) }, { argument := 1393279031895200995737600, coefficient := (-1393279031895200995737600) }, { argument := 58285433969143644550070272, coefficient := (-58285433969143644550070272) }, { argument := 611183054955926959589163008, coefficient := (-611183054955926959589163008) }, { argument := 58320804756198577506615296, coefficient := (-58320804756198577506615296) }, { argument := 1424190584564167659749376, coefficient := (-1424190584564167659749376) }, { argument := 786668885582304678479134720, coefficient := (-786668885582304678479134720) }, { argument := 37727896180936701999132442624, coefficient := (-37727896180936701999132442624) }, { argument := 37732022209659328801869398016, coefficient := (-37732022209659328801869398016) }, { argument := 783341974509079484958769152, coefficient := (-783341974509079484958769152) }, { argument := 58285433969143644550070272, coefficient := (-58285433969143644550070272) }, { argument := 2470667316655408929604370432, coefficient := (-2470667316655408929604370432) }, { argument := 26219421642211024416880459776, coefficient := (-26219421642211024416880459776) }, { argument := 2472175005219495093460795392, coefficient := (-2472175005219495093460795392) }, { argument := 59603382171369971340279808, coefficient := (-59603382171369971340279808) }, { argument := 22219739339831223519281152, coefficient := (-22219739339831223519281152) }, { argument := 786668885582304678479134720, coefficient := (-786668885582304678479134720) }, { argument := 786865106808112936457863168, coefficient := (-786865106808112936457863168) }, { argument := 22417089656346660114006016, coefficient := (-22417089656346660114006016) }, { argument := 786865106808112936457863168, coefficient := (-786865106808112936457863168) }, { argument := 37736646343002814743480107008, coefficient := (-37736646343002814743480107008) }, { argument := 37740772661873225239281795072, coefficient := (-37740772661873225239281795072) }, { argument := 783538185606855130934673408, coefficient := (-783538185606855130934673408) }, { argument := 611183054955926959589163008, coefficient := (-611183054955926959589163008) }, { argument := 26219421642211024416880459776, coefficient := (-26219421642211024416880459776) }, { argument := 278398028729859867775973982208, coefficient := (-278398028729859867775973982208) }, { argument := 26233912138727586184139112448, coefficient := (-26233912138727586184139112448) }, { argument := 623828301766857122077736960, coefficient := (-623828301766857122077736960) }, { argument := 1067910888142823296094699520, coefficient := (-1067910888142823296094699520) }, { argument := 37727896180936701999132442624, coefficient := (-37727896180936701999132442624) }, { argument := 37736646343002814743480107008, coefficient := (-37736646343002814743480107008) }, { argument := 1076716589027382737999233024, coefficient := (-1076716589027382737999233024) }, { argument := 22417089656346660114006016, coefficient := (-22417089656346660114006016) }, { argument := 1076716589027382737999233024, coefficient := (-1076716589027382737999233024) }, { argument := 1076835971510843437026902016, coefficient := (-1076835971510843437026902016) }, { argument := 22320281780144229706629120, coefficient := (-22320281780144229706629120) }, { argument := 58320804756198577506615296, coefficient := (-58320804756198577506615296) }, { argument := 2472175005219495093460795392, coefficient := (-2472175005219495093460795392) }, { argument := 26233912138727586184139112448, coefficient := (-26233912138727586184139112448) }, { argument := 2473682718732115818066214912, coefficient := (-2473682718732115818066214912) }, { argument := 59638760840287202148614144, coefficient := (-59638760840287202148614144) }, { argument := 1068029973002524920622612480, coefficient := (-1068029973002524920622612480) }, { argument := 37732022209659328801869398016, coefficient := (-37732022209659328801869398016) }, { argument := 37740772661873225239281795072, coefficient := (-37740772661873225239281795072) }, { argument := 1076835971510843437026902016, coefficient := (-1076835971510843437026902016) }, { argument := 1424190584564167659749376, coefficient := (-1424190584564167659749376) }, { argument := 59603382171369971340279808, coefficient := (-59603382171369971340279808) }, { argument := 623828301766857122077736960, coefficient := (-623828301766857122077736960) }, { argument := 59638760840287202148614144, coefficient := (-59638760840287202148614144) }, { argument := 1455096637493564374253568, coefficient := (-1455096637493564374253568) }, { argument := 22122948090355667410354176, coefficient := (-22122948090355667410354176) }, { argument := 783341974509079484958769152, coefficient := (-783341974509079484958769152) }, { argument := 783538185606855130934673408, coefficient := (-783538185606855130934673408) }, { argument := 22320281780144229706629120, coefficient := (-22320281780144229706629120) }, { argument := 713053462628379038341895553024, coefficient := 713053462628379038341895553024 }, { argument := 4360567097151070215293894656, coefficient := 4360567097151070215293894656 }, { argument := 154059858501374829928879489024, coefficient := 154059858501374829928879489024 }, { argument := 154095644594582016100308877312, coefficient := 154095644594582016100308877312 }, { argument := 4396579863949434129693540352, coefficient := 4396579863949434129693540352 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 1461213526595457100602671104, coefficient := 1461213526595457100602671104 }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-26668706242448133437284052631552)
def positiveArguments : Array ℕ := #[
    3311915, 70322025, 207111, 157961, 342661, 16434381,
    16436179, 341211
  ]
def positiveCoefficients : Array ℕ := #[
    62560305560452884111671951360, 664172747735042524917320908800, 62595458856551365750642704384, 1491899464001144055201267712, 3236341642773190997140570112, 155218340002219445553412964352,
    155235321632091844797601415168, 3222646779972869026020851712
  ]
def positiveScales : Array ℕ := #[
    21, 26, 17, 17, 18, 23,
    23, 18
  ]
def negativeArguments : Array ℕ := #[
    5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    792281625142643375935439503360, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    21659234215996668, 26067473279280369, 17660044653894114, 17269208880612298, 18386422475140169, 23970213781727482,
    23970371610839463, 18380304631613657
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2321928094887363, 0
  ]

abbrev PositiveTerm := Fin 8
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 329333049 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1383977 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 62560305560452884111671951360, coefficient := 62560305560452884111671951360 }, { argument := 664172747735042524917320908800, coefficient := 664172747735042524917320908800 }, { argument := 62595458856551365750642704384, coefficient := 62595458856551365750642704384 }, { argument := 1491899464001144055201267712, coefficient := 1491899464001144055201267712 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 3236341642773190997140570112, coefficient := 3236341642773190997140570112 }, { argument := 155218340002219445553412964352, coefficient := 155218340002219445553412964352 }, { argument := 155235321632091844797601415168, coefficient := 155235321632091844797601415168 }, { argument := 3222646779972869026020851712, coefficient := 3222646779972869026020851712 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk3
