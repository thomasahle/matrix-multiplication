import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 22, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk22

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 3150084880921802675389425283760128
def positiveArguments : Array ℕ := #[
    227, 21, 315, 553, 21, 175,
    21, 553, 1099, 175, 16961, 1085,
    315, 553, 21, 1085, 21, 553,
    553, 21, 873, 3977
  ]
def positiveCoefficients : Array ℕ := #[
    35969585781476009267468953452544, 1624796301562061610805100544, 24371944523430924162076508160, 42786302607800955751200980992, 1624796301562061610805100544, 27079938359367693513418342400,
    1624796301562061610805100544, 42786302607800955751200980992, 42515503224207278816066797568, 27079938359367693513418342400, 656146906447479213830126436352, 41973904457019924945798430720,
    24371944523430924162076508160, 42786302607800955751200980992, 1624796301562061610805100544, 41973904457019924945798430720, 1624796301562061610805100544, 42786302607800955751200980992,
    42786302607800955751200980992, 1624796301562061610805100544, 67545103393508561249183465472, 76926367753718083644903391232
  ]
def positiveScales : Array ℕ := #[
    7, 4, 8, 9, 4, 7,
    4, 9, 10, 7, 14, 10,
    8, 9, 4, 10, 4, 9,
    9, 4, 9, 11
  ]
def negativeArguments : Array ℕ := #[
    931135599, 7023266679, 25262481387, 3511634511, 17590908879, 17590913073,
    553, 931135377, 931135599, 1099, 5026896381, 18081596793,
    2513449029, 10796137209, 10796139783, 175, 17590908879, 17590913073,
    16961, 1085, 1058568069, 105027525, 1058568177, 105027525,
    3762087, 553, 260787111, 938043483, 130393599, 931135377,
    931135599, 21, 931135377, 931135599, 1085, 21,
    1031798661, 1031798907, 553, 553, 30247, 7
  ]
def negativeCoefficients : Array ℕ := #[
    17176420092673243495985577984, 129556402988925013788683403264, 466010528812840103743315771392, 129556446209646378490162839552, 648989988229715963978006396928, 648990142961005254253725351936,
    21393151303900477875600490496, 17176415997496059132465119232, 17176420092673243495985577984, 21257751612103639408033398784, 92729871025363742263603101696, 333546588484478384113333567488,
    92729901960553553874521161728, 199153580079075928860203679744, 199153627560995174588589539328, 13539969179683846756709171200, 648989988229715963978006396928, 648990142961005254253725351936,
    328073453223739606915063218176, 20986952228509962472899215360, 39054268506887827442009899008, 3874831748740263550176460800, 39054272491384547363273048064, 3874831748740263550176460800,
    71063814217758459812231774208, 21393151303900477875600490496, 4810673094339085019042021376, 17303848060912116528240918528, 4810674699205819431773011968, 17176415997496059132465119232,
    17176420092673243495985577984, 812398150781030805402550272, 17176415997496059132465119232, 17176420092673243495985577984, 20986952228509962472899215360, 812398150781030805402550272,
    19033325835063200660299186176, 19033330372962242792848883712, 21393151303900477875600490496, 21393151303900477875600490496, 1142699352058865270229303296, 1109194275199700726309615304704
  ]
def negativeScales : Array ℕ := #[
    29, 32, 34, 31, 34, 34,
    9, 29, 29, 10, 32, 34,
    31, 33, 33, 7, 34, 34,
    14, 10, 29, 26, 29, 26,
    21, 9, 27, 29, 26, 29,
    29, 4, 29, 29, 10, 4,
    29, 29, 9, 9, 14, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7826548487222833, 4392317422778759, 8299208018387278, 9111135670234706, 4392317422778759, 7451211111832325,
    4392317422778759, 9111135670234706, 10101975670949231, 7451211111832325, 14049933611508950, 10083479327331841,
    8299208018387278, 9111135670234706, 4392317422778759, 10083479327331841, 4392317422778759, 9111135670234706,
    9111135670234706, 4392317422778759, 9769837843608060, 11957464846075818
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    29794416038909017, 32709495070561436, 34556277302525558, 31709495551852277, 34034110974113932, 34034111318079234,
    9111135670234708, 29794415694943711, 29794416038909017, 10101975670949232, 32227020805172287, 34073803037225162,
    31227021286463126, 33329796166238042, 33329796510203343, 7451211111832378, 34034110974113932, 34034111318079234,
    14049933611508951, 10083479327331842, 29979466912794946, 26646192229648104, 29979467059985386, 26646192229648104,
    21843101783077954, 9111135670234708, 27958297339440358, 29805079560225814, 26958297820731294, 29794415694943711,
    29794416038909017, 4392317422778766, 29794415694943711, 29794416038909017, 10083479327331842, 4392317422778766,
    29942514342537762, 29942514686503118, 9111135670234708, 9111135670234708, 14884504440946755, 2807354922807594
  ]

abbrev PositiveTerm := Fin 22
abbrev NegativeTerm := Fin 42
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
noncomputable def positiveFloor : ℝ := 356769283 / 100000000000
noncomputable def negativeCeiling : ℝ := 390467711 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 17176420092673243495985577984, coefficient := (-17176420092673243495985577984) }, { argument := 129556402988925013788683403264, coefficient := (-129556402988925013788683403264) }, { argument := 466010528812840103743315771392, coefficient := (-466010528812840103743315771392) }, { argument := 129556446209646378490162839552, coefficient := (-129556446209646378490162839552) }, { argument := 648989988229715963978006396928, coefficient := (-648989988229715963978006396928) }, { argument := 648990142961005254253725351936, coefficient := (-648990142961005254253725351936) }, { argument := 21393151303900477875600490496, coefficient := (-21393151303900477875600490496) }, { argument := 17176415997496059132465119232, coefficient := (-17176415997496059132465119232) }, { argument := 17176420092673243495985577984, coefficient := (-17176420092673243495985577984) }, { argument := 21257751612103639408033398784, coefficient := (-21257751612103639408033398784) }, { argument := 92729871025363742263603101696, coefficient := (-92729871025363742263603101696) }, { argument := 333546588484478384113333567488, coefficient := (-333546588484478384113333567488) }, { argument := 92729901960553553874521161728, coefficient := (-92729901960553553874521161728) }, { argument := 199153580079075928860203679744, coefficient := (-199153580079075928860203679744) }, { argument := 199153627560995174588589539328, coefficient := (-199153627560995174588589539328) }, { argument := 13539969179683846756709171200, coefficient := (-13539969179683846756709171200) }, { argument := 648989988229715963978006396928, coefficient := (-648989988229715963978006396928) }, { argument := 648990142961005254253725351936, coefficient := (-648990142961005254253725351936) }, { argument := 328073453223739606915063218176, coefficient := (-328073453223739606915063218176) }, { argument := 20986952228509962472899215360, coefficient := (-20986952228509962472899215360) }, { argument := 39054268506887827442009899008, coefficient := (-39054268506887827442009899008) }, { argument := 3874831748740263550176460800, coefficient := (-3874831748740263550176460800) }, { argument := 39054272491384547363273048064, coefficient := (-39054272491384547363273048064) }, { argument := 3874831748740263550176460800, coefficient := (-3874831748740263550176460800) }, { argument := 71063814217758459812231774208, coefficient := (-71063814217758459812231774208) }, { argument := 21393151303900477875600490496, coefficient := (-21393151303900477875600490496) }, { argument := 4810673094339085019042021376, coefficient := (-4810673094339085019042021376) }, { argument := 17303848060912116528240918528, coefficient := (-17303848060912116528240918528) }, { argument := 4810674699205819431773011968, coefficient := (-4810674699205819431773011968) }, { argument := 17176415997496059132465119232, coefficient := (-17176415997496059132465119232) }, { argument := 17176420092673243495985577984, coefficient := (-17176420092673243495985577984) }, { argument := 812398150781030805402550272, coefficient := (-812398150781030805402550272) }, { argument := 17176415997496059132465119232, coefficient := (-17176415997496059132465119232) }, { argument := 17176420092673243495985577984, coefficient := (-17176420092673243495985577984) }, { argument := 20986952228509962472899215360, coefficient := (-20986952228509962472899215360) }, { argument := 812398150781030805402550272, coefficient := (-812398150781030805402550272) }, { argument := 19033325835063200660299186176, coefficient := (-19033325835063200660299186176) }, { argument := 19033330372962242792848883712, coefficient := (-19033330372962242792848883712) }, { argument := 21393151303900477875600490496, coefficient := (-21393151303900477875600490496) }, { argument := 21393151303900477875600490496, coefficient := (-21393151303900477875600490496) }, { argument := 1142699352058865270229303296, coefficient := (-1142699352058865270229303296) }, { argument := 35969585781476009267468953452544, coefficient := 35969585781476009267468953452544 }, { argument := 1624796301562061610805100544, coefficient := 1624796301562061610805100544 }, { argument := 24371944523430924162076508160, coefficient := 24371944523430924162076508160 }, { argument := 42786302607800955751200980992, coefficient := 42786302607800955751200980992 }, { argument := 1624796301562061610805100544, coefficient := 1624796301562061610805100544 }, { argument := 27079938359367693513418342400, coefficient := 27079938359367693513418342400 }, { argument := 1624796301562061610805100544, coefficient := 1624796301562061610805100544 }, { argument := 42786302607800955751200980992, coefficient := 42786302607800955751200980992 }, { argument := 42515503224207278816066797568, coefficient := 42515503224207278816066797568 }, { argument := 27079938359367693513418342400, coefficient := 27079938359367693513418342400 }, { argument := 656146906447479213830126436352, coefficient := 656146906447479213830126436352 }, { argument := 41973904457019924945798430720, coefficient := 41973904457019924945798430720 }, { argument := 24371944523430924162076508160, coefficient := 24371944523430924162076508160 }, { argument := 42786302607800955751200980992, coefficient := 42786302607800955751200980992 }, { argument := 1624796301562061610805100544, coefficient := 1624796301562061610805100544 }, { argument := 41973904457019924945798430720, coefficient := 41973904457019924945798430720 }, { argument := 1624796301562061610805100544, coefficient := 1624796301562061610805100544 }, { argument := 42786302607800955751200980992, coefficient := 42786302607800955751200980992 }, { argument := 42786302607800955751200980992, coefficient := 42786302607800955751200980992 }, { argument := 1624796301562061610805100544, coefficient := 1624796301562061610805100544 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 67545103393508561249183465472, coefficient := 67545103393508561249183465472 }, { argument := 76926367753718083644903391232, coefficient := 76926367753718083644903391232 }] }

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


end Parent3

namespace Parent3

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1387997214836829526114179571777536)
def positiveArguments : Array ℕ := #[
    97, 41613, 1843, 97, 1843, 3589,
    67803, 3589, 41613, 67803, 873, 3589,
    3589, 3977, 21, 105, 87, 1563,
    585, 21, 2343, 2343, 1677, 87,
    915, 1005, 915, 1005, 5, 11,
    1468006303, 1468006497, 31438885, 1829305257, 503022087, 11312943,
    55208991, 441671811, 5656491, 8743, 3116961, 7869959,
    3116967, 8743
  ]
def positiveCoefficients : Array ℕ := #[
    60040091905340943332607524864, 804912482105977021552769630208, 71297609137592370207471435776, 60040091905340943332607524864, 71297609137592370207471435776, 69421356265550465728327450624,
    2623001515114582461843291242496, 69421356265550465728327450624, 804912482105977021552769630208, 2623001515114582461843291242496, 67545103393508561249183465472, 69421356265550465728327450624,
    69421356265550465728327450624, 76926367753718083644903391232, 51993481649985971545763217408, 1039869632999719430915264348160, 53850391708914041958111903744, 967450140701524684833665581056,
    1448389845963894921631975342080, 51993481649985971545763217408, 1450246756022822992044324028416, 1450246756022822992044324028416, 1038012722940791360502915661824, 53850391708914041958111903744,
    566357567973061475766349332480, 622064869740903588136809922560, 566357567973061475766349332480, 622064869740903588136809922560, 792281625142643375935439503360, 1743019575313815427057966907392,
    6932463761928580701079509925888, 6932464678067678377790681382912, 4750909977049383867654047006720, 17277299665188084870277962399744, 4750909287583877368685845807104, 106847725691629545465531334656,
    4171473418423230348418168651776, 4171472313389473356921188646912, 106848094036215209297858002944, 660602402555668929653506048, 117755457238494817719416782848, 1189274579301065925642680270848,
    117755683912085995462387040256, 660602402555668929653506048
  ]
def positiveScales : Array ℕ := #[
    6, 15, 10, 6, 10, 11,
    16, 11, 15, 16, 9, 11,
    11, 11, 4, 6, 6, 10,
    9, 4, 11, 11, 10, 6,
    9, 9, 9, 9, 2, 3,
    30, 30, 24, 30, 28, 23,
    25, 28, 22, 13, 21, 22,
    21, 13
  ]
def negativeArguments : Array ℕ := #[
    97, 3, 15, 5, 11, 175,
    169, 27, 9
  ]
def negativeCoefficients : Array ℕ := #[
    7685131763883640746573763182592, 7605903601369376408980219232256, 2376844875427930127806318510080, 792281625142643375935439503360, 1743019575313815427057966907392, 13864928439996259078870191308800,
    26779118929821346106617855213568, 8556641551540548460102746636288, 1426106925256758076683791106048
  ]
def negativeScales : Array ℕ := #[
    6, 1, 3, 2, 3, 7,
    7, 4, 3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6599912842186776, 15344746679686672, 10847840355527847, 6599912842186776, 10847840355527847, 11809366207767696,
    16049061487562564, 11809366207767696, 15344746679686672, 16049061487562564, 9769837843608060, 11809366207767696,
    11809366207767696, 11957464846075818, 4392317422778759, 6714245517659862, 6442943495848725, 10610102062999199,
    9192292814470766, 4392317422778759, 11194141238863135, 11194141238863135, 10711666973558447, 6442943495848725,
    9837627933086892, 9972979785123183, 9837627933086892, 9972979785123183, 2321928094887362, 3459431618637292,
    30451211016504795, 30451211207159848, 24906046716319831, 30768648692318190, 28906046506951828, 23431470951557832,
    25718399898868316, 28718399516694735, 22431475925065575, 13093912683665561, 21571708673129583, 22907924688780240,
    21571711450245470, 13093912683665561
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6599912842192769, 1584962500724866, 3906890600547867, 2321928094887363, 3459431618637364, 7451211111832378,
    7400879436282192, 4754887502413606, 3169925001442313
  ]

abbrev PositiveTerm := Fin 44
abbrev NegativeTerm := Fin 9
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
noncomputable def positiveFloor : ℝ := 5105508529 / 250000000000
noncomputable def negativeCeiling : ℝ := 1027093341 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 60040091905340943332607524864, coefficient := 60040091905340943332607524864 }, { argument := 804912482105977021552769630208, coefficient := 804912482105977021552769630208 }, { argument := 71297609137592370207471435776, coefficient := 71297609137592370207471435776 }, { argument := 60040091905340943332607524864, coefficient := 60040091905340943332607524864 }, { argument := 71297609137592370207471435776, coefficient := 71297609137592370207471435776 }, { argument := 69421356265550465728327450624, coefficient := 69421356265550465728327450624 }, { argument := 2623001515114582461843291242496, coefficient := 2623001515114582461843291242496 }, { argument := 69421356265550465728327450624, coefficient := 69421356265550465728327450624 }, { argument := 804912482105977021552769630208, coefficient := 804912482105977021552769630208 }, { argument := 2623001515114582461843291242496, coefficient := 2623001515114582461843291242496 }, { argument := 67545103393508561249183465472, coefficient := 67545103393508561249183465472 }, { argument := 69421356265550465728327450624, coefficient := 69421356265550465728327450624 }, { argument := 69421356265550465728327450624, coefficient := 69421356265550465728327450624 }, { argument := 76926367753718083644903391232, coefficient := 76926367753718083644903391232 }, { argument := 7685131763883640746573763182592, coefficient := (-7685131763883640746573763182592) }, { argument := 51993481649985971545763217408, coefficient := 51993481649985971545763217408 }, { argument := 1039869632999719430915264348160, coefficient := 1039869632999719430915264348160 }, { argument := 53850391708914041958111903744, coefficient := 53850391708914041958111903744 }, { argument := 967450140701524684833665581056, coefficient := 967450140701524684833665581056 }, { argument := 1448389845963894921631975342080, coefficient := 1448389845963894921631975342080 }, { argument := 51993481649985971545763217408, coefficient := 51993481649985971545763217408 }, { argument := 1450246756022822992044324028416, coefficient := 1450246756022822992044324028416 }, { argument := 1450246756022822992044324028416, coefficient := 1450246756022822992044324028416 }, { argument := 1038012722940791360502915661824, coefficient := 1038012722940791360502915661824 }, { argument := 53850391708914041958111903744, coefficient := 53850391708914041958111903744 }, { argument := 7605903601369376408980219232256, coefficient := (-7605903601369376408980219232256) }, { argument := 566357567973061475766349332480, coefficient := 566357567973061475766349332480 }, { argument := 622064869740903588136809922560, coefficient := 622064869740903588136809922560 }, { argument := 566357567973061475766349332480, coefficient := 566357567973061475766349332480 }, { argument := 622064869740903588136809922560, coefficient := 622064869740903588136809922560 }, { argument := 2376844875427930127806318510080, coefficient := (-2376844875427930127806318510080) }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 1743019575313815427057966907392, coefficient := 1743019575313815427057966907392 }, { argument := 1743019575313815427057966907392, coefficient := (-1743019575313815427057966907392) }, { argument := 6932463761928580701079509925888, coefficient := 6932463761928580701079509925888 }, { argument := 6932464678067678377790681382912, coefficient := 6932464678067678377790681382912 }, { argument := 13864928439996259078870191308800, coefficient := (-13864928439996259078870191308800) }, { argument := 4750909977049383867654047006720, coefficient := 4750909977049383867654047006720 }, { argument := 17277299665188084870277962399744, coefficient := 17277299665188084870277962399744 }, { argument := 4750909287583877368685845807104, coefficient := 4750909287583877368685845807104 }, { argument := 26779118929821346106617855213568, coefficient := (-26779118929821346106617855213568) }, { argument := 106847725691629545465531334656, coefficient := 106847725691629545465531334656 }, { argument := 4171473418423230348418168651776, coefficient := 4171473418423230348418168651776 }, { argument := 4171472313389473356921188646912, coefficient := 4171472313389473356921188646912 }, { argument := 106848094036215209297858002944, coefficient := 106848094036215209297858002944 }, { argument := 8556641551540548460102746636288, coefficient := (-8556641551540548460102746636288) }, { argument := 660602402555668929653506048, coefficient := 660602402555668929653506048 }, { argument := 117755457238494817719416782848, coefficient := 117755457238494817719416782848 }, { argument := 1189274579301065925642680270848, coefficient := 1189274579301065925642680270848 }, { argument := 117755683912085995462387040256, coefficient := 117755683912085995462387040256 }, { argument := 660602402555668929653506048, coefficient := 660602402555668929653506048 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk22
