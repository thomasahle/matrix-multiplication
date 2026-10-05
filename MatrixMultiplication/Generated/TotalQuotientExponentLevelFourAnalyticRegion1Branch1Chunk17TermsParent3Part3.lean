import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 17, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-153020775743060635448979697661116416)
def positiveArguments : Array ℕ := #[
    71765, 20835, 36577, 1389, 71765, 1389,
    36577, 36577, 1389, 10323, 47027, 1147,
    492063, 21793, 1147, 21793, 42439, 801753,
    42439, 492063, 801753, 10323, 42439, 42439,
    47027, 441, 2205, 1827, 32823, 12285,
    441, 49203, 49203, 35217, 1827, 61,
    67, 61, 67, 115, 47471133165, 47471132179,
    103757861929, 377763549669, 51875884281, 7072241371, 138235549007, 138235537283,
    7072264065, 5597447, 1670408869, 8244215465, 1670411245, 5597447,
    2862659
  ]
def positiveCoefficients : Array ℕ := #[
    2776273966228603607129239060480, 1612030044906931126720203325440, 2830008301058834644686579171328, 107468669660462075114680221696, 2776273966228603607129239060480, 107468669660462075114680221696,
    2830008301058834644686579171328, 2830008301058834644686579171328, 107468669660462075114680221696, 798703439096436286111478710272, 909634472304274659182517420032, 709958612530165587654647742464,
    9517882649232532409495121297408, 843075852379571635339894194176, 709958612530165587654647742464, 843075852379571635339894194176, 820889645738003960725686452224, 31016316884911609110662423248896,
    820889645738003960725686452224, 9517882649232532409495121297408, 31016316884911609110662423248896, 798703439096436286111478710272, 820889645738003960725686452224, 820889645738003960725686452224,
    909634472304274659182517420032, 34120722332803293826907111424, 682414446656065876538142228480, 35339319558974840035010936832, 634889154835375574422093037568, 950505836413806042320983818240,
    34120722332803293826907111424, 951724433639977588529087643648, 951724433639977588529087643648, 681195849429894330330038403072, 35339319558974840035010936832, 37757171198204098384423288832,
    41470991316060239209120661504, 37757171198204098384423288832, 41470991316060239209120661504, 18222477378280797646515108577280, 224176088162237619275667697827840, 224176083505984267166197517123584,
    489982649507725991787885267779584, 1783937925406748057336457015066624, 489953874395637367826438424625152, 33397715609174467680392987017216, 1305597846743482133861152791199744, 1305597736013432843533711820455936,
    33397822778559429924121466634240, 211465568819513975939736272896, 31553131422615167743364794679296, 311457654315772693198526344069120, 31553176303986220936472905646080, 211465568819513975939736272896,
    27037049826970271395587555328
  ]
def positiveScales : Array ℕ := #[
    16, 14, 15, 10, 16, 10,
    15, 15, 10, 13, 15, 10,
    18, 14, 10, 14, 15, 19,
    15, 18, 19, 13, 15, 15,
    15, 8, 11, 10, 15, 13,
    8, 15, 15, 15, 10, 5,
    6, 5, 6, 6, 35, 35,
    36, 38, 35, 32, 37, 37,
    32, 22, 30, 32, 30, 22,
    21
  ]
def negativeArguments : Array ℕ := #[
    463, 1147, 63, 1, 115, 5659,
    34885, 33801, 4733
  ]
def negativeCoefficients : Array ℕ := #[
    73365278488208776611621698011136, 90874702403861195219794911035392, 4991374238398653268393268871168, 158456325028528675187087900672, 18222477378280797646515108577280, 448352171668221886441865214951424,
    2763874449310111416950780707471360, 2677991121144648874999379065307136, 374986893180013109830243516940288
  ]
def negativeScales : Array ℕ := #[
    8, 10, 5, 0, 6, 12,
    15, 15, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    16130992788534473, 14346721479589910, 15158649131437339, 10439830883981390, 16130992788534473, 10439830883981390,
    15158649131437339, 15158649131437339, 10439830883981390, 13333574677458137, 15521201680633874, 10163649676015824,
    18908483513201369, 14411577189459409, 10163649676015824, 14411577189459409, 15373103041644774, 19612798321390761,
    15373103041644774, 18908483513201369, 19612798321390761, 13333574677458137, 15373103041644774, 15373103041644774,
    15521201680633874, 8784634845528344, 11106562940444882, 10835260918546769, 15002419485778424, 13584610237249298,
    8784634845528344, 15586458661641654, 15586458661641654, 15103984396343106, 10835260918546769, 5930737337099561,
    6066089190457772, 5930737337099561, 6066089190457772, 6845490050846035, 35466331437065523, 35466331407100000,
    36594429700087745, 38458692546840541, 35594344972739575, 32719520367792577, 37008337714342977, 37008337591985468,
    32719524997225738, 22416337532161015, 30637554130984391, 32940735064066118, 30637556183081361, 22416337532161015,
    21448924396032773
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    8854868385160488, 10163649676015826, 5977279939904027, 0, 6845490052533228, 12466331422082852,
    15090319213191611, 15044778308710746, 12208539206738364
  ]

abbrev PositiveTerm := Fin 55
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
noncomputable def positiveFloor : ℝ := 876679213 / 312500000
noncomputable def negativeCeiling : ℝ := 226038488121 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2776273966228603607129239060480, coefficient := 2776273966228603607129239060480 }, { argument := 1612030044906931126720203325440, coefficient := 1612030044906931126720203325440 }, { argument := 2830008301058834644686579171328, coefficient := 2830008301058834644686579171328 }, { argument := 107468669660462075114680221696, coefficient := 107468669660462075114680221696 }, { argument := 2776273966228603607129239060480, coefficient := 2776273966228603607129239060480 }, { argument := 107468669660462075114680221696, coefficient := 107468669660462075114680221696 }, { argument := 2830008301058834644686579171328, coefficient := 2830008301058834644686579171328 }, { argument := 2830008301058834644686579171328, coefficient := 2830008301058834644686579171328 }, { argument := 107468669660462075114680221696, coefficient := 107468669660462075114680221696 }, { argument := 73365278488208776611621698011136, coefficient := (-73365278488208776611621698011136) }, { argument := 798703439096436286111478710272, coefficient := 798703439096436286111478710272 }, { argument := 909634472304274659182517420032, coefficient := 909634472304274659182517420032 }, { argument := 709958612530165587654647742464, coefficient := 709958612530165587654647742464 }, { argument := 9517882649232532409495121297408, coefficient := 9517882649232532409495121297408 }, { argument := 843075852379571635339894194176, coefficient := 843075852379571635339894194176 }, { argument := 709958612530165587654647742464, coefficient := 709958612530165587654647742464 }, { argument := 843075852379571635339894194176, coefficient := 843075852379571635339894194176 }, { argument := 820889645738003960725686452224, coefficient := 820889645738003960725686452224 }, { argument := 31016316884911609110662423248896, coefficient := 31016316884911609110662423248896 }, { argument := 820889645738003960725686452224, coefficient := 820889645738003960725686452224 }, { argument := 9517882649232532409495121297408, coefficient := 9517882649232532409495121297408 }, { argument := 31016316884911609110662423248896, coefficient := 31016316884911609110662423248896 }, { argument := 798703439096436286111478710272, coefficient := 798703439096436286111478710272 }, { argument := 820889645738003960725686452224, coefficient := 820889645738003960725686452224 }, { argument := 820889645738003960725686452224, coefficient := 820889645738003960725686452224 }, { argument := 909634472304274659182517420032, coefficient := 909634472304274659182517420032 }, { argument := 90874702403861195219794911035392, coefficient := (-90874702403861195219794911035392) }, { argument := 34120722332803293826907111424, coefficient := 34120722332803293826907111424 }, { argument := 682414446656065876538142228480, coefficient := 682414446656065876538142228480 }, { argument := 35339319558974840035010936832, coefficient := 35339319558974840035010936832 }, { argument := 634889154835375574422093037568, coefficient := 634889154835375574422093037568 }, { argument := 950505836413806042320983818240, coefficient := 950505836413806042320983818240 }, { argument := 34120722332803293826907111424, coefficient := 34120722332803293826907111424 }, { argument := 951724433639977588529087643648, coefficient := 951724433639977588529087643648 }, { argument := 951724433639977588529087643648, coefficient := 951724433639977588529087643648 }, { argument := 681195849429894330330038403072, coefficient := 681195849429894330330038403072 }, { argument := 35339319558974840035010936832, coefficient := 35339319558974840035010936832 }, { argument := 4991374238398653268393268871168, coefficient := (-4991374238398653268393268871168) }, { argument := 37757171198204098384423288832, coefficient := 37757171198204098384423288832 }, { argument := 41470991316060239209120661504, coefficient := 41470991316060239209120661504 }, { argument := 37757171198204098384423288832, coefficient := 37757171198204098384423288832 }, { argument := 41470991316060239209120661504, coefficient := 41470991316060239209120661504 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 18222477378280797646515108577280, coefficient := 18222477378280797646515108577280 }, { argument := 18222477378280797646515108577280, coefficient := (-18222477378280797646515108577280) }, { argument := 224176088162237619275667697827840, coefficient := 224176088162237619275667697827840 }, { argument := 224176083505984267166197517123584, coefficient := 224176083505984267166197517123584 }, { argument := 448352171668221886441865214951424, coefficient := (-448352171668221886441865214951424) }, { argument := 489982649507725991787885267779584, coefficient := 489982649507725991787885267779584 }, { argument := 1783937925406748057336457015066624, coefficient := 1783937925406748057336457015066624 }, { argument := 489953874395637367826438424625152, coefficient := 489953874395637367826438424625152 }, { argument := 2763874449310111416950780707471360, coefficient := (-2763874449310111416950780707471360) }, { argument := 33397715609174467680392987017216, coefficient := 33397715609174467680392987017216 }, { argument := 1305597846743482133861152791199744, coefficient := 1305597846743482133861152791199744 }, { argument := 1305597736013432843533711820455936, coefficient := 1305597736013432843533711820455936 }, { argument := 33397822778559429924121466634240, coefficient := 33397822778559429924121466634240 }, { argument := 2677991121144648874999379065307136, coefficient := (-2677991121144648874999379065307136) }, { argument := 211465568819513975939736272896, coefficient := 211465568819513975939736272896 }, { argument := 31553131422615167743364794679296, coefficient := 31553131422615167743364794679296 }, { argument := 311457654315772693198526344069120, coefficient := 311457654315772693198526344069120 }, { argument := 31553176303986220936472905646080, coefficient := 31553176303986220936472905646080 }, { argument := 211465568819513975939736272896, coefficient := 211465568819513975939736272896 }, { argument := 374986893180013109830243516940288, coefficient := (-374986893180013109830243516940288) }, { argument := 27037049826970271395587555328, coefficient := 27037049826970271395587555328 }] }

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

end TermShard6


end Parent3

namespace Parent3

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-233953764479134810285774578122752)
def positiveArguments : Array ℕ := #[
    508842429, 508842483, 2862605
  ]
def positiveCoefficients : Array ℕ := #[
    4805880863543154321810593415168, 4805881373558734471732276494336, 27036539811390121473904476160
  ]
def positiveScales : Array ℕ := #[
    28, 28, 21
  ]
def negativeArguments : Array ℕ := #[
    61
  ]
def negativeCoefficients : Array ℕ := #[
    9665835826740249186412361940992
  ]
def negativeScales : Array ℕ := #[
    5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    28922643731118373, 28922643884221815, 21448897181381288
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    5930737345064576
  ]

abbrev PositiveTerm := Fin 3
abbrev NegativeTerm := Fin 1
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
noncomputable def positiveFloor : ℝ := 670650887 / 200000000000
noncomputable def negativeCeiling : ℝ := 69003101 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4805880863543154321810593415168, coefficient := 4805880863543154321810593415168 }, { argument := 4805881373558734471732276494336, coefficient := 4805881373558734471732276494336 }, { argument := 27036539811390121473904476160, coefficient := 27036539811390121473904476160 }, { argument := 9665835826740249186412361940992, coefficient := (-9665835826740249186412361940992) }] }

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

end TermShard7


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17
