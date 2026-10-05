import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 4, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk4

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
def constantNumerator : ℤ := (-84496637480983944118743397826560)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    501594859683, 24758469175119, 49510522402287, 1005351381549, 84199775931, 2214430112763,
    14389944033939, 276232577985, 20791246983, 84199775931, 97522405359, 1560723548981,
    83690294523, 3582148412703, 176861176083879, 176837549851011, 3590330926007, 97522405359,
    81704972978793, 1063786699665367, 10192222145711, 385360673869, 2214430112763, 81704972978793,
    81723875997985, 2199999529083, 501594859683, 3582148412703, 1003236403611, 1003236403611,
    49520266673083, 24756917593159, 251352007815, 1560723548981, 81723875997985, 532009159332287,
    81556679999993, 1541807670655, 14389944033939, 1063786699665367, 532009159332287, 28604460820357,
    24758469175119, 176861176083879, 49520266673083, 83690294523, 2199999529083, 28604460820357,
    2195447331463, 41329788991, 276232577985, 10192222145711, 81556679999993, 2195447331463,
    49510522402287, 176837549851011, 24756917593159, 20791246983, 385360673869, 1541807670655,
    41329788991, 1005351381549, 3590330926007, 251352007815
  ]
def negativeCoefficients : Array ℕ := #[
    282372802894914378421764096, 13937779068916229984514736128, 13935973140116145478431670272, 282981256707530609230086144, 23700129969220678620020736, 623306664417340764903702528,
    8100818323641246555693907968, 622020467640418738404065280, 23408863041301687295803392, 23700129969220678620020736, 878403736870133724377776128, 878609249202398707761283072,
    23556723701769366392537088, 1008285141039690282505863168, 49781995419229071462969114624, 49775345225882790627656073216, 1010588313781368315384430592, 878403736870133724377776128,
    22997905366350537461185118208, 299429336513414785193583050752, 22950843928750688392947171328, 867755093619835817544384512, 623306664417340764903702528, 22997905366350537461185118208,
    23003226093237366744584028160, 619244816212091592348008448, 282372802894914378421764096, 1008285141039690282505863168, 282385943341688507980578816, 282385943341688507980578816,
    13938715908511511903834472448, 13936905605924118636536004608, 282997202183614999623106560, 878609249202398707761283072, 23003226093237366744584028160, 299494531465822320969115500544,
    22956164603596453657243025408, 867960556379853802553999360, 8100818323641246555693907968, 299429336513414785193583050752, 299494531465822320969115500544, 8051439943230858595183624192,
    13937779068916229984514736128, 49781995419229071462969114624, 13938715908511511903834472448, 23556723701769366392537088, 619244816212091592348008448, 8051439943230858595183624192,
    617963486493019788676169728, 23266602787396103482376192, 622020467640418738404065280, 22950843928750688392947171328, 22956164603596453657243025408, 617963486493019788676169728,
    13935973140116145478431670272, 49775345225882790627656073216, 13936905605924118636536004608, 23408863041301687295803392, 867755093619835817544384512, 867960556379853802553999360,
    23266602787396103482376192, 282981256707530609230086144, 1010588313781368315384430592, 282997202183614999623106560
  ]
def negativeScales : Array ℕ := #[
    38, 44, 45, 39, 36, 41,
    43, 38, 34, 36, 36, 40,
    36, 41, 47, 47, 41, 36,
    46, 49, 43, 38, 41, 46,
    46, 41, 38, 41, 39, 39,
    45, 44, 37, 40, 46, 48,
    46, 40, 43, 49, 48, 44,
    44, 47, 45, 36, 41, 44,
    40, 35, 38, 43, 46, 40,
    45, 47, 44, 34, 38, 40,
    35, 39, 41, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    38867731609736500, 44492987348502502, 45492800405280204, 39870836968804231, 36293097342929366, 41010072605250104,
    43710126214717728, 38007092520220717, 34275257237240176, 36293097342929366, 36505014658883595, 40505352153969068,
    36284341273496230, 41703962249874959, 47329610716086955, 47329417978898241, 41707253964204745, 36505014658883595,
    46215489124311819, 49918130333759479, 43212533861005412, 38487418395599746, 41010072605250104, 46215489124311819,
    46215822863334501, 41000640353584787, 38867731609736500, 41703962249874959, 39867798745158068, 39867798745158068,
    45493084317209640, 44492896933795234, 37870918259743891, 40505352153969068, 46215822863334501, 48918444418570225,
    46212868281020741, 40487759949363292, 43710126214717728, 49918130333759479, 48918444418570225, 44701305384165423,
    44492987348502502, 47329610716086955, 45493084317209640, 36284341273496230, 41000640353584787, 44701305384165423,
    40997652086239880, 35266462946933646, 38007092520220717, 43212533861005412, 46212868281020741, 40997652086239880,
    45492800405280204, 47329417978898241, 44492896933795234, 34275257237240176, 38487418395599746, 40487759949363292,
    35266462946933646, 39870836968804231, 41707253964204745, 37870918259743891
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
noncomputable def negativeCeiling : ℝ := 1013005053 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 282372802894914378421764096, coefficient := (-282372802894914378421764096) }, { argument := 13937779068916229984514736128, coefficient := (-13937779068916229984514736128) }, { argument := 13935973140116145478431670272, coefficient := (-13935973140116145478431670272) }, { argument := 282981256707530609230086144, coefficient := (-282981256707530609230086144) }, { argument := 23700129969220678620020736, coefficient := (-23700129969220678620020736) }, { argument := 623306664417340764903702528, coefficient := (-623306664417340764903702528) }, { argument := 8100818323641246555693907968, coefficient := (-8100818323641246555693907968) }, { argument := 622020467640418738404065280, coefficient := (-622020467640418738404065280) }, { argument := 23408863041301687295803392, coefficient := (-23408863041301687295803392) }, { argument := 23700129969220678620020736, coefficient := (-23700129969220678620020736) }, { argument := 878403736870133724377776128, coefficient := (-878403736870133724377776128) }, { argument := 878609249202398707761283072, coefficient := (-878609249202398707761283072) }, { argument := 23556723701769366392537088, coefficient := (-23556723701769366392537088) }, { argument := 1008285141039690282505863168, coefficient := (-1008285141039690282505863168) }, { argument := 49781995419229071462969114624, coefficient := (-49781995419229071462969114624) }, { argument := 49775345225882790627656073216, coefficient := (-49775345225882790627656073216) }, { argument := 1010588313781368315384430592, coefficient := (-1010588313781368315384430592) }, { argument := 878403736870133724377776128, coefficient := (-878403736870133724377776128) }, { argument := 22997905366350537461185118208, coefficient := (-22997905366350537461185118208) }, { argument := 299429336513414785193583050752, coefficient := (-299429336513414785193583050752) }, { argument := 22950843928750688392947171328, coefficient := (-22950843928750688392947171328) }, { argument := 867755093619835817544384512, coefficient := (-867755093619835817544384512) }, { argument := 623306664417340764903702528, coefficient := (-623306664417340764903702528) }, { argument := 22997905366350537461185118208, coefficient := (-22997905366350537461185118208) }, { argument := 23003226093237366744584028160, coefficient := (-23003226093237366744584028160) }, { argument := 619244816212091592348008448, coefficient := (-619244816212091592348008448) }, { argument := 282372802894914378421764096, coefficient := (-282372802894914378421764096) }, { argument := 1008285141039690282505863168, coefficient := (-1008285141039690282505863168) }, { argument := 282385943341688507980578816, coefficient := (-282385943341688507980578816) }, { argument := 282385943341688507980578816, coefficient := (-282385943341688507980578816) }, { argument := 13938715908511511903834472448, coefficient := (-13938715908511511903834472448) }, { argument := 13936905605924118636536004608, coefficient := (-13936905605924118636536004608) }, { argument := 282997202183614999623106560, coefficient := (-282997202183614999623106560) }, { argument := 878609249202398707761283072, coefficient := (-878609249202398707761283072) }, { argument := 23003226093237366744584028160, coefficient := (-23003226093237366744584028160) }, { argument := 299494531465822320969115500544, coefficient := (-299494531465822320969115500544) }, { argument := 22956164603596453657243025408, coefficient := (-22956164603596453657243025408) }, { argument := 867960556379853802553999360, coefficient := (-867960556379853802553999360) }, { argument := 8100818323641246555693907968, coefficient := (-8100818323641246555693907968) }, { argument := 299429336513414785193583050752, coefficient := (-299429336513414785193583050752) }, { argument := 299494531465822320969115500544, coefficient := (-299494531465822320969115500544) }, { argument := 8051439943230858595183624192, coefficient := (-8051439943230858595183624192) }, { argument := 13937779068916229984514736128, coefficient := (-13937779068916229984514736128) }, { argument := 49781995419229071462969114624, coefficient := (-49781995419229071462969114624) }, { argument := 13938715908511511903834472448, coefficient := (-13938715908511511903834472448) }, { argument := 23556723701769366392537088, coefficient := (-23556723701769366392537088) }, { argument := 619244816212091592348008448, coefficient := (-619244816212091592348008448) }, { argument := 8051439943230858595183624192, coefficient := (-8051439943230858595183624192) }, { argument := 617963486493019788676169728, coefficient := (-617963486493019788676169728) }, { argument := 23266602787396103482376192, coefficient := (-23266602787396103482376192) }, { argument := 622020467640418738404065280, coefficient := (-622020467640418738404065280) }, { argument := 22950843928750688392947171328, coefficient := (-22950843928750688392947171328) }, { argument := 22956164603596453657243025408, coefficient := (-22956164603596453657243025408) }, { argument := 617963486493019788676169728, coefficient := (-617963486493019788676169728) }, { argument := 13935973140116145478431670272, coefficient := (-13935973140116145478431670272) }, { argument := 49775345225882790627656073216, coefficient := (-49775345225882790627656073216) }, { argument := 13936905605924118636536004608, coefficient := (-13936905605924118636536004608) }, { argument := 23408863041301687295803392, coefficient := (-23408863041301687295803392) }, { argument := 867755093619835817544384512, coefficient := (-867755093619835817544384512) }, { argument := 867960556379853802553999360, coefficient := (-867960556379853802553999360) }, { argument := 23266602787396103482376192, coefficient := (-23266602787396103482376192) }, { argument := 282981256707530609230086144, coefficient := (-282981256707530609230086144) }, { argument := 1010588313781368315384430592, coefficient := (-1010588313781368315384430592) }, { argument := 282997202183614999623106560, coefficient := (-282997202183614999623106560) }] }

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

namespace Parent1

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 90528968527806808685888380338176
def positiveArguments : Array ℕ := #[
    11, 6022215, 672175, 6022617, 1989099, 36753209,
    18380641, 1976863, 382069, 10004239, 32561859, 2495941,
    94359, 333105, 16444825, 16442651, 333851
  ]
def positiveCoefficients : Array ℕ := #[
    1743019575313815427057966907392, 56878212537269640901196513280, 203152428199865841377030963200, 56882009319921868095948324864, 18786508897419056849834999808, 694248489278011961179275001856,
    694400983936476787762515673088, 18670943144850270892165431296, 3608539679487044954303234048, 94487365880434673126041714688, 1230152252492218422627152166912, 94293984972961161154540863488,
    3564782231656774821753126912, 3146087774552586337816412160, 155316980793313626702636646400, 155296447943846109485247496192, 3153133545345027848475246592
  ]
def positiveScales : Array ℕ := #[
    3, 22, 19, 22, 20, 25,
    24, 20, 18, 23, 24, 21,
    16, 18, 23, 23, 18
  ]
def negativeArguments : Array ℕ := #[
    1, 9, 9, 1
  ]
def negativeCoefficients : Array ℕ := #[
    316912650057057350374175801344, 1426106925256758076683791106048, 1426106925256758076683791106048, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    0, 3, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3459431618637292, 22521862784177969, 19358477360363393, 22521959084966000, 20923683651649219, 25131366884399175,
    24131683743754480, 20914781462261336, 18543473680678125, 23254108093056179, 24956679730832945, 21251152400954847,
    16525872508780816, 18345617483871068, 23971130318902293, 23970939582527369, 18348844836048204
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 3169925001442313, 3169925001442313, 0
  ]

abbrev PositiveTerm := Fin 17
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 542278389 / 500000000000
noncomputable def negativeCeiling : ℝ := 108830739 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1743019575313815427057966907392, coefficient := 1743019575313815427057966907392 }, { argument := 56878212537269640901196513280, coefficient := 56878212537269640901196513280 }, { argument := 203152428199865841377030963200, coefficient := 203152428199865841377030963200 }, { argument := 56882009319921868095948324864, coefficient := 56882009319921868095948324864 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 18786508897419056849834999808, coefficient := 18786508897419056849834999808 }, { argument := 694248489278011961179275001856, coefficient := 694248489278011961179275001856 }, { argument := 694400983936476787762515673088, coefficient := 694400983936476787762515673088 }, { argument := 18670943144850270892165431296, coefficient := 18670943144850270892165431296 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 3608539679487044954303234048, coefficient := 3608539679487044954303234048 }, { argument := 94487365880434673126041714688, coefficient := 94487365880434673126041714688 }, { argument := 1230152252492218422627152166912, coefficient := 1230152252492218422627152166912 }, { argument := 94293984972961161154540863488, coefficient := 94293984972961161154540863488 }, { argument := 3564782231656774821753126912, coefficient := 3564782231656774821753126912 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 3146087774552586337816412160, coefficient := 3146087774552586337816412160 }, { argument := 155316980793313626702636646400, coefficient := 155316980793313626702636646400 }, { argument := 155296447943846109485247496192, coefficient := 155296447943846109485247496192 }, { argument := 3153133545345027848475246592, coefficient := 3153133545345027848475246592 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk4
