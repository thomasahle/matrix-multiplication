import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 19, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19

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
def constantNumerator : ℤ := (-16907731792857563623375656267546624)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5353187, 479705413, 22721, 2196381783, 12061, 873,
    22721, 22655, 12061, 280955, 1401, 239852709,
    22721, 873, 1401, 873, 11361, 22655,
    183151, 216950759081629, 2451, 7746969718140259, 38571, 1161,
    61973659996578741, 1161, 1161, 99459, 1161, 38571,
    99459, 1737703829109835, 1161, 1161, 2451, 35911920654740747,
    10181229849, 571979205, 64517915314368169, 30925009017, 35911918520849827, 30925009017,
    30925009017, 10181229849, 571979205, 126070853, 2206082767, 2206083849,
    126069771, 4778944623, 8099665809, 4778944623, 108783512007757, 126070853,
    108783485826995, 126070853, 268480035, 455037405, 268480035, 19,
    19, 5350235, 216950706803043, 2451
  ]
def negativeCoefficients : Array ℕ := #[
    25279710865333507452569649152, 2265344764002340582399512936448, 439488056759423831655984398336, 20744239431249340622070072999936, 233293668965952679618099019776, 16886275848377140312295866368,
    439488056759423831655984398336, 438211431093910783247494676480, 233293668965952679618099019776, 5434460058397250236473178849280, 433588498759704441283418259456, 2265344787614172996747739004928,
    439488056759423831655984398336, 16886275848377140312295866368, 433588498759704441283418259456, 16886275848377140312295866368, 439507399572537665722779697152, 438211431093910783247494676480,
    27676996598529868497076355072, 1954118715515541230778180435968, 94818469884014595430554796032, 69778499871733973717550972796928, 746071644613693790361470631936, 89828024100645406197367701504,
    69776138016844458094455511056384, 89828024100645406197367701504, 89828024100645406197367701504, 3847633698977644898787249881088, 89828024100645406197367701504, 746071644613693790361470631936,
    3847633698977644898787249881088, 1956480579314834241475355607040, 89828024100645406197367701504, 89828024100645406197367701504, 94818469884014595430554796032, 20216614059856155865725024600064,
    93905270690057771534612692992, 5275577005059425367113072640, 72640714842127425800346278035456, 142616431703439799090956730368, 20216612858582361845564413313024, 142616431703439799090956730368,
    142616431703439799090956730368, 93905270690057771534612692992, 5275577005059425367113072640, 1162798380222629023238324224, 40695044208270019583354601472, 40695064167647107337089449984,
    1162788400534085146370899968, 88155968402911377359024160768, 298824924522397262041671794688, 88155968402911377359024160768, 1959669536568753209485859749888, 1162798380222629023238324224,
    1959669064938073259583293358080, 1162798380222629023238324224, 4952582494545582997697986560, 16787917107999846182116392960, 4952582494545582997697986560, 94083442985688900892333441024,
    94083442985688900892333441024, 25265770439476076259898818560, 1954118244631900372665322438656, 94818469884014595430554796032
  ]
def negativeScales : Array ℕ := #[
    22, 28, 14, 31, 13, 9,
    14, 14, 13, 18, 10, 27,
    14, 9, 10, 9, 13, 14,
    17, 47, 11, 52, 15, 10,
    55, 10, 10, 16, 10, 15,
    16, 50, 10, 10, 11, 54,
    33, 29, 55, 34, 54, 34,
    34, 33, 29, 26, 31, 31,
    26, 32, 32, 32, 46, 26,
    46, 26, 28, 28, 28, 4,
    4, 22, 47, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    22351966619746648, 28837573479477134, 14471738711896213, 31032481704580425, 13558061908284247, 9769837843974277,
    14471738711896213, 14467541870400840, 13558061908284247, 18099979549809284, 10452241240430869, 27837573494514436,
    14471738711896213, 9769837843974277, 10452241240430869, 9769837843974277, 13471802206605679, 14467541870400840,
    17482674052584731, 47624360962394092, 11259154768866840, 52782553524144841, 15235228929621360, 10181152256865567,
    55782504691136919, 10181152256865567, 10181152256865567, 16601814305344234, 10181152256865567, 15235228929621360,
    16601814305344234, 50626103636265244, 10181152256865567, 10181152256865567, 11259154768866840, 54995312353985253,
    33245192792201307, 29091387456122272, 55840549342912606, 34848054966399943, 54995312268260096, 34848054966399943,
    34848054966399943, 33245192792201307, 29091387456122272, 26909659534061884, 31038839772431639, 31038840480018714,
    26909647152112851, 32154044904143112, 32915215243552797, 32154044904143112, 46628453236611522, 26909659534061884,
    46628452889400264, 26909659534061884, 28000239568064076, 28761409902038808, 28000239568064076, 4247927513443586,
    4247927513443586, 22351170830162963, 47624360614748082, 11259154768866840
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
noncomputable def negativeCeiling : ℝ := 37192768797 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 25279710865333507452569649152, coefficient := (-25279710865333507452569649152) }, { argument := 2265344764002340582399512936448, coefficient := (-2265344764002340582399512936448) }, { argument := 439488056759423831655984398336, coefficient := (-439488056759423831655984398336) }, { argument := 20744239431249340622070072999936, coefficient := (-20744239431249340622070072999936) }, { argument := 233293668965952679618099019776, coefficient := (-233293668965952679618099019776) }, { argument := 16886275848377140312295866368, coefficient := (-16886275848377140312295866368) }, { argument := 439488056759423831655984398336, coefficient := (-439488056759423831655984398336) }, { argument := 438211431093910783247494676480, coefficient := (-438211431093910783247494676480) }, { argument := 233293668965952679618099019776, coefficient := (-233293668965952679618099019776) }, { argument := 5434460058397250236473178849280, coefficient := (-5434460058397250236473178849280) }, { argument := 433588498759704441283418259456, coefficient := (-433588498759704441283418259456) }, { argument := 2265344787614172996747739004928, coefficient := (-2265344787614172996747739004928) }, { argument := 439488056759423831655984398336, coefficient := (-439488056759423831655984398336) }, { argument := 16886275848377140312295866368, coefficient := (-16886275848377140312295866368) }, { argument := 433588498759704441283418259456, coefficient := (-433588498759704441283418259456) }, { argument := 16886275848377140312295866368, coefficient := (-16886275848377140312295866368) }, { argument := 439507399572537665722779697152, coefficient := (-439507399572537665722779697152) }, { argument := 438211431093910783247494676480, coefficient := (-438211431093910783247494676480) }, { argument := 27676996598529868497076355072, coefficient := (-27676996598529868497076355072) }, { argument := 1954118715515541230778180435968, coefficient := (-1954118715515541230778180435968) }, { argument := 94818469884014595430554796032, coefficient := (-94818469884014595430554796032) }, { argument := 69778499871733973717550972796928, coefficient := (-69778499871733973717550972796928) }, { argument := 746071644613693790361470631936, coefficient := (-746071644613693790361470631936) }, { argument := 89828024100645406197367701504, coefficient := (-89828024100645406197367701504) }, { argument := 69776138016844458094455511056384, coefficient := (-69776138016844458094455511056384) }, { argument := 89828024100645406197367701504, coefficient := (-89828024100645406197367701504) }, { argument := 89828024100645406197367701504, coefficient := (-89828024100645406197367701504) }, { argument := 3847633698977644898787249881088, coefficient := (-3847633698977644898787249881088) }, { argument := 89828024100645406197367701504, coefficient := (-89828024100645406197367701504) }, { argument := 746071644613693790361470631936, coefficient := (-746071644613693790361470631936) }, { argument := 3847633698977644898787249881088, coefficient := (-3847633698977644898787249881088) }, { argument := 1956480579314834241475355607040, coefficient := (-1956480579314834241475355607040) }, { argument := 89828024100645406197367701504, coefficient := (-89828024100645406197367701504) }, { argument := 89828024100645406197367701504, coefficient := (-89828024100645406197367701504) }, { argument := 94818469884014595430554796032, coefficient := (-94818469884014595430554796032) }, { argument := 20216614059856155865725024600064, coefficient := (-20216614059856155865725024600064) }, { argument := 93905270690057771534612692992, coefficient := (-93905270690057771534612692992) }, { argument := 5275577005059425367113072640, coefficient := (-5275577005059425367113072640) }, { argument := 72640714842127425800346278035456, coefficient := (-72640714842127425800346278035456) }, { argument := 142616431703439799090956730368, coefficient := (-142616431703439799090956730368) }, { argument := 20216612858582361845564413313024, coefficient := (-20216612858582361845564413313024) }, { argument := 142616431703439799090956730368, coefficient := (-142616431703439799090956730368) }, { argument := 142616431703439799090956730368, coefficient := (-142616431703439799090956730368) }, { argument := 93905270690057771534612692992, coefficient := (-93905270690057771534612692992) }, { argument := 5275577005059425367113072640, coefficient := (-5275577005059425367113072640) }, { argument := 1162798380222629023238324224, coefficient := (-1162798380222629023238324224) }, { argument := 40695044208270019583354601472, coefficient := (-40695044208270019583354601472) }, { argument := 40695064167647107337089449984, coefficient := (-40695064167647107337089449984) }, { argument := 1162788400534085146370899968, coefficient := (-1162788400534085146370899968) }, { argument := 88155968402911377359024160768, coefficient := (-88155968402911377359024160768) }, { argument := 298824924522397262041671794688, coefficient := (-298824924522397262041671794688) }, { argument := 88155968402911377359024160768, coefficient := (-88155968402911377359024160768) }, { argument := 1959669536568753209485859749888, coefficient := (-1959669536568753209485859749888) }, { argument := 1162798380222629023238324224, coefficient := (-1162798380222629023238324224) }, { argument := 1959669064938073259583293358080, coefficient := (-1959669064938073259583293358080) }, { argument := 1162798380222629023238324224, coefficient := (-1162798380222629023238324224) }, { argument := 4952582494545582997697986560, coefficient := (-4952582494545582997697986560) }, { argument := 16787917107999846182116392960, coefficient := (-16787917107999846182116392960) }, { argument := 4952582494545582997697986560, coefficient := (-4952582494545582997697986560) }, { argument := 94083442985688900892333441024, coefficient := (-94083442985688900892333441024) }, { argument := 94083442985688900892333441024, coefficient := (-94083442985688900892333441024) }, { argument := 25265770439476076259898818560, coefficient := (-25265770439476076259898818560) }, { argument := 1954118244631900372665322438656, coefficient := (-1954118244631900372665322438656) }, { argument := 94818469884014595430554796032, coefficient := (-94818469884014595430554796032) }] }

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
def constantNumerator : ℤ := (-51274143639060291969022170109050880)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    7746967787561629, 38571, 1161, 61973644551953483, 1161, 1161,
    99459, 1161, 38571, 99459, 1737703410877365, 1161,
    1161, 2451, 64514345533816489, 17255809767, 969427515, 115911853267232163,
    52413714311, 64514341871179281, 52413714311, 52413714311, 17255809767, 969427515,
    3886305368671667, 2206082767, 3886304401850957, 2206082767, 14515820559, 24602355697,
    14515820559, 299, 299, 482159645, 9, 9,
    22539, 35911918520849827, 10181229849, 571979205, 64517911651730961, 30925009017,
    35911916386958907, 30925009017, 30925009017, 10181229849, 571979205, 31089387585464805,
    2206083849, 31089379850901019, 2206083849, 276291361, 9, 9,
    11965, 433, 126070853, 2206082767, 2206083849, 126069771,
    14515820559, 24602355697, 14515820559, 9
  ]
def negativeCoefficients : Array ℕ := #[
    69778482482627576362665632595968, 746071644613693790361470631936, 89828024100645406197367701504, 69776120627742318893017849659392, 89828024100645406197367701504, 89828024100645406197367701504,
    3847633698977644898787249881088, 89828024100645406197367701504, 746071644613693790361470631936, 3847633698977644898787249881088, 1956480108426935229914818805760, 89828024100645406197367701504,
    89828024100645406197367701504, 94818469884014595430554796032, 72636695626536840677436619227136, 318313506556466648696563433472, 17882781267217227454863114240, 261010289591065189298649824231424,
    483431186923772382196466188288, 72636691502773949391908156473344, 483431186923772382196466188288, 483431186923772382196466188288, 318313506556466648696563433472, 17882781267217227454863114240,
    70009453640790710322158347747328, 40695044208270019583354601472, 70009436224097153161844844658688, 40695044208270019583354601472, 133884813435882260371102236672, 453833359152929175123213156352,
    133884813435882260371102236672, 740288143492657404389676285952, 740288143492657404389676285952, 2276934546940326717511612497920, 89131682828547379792736944128, 89131682828547379792736944128,
    435967664772706031499240013824, 20216612858582361845564413313024, 93905270690057771534612692992, 5275577005059425367113072640, 72640710718364534514817815281664, 142616431703439799090956730368,
    20216611657308567825403802025984, 142616431703439799090956730368, 142616431703439799090956730368, 93905270690057771534612692992, 5275577005059425367113072640, 70007077172538110081246051696640,
    40695064167647107337089449984, 70007059755848817829779668467712, 40695064167647107337089449984, 20875985003085399386867258884096, 89131682828547379792736944128, 89131682828547379792736944128,
    231436758907024609205750333440, 16750876156580301844728774656, 1162798380222629023238324224, 40695044208270019583354601472, 40695064167647107337089449984, 1162788400534085146370899968,
    133884813435882260371102236672, 453833359152929175123213156352, 133884813435882260371102236672, 89131682828547379792736944128
  ]
def negativeScales : Array ℕ := #[
    52, 15, 10, 55, 10, 10,
    16, 10, 15, 16, 50, 10,
    10, 11, 55, 34, 29, 56,
    35, 55, 35, 35, 34, 29,
    51, 31, 51, 31, 33, 34,
    33, 8, 8, 28, 3, 3,
    14, 54, 33, 29, 55, 34,
    54, 34, 34, 33, 29, 54,
    31, 54, 31, 28, 3, 3,
    13, 8, 26, 31, 31, 26,
    33, 34, 33, 3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    52782553164618899, 15235228929621360, 10181152256865567, 55782504331598895, 10181152256865567, 10181152256865567,
    16601814305344234, 10181152256865567, 15235228929621360, 16601814305344234, 50626103289035772, 10181152256865567,
    10181152256865567, 11259154768866840, 55840469516289247, 34006363125888053, 29852557791627662, 56685805718527434,
    35609225298425057, 55840469434383916, 35609225298425057, 35609225298425057, 34006363125888053, 29852557791627662,
    51787320689775048, 31038839772431639, 51787320330866650, 31038839772431639, 33756907076934159, 34518077410360067,
    33756907076934159, 8224001674198106, 8224001674198106, 28844935668362284, 3169925001442313, 3169925001442313,
    14460135887648612, 54995312268260096, 33245192792201307, 29091387456122272, 55840549261011807, 34848054966399943,
    54995312182534935, 34848054966399943, 34848054966399943, 33245192792201307, 29091387456122272, 54787271716714815,
    31038840480018714, 54787271357794322, 31038840480018714, 28041615212174719, 3169925001442313, 3169925001442313,
    13546532776427058, 8758223214995597, 26909659534061884, 31038839772431639, 31038840480018714, 26909647152112851,
    33756907076934159, 34518077410360067, 33756907076934159, 3169925001442313
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
noncomputable def negativeCeiling : ℝ := 635176872741 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 69778482482627576362665632595968, coefficient := (-69778482482627576362665632595968) }, { argument := 746071644613693790361470631936, coefficient := (-746071644613693790361470631936) }, { argument := 89828024100645406197367701504, coefficient := (-89828024100645406197367701504) }, { argument := 69776120627742318893017849659392, coefficient := (-69776120627742318893017849659392) }, { argument := 89828024100645406197367701504, coefficient := (-89828024100645406197367701504) }, { argument := 89828024100645406197367701504, coefficient := (-89828024100645406197367701504) }, { argument := 3847633698977644898787249881088, coefficient := (-3847633698977644898787249881088) }, { argument := 89828024100645406197367701504, coefficient := (-89828024100645406197367701504) }, { argument := 746071644613693790361470631936, coefficient := (-746071644613693790361470631936) }, { argument := 3847633698977644898787249881088, coefficient := (-3847633698977644898787249881088) }, { argument := 1956480108426935229914818805760, coefficient := (-1956480108426935229914818805760) }, { argument := 89828024100645406197367701504, coefficient := (-89828024100645406197367701504) }, { argument := 89828024100645406197367701504, coefficient := (-89828024100645406197367701504) }, { argument := 94818469884014595430554796032, coefficient := (-94818469884014595430554796032) }, { argument := 72636695626536840677436619227136, coefficient := (-72636695626536840677436619227136) }, { argument := 318313506556466648696563433472, coefficient := (-318313506556466648696563433472) }, { argument := 17882781267217227454863114240, coefficient := (-17882781267217227454863114240) }, { argument := 261010289591065189298649824231424, coefficient := (-261010289591065189298649824231424) }, { argument := 483431186923772382196466188288, coefficient := (-483431186923772382196466188288) }, { argument := 72636691502773949391908156473344, coefficient := (-72636691502773949391908156473344) }, { argument := 483431186923772382196466188288, coefficient := (-483431186923772382196466188288) }, { argument := 483431186923772382196466188288, coefficient := (-483431186923772382196466188288) }, { argument := 318313506556466648696563433472, coefficient := (-318313506556466648696563433472) }, { argument := 17882781267217227454863114240, coefficient := (-17882781267217227454863114240) }, { argument := 70009453640790710322158347747328, coefficient := (-70009453640790710322158347747328) }, { argument := 40695044208270019583354601472, coefficient := (-40695044208270019583354601472) }, { argument := 70009436224097153161844844658688, coefficient := (-70009436224097153161844844658688) }, { argument := 40695044208270019583354601472, coefficient := (-40695044208270019583354601472) }, { argument := 133884813435882260371102236672, coefficient := (-133884813435882260371102236672) }, { argument := 453833359152929175123213156352, coefficient := (-453833359152929175123213156352) }, { argument := 133884813435882260371102236672, coefficient := (-133884813435882260371102236672) }, { argument := 740288143492657404389676285952, coefficient := (-740288143492657404389676285952) }, { argument := 740288143492657404389676285952, coefficient := (-740288143492657404389676285952) }, { argument := 2276934546940326717511612497920, coefficient := (-2276934546940326717511612497920) }, { argument := 89131682828547379792736944128, coefficient := (-89131682828547379792736944128) }, { argument := 89131682828547379792736944128, coefficient := (-89131682828547379792736944128) }, { argument := 435967664772706031499240013824, coefficient := (-435967664772706031499240013824) }, { argument := 20216612858582361845564413313024, coefficient := (-20216612858582361845564413313024) }, { argument := 93905270690057771534612692992, coefficient := (-93905270690057771534612692992) }, { argument := 5275577005059425367113072640, coefficient := (-5275577005059425367113072640) }, { argument := 72640710718364534514817815281664, coefficient := (-72640710718364534514817815281664) }, { argument := 142616431703439799090956730368, coefficient := (-142616431703439799090956730368) }, { argument := 20216611657308567825403802025984, coefficient := (-20216611657308567825403802025984) }, { argument := 142616431703439799090956730368, coefficient := (-142616431703439799090956730368) }, { argument := 142616431703439799090956730368, coefficient := (-142616431703439799090956730368) }, { argument := 93905270690057771534612692992, coefficient := (-93905270690057771534612692992) }, { argument := 5275577005059425367113072640, coefficient := (-5275577005059425367113072640) }, { argument := 70007077172538110081246051696640, coefficient := (-70007077172538110081246051696640) }, { argument := 40695064167647107337089449984, coefficient := (-40695064167647107337089449984) }, { argument := 70007059755848817829779668467712, coefficient := (-70007059755848817829779668467712) }, { argument := 40695064167647107337089449984, coefficient := (-40695064167647107337089449984) }, { argument := 20875985003085399386867258884096, coefficient := (-20875985003085399386867258884096) }, { argument := 89131682828547379792736944128, coefficient := (-89131682828547379792736944128) }, { argument := 89131682828547379792736944128, coefficient := (-89131682828547379792736944128) }, { argument := 231436758907024609205750333440, coefficient := (-231436758907024609205750333440) }, { argument := 16750876156580301844728774656, coefficient := (-16750876156580301844728774656) }, { argument := 1162798380222629023238324224, coefficient := (-1162798380222629023238324224) }, { argument := 40695044208270019583354601472, coefficient := (-40695044208270019583354601472) }, { argument := 40695064167647107337089449984, coefficient := (-40695064167647107337089449984) }, { argument := 1162788400534085146370899968, coefficient := (-1162788400534085146370899968) }, { argument := 133884813435882260371102236672, coefficient := (-133884813435882260371102236672) }, { argument := 453833359152929175123213156352, coefficient := (-453833359152929175123213156352) }, { argument := 133884813435882260371102236672, coefficient := (-133884813435882260371102236672) }, { argument := 89131682828547379792736944128, coefficient := (-89131682828547379792736944128) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19
