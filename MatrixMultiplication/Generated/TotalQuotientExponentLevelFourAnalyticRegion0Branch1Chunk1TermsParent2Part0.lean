import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 1, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk1

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
def constantNumerator : ℤ := (-46831668349860202261608392556544)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    127202490909, 26376381478629, 26381259459711, 63025951365, 8657901549, 392229351577,
    1986182321811, 196116208781, 4328523933, 8657901549, 311015090817, 622222133877,
    17510052015, 411392400289, 85305270438409, 85321046578731, 203835610665, 311015090817,
    28140974056527, 569346693706683, 28141194348393, 1243937983185, 392229351577, 28140974056527,
    28149152934741, 396375099285, 127202490909, 411392400289, 63638017313, 63638017313,
    13195815657353, 13198256058027, 31531195305, 622222133877, 28149152934741, 71187951863367,
    14074686647391, 155540231703, 1986182321811, 569346693706683, 71187951863367, 16048805799285,
    26376381478629, 85305270438409, 13195815657353, 17510052015, 396375099285, 16048805799285,
    792756399525, 35016654735, 196116208781, 28141194348393, 14074686647391, 792756399525,
    26381259459711, 85321046578731, 13198256058027, 4328523933, 1243937983185, 155540231703,
    35016654735, 63025951365, 203835610665, 31531195305
  ]
def negativeCoefficients : Array ℕ := #[
    143217272664592826253705216, 7424291362408476043980570624, 7425664392019927014536380416, 141921825541042501865963520, 9747930547471710028824576, 441610990401487116905218048,
    4472484982198943084999344128, 441614442393712997787762688, 9746969385861536897040384, 9747930547471710028824576, 350171861777510543086583808, 350279921283766509448986624,
    9857282966249000329543680, 463186665161148582735118336, 24011299009947385021861986304, 24015739598677104012910657536, 458996990117865750181969920, 350171861777510543086583808,
    15841960034352224054934503424, 160256847351377592427424514048, 15842084047647927848839151616, 350137414846498269938319360, 441610990401487116905218048, 15841960034352224054934503424,
    15846564333461833938414600192, 446278687359717338869923840, 143217272664592826253705216, 463186665161148582735118336, 143300075528711986556698624, 143300075528711986556698624,
    7428583809663090940639707136, 7429957633108848579050471424, 142003879426144332970721280, 350279921283766509448986624, 15846564333461833938414600192, 160301016742564213788839510016,
    15846688385136650806817193984, 350245464769375704233017344, 4472484982198943084999344128, 160256847351377592427424514048, 160301016742564213788839510016, 4517337238587586326256680960,
    7424291362408476043980570624, 24011299009947385021861986304, 7428583809663090940639707136, 9857282966249000329543680, 446278687359717338869923840, 4517337238587586326256680960,
    446282178187045756521676800, 9856312076019207147356160, 441614442393712997787762688, 15842084047647927848839151616, 15846688385136650806817193984, 446282178187045756521676800,
    7425664392019927014536380416, 24015739598677104012910657536, 7429957633108848579050471424, 9746969385861536897040384, 350137414846498269938319360, 350245464769375704233017344,
    9856312076019207147356160, 141921825541042501865963520, 458996990117865750181969920, 142003879426144332970721280
  ]
def negativeScales : Array ℕ := #[
    36, 44, 44, 35, 33, 38,
    40, 37, 32, 33, 38, 39,
    34, 38, 46, 46, 37, 38,
    44, 49, 44, 40, 38, 44,
    44, 38, 36, 38, 35, 35,
    43, 43, 34, 39, 44, 46,
    43, 37, 40, 49, 46, 43,
    44, 46, 43, 34, 38, 43,
    39, 35, 37, 44, 43, 39,
    44, 46, 43, 32, 40, 37,
    35, 35, 37, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36888335969390529, 44584311891346761, 44584578675039594, 35875226942116957, 33011370249410978, 38512906544080172,
    40853135201772069, 37512917821318984, 32011227990348930, 33011370249410978, 38178193627070730, 39178638759537527,
    34027464318291645, 38581724186760318, 46277700112247652, 46277966895940457, 37568615160241651, 38178193627070730,
    44677737499686414, 49016300752439170, 44677748793280530, 40178051700015801, 38512906544080172, 44677737499686414,
    44678156742909529, 38528075377460587, 36888335969390529, 38581724186760318, 35889169840660502, 35889169840660502,
    43585145762562781, 43585412546255614, 34876060813376088, 39178638759537527, 44678156742909529, 46016698327848573,
    43678168036716312, 37178496836793633, 40853135201772069, 49016300752439170, 46016698327848573, 43867531185534857,
    44584311891346761, 46277700112247652, 43585145762562781, 34027464318291645, 38528075377460587, 43867531185534857,
    39528086662291617, 35027322213463185, 37512917821318984, 44677748793280530, 43678168036716312, 39528086662291617,
    44584578675039594, 46277966895940457, 43585412546255614, 32011227990348930, 40178051700015801, 37178496836793633,
    35027322213463185, 35875226942116957, 37568615160241651, 34876060813376088
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
noncomputable def negativeCeiling : ℝ := 533003271 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 143217272664592826253705216, coefficient := (-143217272664592826253705216) }, { argument := 7424291362408476043980570624, coefficient := (-7424291362408476043980570624) }, { argument := 7425664392019927014536380416, coefficient := (-7425664392019927014536380416) }, { argument := 141921825541042501865963520, coefficient := (-141921825541042501865963520) }, { argument := 9747930547471710028824576, coefficient := (-9747930547471710028824576) }, { argument := 441610990401487116905218048, coefficient := (-441610990401487116905218048) }, { argument := 4472484982198943084999344128, coefficient := (-4472484982198943084999344128) }, { argument := 441614442393712997787762688, coefficient := (-441614442393712997787762688) }, { argument := 9746969385861536897040384, coefficient := (-9746969385861536897040384) }, { argument := 9747930547471710028824576, coefficient := (-9747930547471710028824576) }, { argument := 350171861777510543086583808, coefficient := (-350171861777510543086583808) }, { argument := 350279921283766509448986624, coefficient := (-350279921283766509448986624) }, { argument := 9857282966249000329543680, coefficient := (-9857282966249000329543680) }, { argument := 463186665161148582735118336, coefficient := (-463186665161148582735118336) }, { argument := 24011299009947385021861986304, coefficient := (-24011299009947385021861986304) }, { argument := 24015739598677104012910657536, coefficient := (-24015739598677104012910657536) }, { argument := 458996990117865750181969920, coefficient := (-458996990117865750181969920) }, { argument := 350171861777510543086583808, coefficient := (-350171861777510543086583808) }, { argument := 15841960034352224054934503424, coefficient := (-15841960034352224054934503424) }, { argument := 160256847351377592427424514048, coefficient := (-160256847351377592427424514048) }, { argument := 15842084047647927848839151616, coefficient := (-15842084047647927848839151616) }, { argument := 350137414846498269938319360, coefficient := (-350137414846498269938319360) }, { argument := 441610990401487116905218048, coefficient := (-441610990401487116905218048) }, { argument := 15841960034352224054934503424, coefficient := (-15841960034352224054934503424) }, { argument := 15846564333461833938414600192, coefficient := (-15846564333461833938414600192) }, { argument := 446278687359717338869923840, coefficient := (-446278687359717338869923840) }, { argument := 143217272664592826253705216, coefficient := (-143217272664592826253705216) }, { argument := 463186665161148582735118336, coefficient := (-463186665161148582735118336) }, { argument := 143300075528711986556698624, coefficient := (-143300075528711986556698624) }, { argument := 143300075528711986556698624, coefficient := (-143300075528711986556698624) }, { argument := 7428583809663090940639707136, coefficient := (-7428583809663090940639707136) }, { argument := 7429957633108848579050471424, coefficient := (-7429957633108848579050471424) }, { argument := 142003879426144332970721280, coefficient := (-142003879426144332970721280) }, { argument := 350279921283766509448986624, coefficient := (-350279921283766509448986624) }, { argument := 15846564333461833938414600192, coefficient := (-15846564333461833938414600192) }, { argument := 160301016742564213788839510016, coefficient := (-160301016742564213788839510016) }, { argument := 15846688385136650806817193984, coefficient := (-15846688385136650806817193984) }, { argument := 350245464769375704233017344, coefficient := (-350245464769375704233017344) }, { argument := 4472484982198943084999344128, coefficient := (-4472484982198943084999344128) }, { argument := 160256847351377592427424514048, coefficient := (-160256847351377592427424514048) }, { argument := 160301016742564213788839510016, coefficient := (-160301016742564213788839510016) }, { argument := 4517337238587586326256680960, coefficient := (-4517337238587586326256680960) }, { argument := 7424291362408476043980570624, coefficient := (-7424291362408476043980570624) }, { argument := 24011299009947385021861986304, coefficient := (-24011299009947385021861986304) }, { argument := 7428583809663090940639707136, coefficient := (-7428583809663090940639707136) }, { argument := 9857282966249000329543680, coefficient := (-9857282966249000329543680) }, { argument := 446278687359717338869923840, coefficient := (-446278687359717338869923840) }, { argument := 4517337238587586326256680960, coefficient := (-4517337238587586326256680960) }, { argument := 446282178187045756521676800, coefficient := (-446282178187045756521676800) }, { argument := 9856312076019207147356160, coefficient := (-9856312076019207147356160) }, { argument := 441614442393712997787762688, coefficient := (-441614442393712997787762688) }, { argument := 15842084047647927848839151616, coefficient := (-15842084047647927848839151616) }, { argument := 15846688385136650806817193984, coefficient := (-15846688385136650806817193984) }, { argument := 446282178187045756521676800, coefficient := (-446282178187045756521676800) }, { argument := 7425664392019927014536380416, coefficient := (-7425664392019927014536380416) }, { argument := 24015739598677104012910657536, coefficient := (-24015739598677104012910657536) }, { argument := 7429957633108848579050471424, coefficient := (-7429957633108848579050471424) }, { argument := 9746969385861536897040384, coefficient := (-9746969385861536897040384) }, { argument := 350137414846498269938319360, coefficient := (-350137414846498269938319360) }, { argument := 350245464769375704233017344, coefficient := (-350245464769375704233017344) }, { argument := 9856312076019207147356160, coefficient := (-9856312076019207147356160) }, { argument := 141921825541042501865963520, coefficient := (-141921825541042501865963520) }, { argument := 458996990117865750181969920, coefficient := (-458996990117865750181969920) }, { argument := 142003879426144332970721280, coefficient := (-142003879426144332970721280) }] }

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
def constantNumerator : ℤ := 48178431070814307584321295220736
def positiveArguments : Array ℕ := #[
    3, 3204981, 10365401, 1603417, 284561, 40793361,
    20402355, 1149765, 76239, 1724581, 69784437, 3449189,
    152463, 39689, 8229809, 8231331, 19665
  ]
def positiveCoefficients : Array ℕ := #[
    950737950171172051122527404032, 30270189705268076773273239552, 97898444527807006735379464192, 30287690795453591678435196928, 10750410629854952893236379648, 385282401420003506288446144512,
    385389589694431681495506616320, 10859223398353235258250362880, 1440113993149995525787877376, 65152828091150524898248491008, 659095372629456671255040098304, 65153338106730674819931570176,
    1439972322155509436431466496, 1499408026708906791091044352, 77728348364037904012964528128, 77742723247611759212995018752, 1485845390170105170037309440
  ]
def positiveScales : Array ℕ := #[
    1, 21, 23, 20, 18, 25,
    24, 20, 16, 20, 26, 21,
    17, 15, 22, 22, 14
  ]
def negativeArguments : Array ℕ := #[
    1, 5, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 792281625142643375935439503360, 792281625142643375935439503360, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 2, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 21611884373504043, 23305272594409062, 20612718244719965, 18118378423855404, 25281831041120704,
    24282232353208698, 20132907588772353, 16218241575600786, 20717814460107432, 26056401993391744, 21717825753463221,
    17218099643714744, 15276451592347871, 22972427516903994, 22972694300592695, 14263342565830272
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 2321928094887363, 2321928094887363, 0
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
noncomputable def positiveFloor : ℝ := 23198499 / 40000000000
noncomputable def negativeCeiling : ℝ := 1383977 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 950737950171172051122527404032, coefficient := 950737950171172051122527404032 }, { argument := 30270189705268076773273239552, coefficient := 30270189705268076773273239552 }, { argument := 97898444527807006735379464192, coefficient := 97898444527807006735379464192 }, { argument := 30287690795453591678435196928, coefficient := 30287690795453591678435196928 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 10750410629854952893236379648, coefficient := 10750410629854952893236379648 }, { argument := 385282401420003506288446144512, coefficient := 385282401420003506288446144512 }, { argument := 385389589694431681495506616320, coefficient := 385389589694431681495506616320 }, { argument := 10859223398353235258250362880, coefficient := 10859223398353235258250362880 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 1440113993149995525787877376, coefficient := 1440113993149995525787877376 }, { argument := 65152828091150524898248491008, coefficient := 65152828091150524898248491008 }, { argument := 659095372629456671255040098304, coefficient := 659095372629456671255040098304 }, { argument := 65153338106730674819931570176, coefficient := 65153338106730674819931570176 }, { argument := 1439972322155509436431466496, coefficient := 1439972322155509436431466496 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 1499408026708906791091044352, coefficient := 1499408026708906791091044352 }, { argument := 77728348364037904012964528128, coefficient := 77728348364037904012964528128 }, { argument := 77742723247611759212995018752, coefficient := 77742723247611759212995018752 }, { argument := 1485845390170105170037309440, coefficient := 1485845390170105170037309440 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk1
