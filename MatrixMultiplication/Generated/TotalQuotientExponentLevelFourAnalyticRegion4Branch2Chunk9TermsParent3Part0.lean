import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 9, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk9

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 475368975085586025561263702016
def positiveArguments : Array ℕ := #[
    1, 2873935, 11029279, 1437001, 89091, 8210441,
    2052607, 178165, 33993, 1187969, 14333263, 1187997,
    16997
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 27143548635891947634446827520, 104168594959636075385735610368, 27144181433000652166905462784, 3365762818602716493867122688, 155090845551914930871933599744,
    155090599988857821650382487552, 3365441697681881357992591360, 321054807704375699498336256, 11220049976576339109738446848, 135373841562711239129191940096, 11220314429099379809870413824,
    321064252437341438788763648
  ]
def positiveScales : Array ℕ := #[
    0, 21, 23, 20, 16, 22,
    20, 17, 15, 20, 23, 20,
    14
  ]
def negativeArguments : Array ℕ := #[
    97693672455, 3414145688015, 41192866199905, 3414226158195, 48848273195, 7937206281,
    731476399131, 182868810237, 15872898015, 97693672455, 374918281047, 48847974993,
    374918281047, 13102441544351, 158085556607377, 13102750364163, 187464655163, 731476399131,
    67411341414481, 16852808669687, 1462813220765, 3414145688015, 13102441544351, 1707112640969,
    48847974993, 1707112640969, 20596913264263, 1707152876997, 24424705997, 182868810237,
    16852808669687, 4213195496449, 365702726155, 41192866199905, 158085556607377, 20596913264263,
    15872898015, 1462813220765, 365702726155, 31742767225, 3414226158195, 13102750364163,
    1707152876997, 48848273195, 187464655163, 24424705997, 1, 1,
    1
  ]
def negativeCoefficients : Array ℕ := #[
    27498324179049580572180480, 960996578020808730701987840, 11594761054263428599439687680, 961019228362850132998225920, 27499133119836773511331840, 17872999624737180182642688,
    823569209639170951027359744, 823567905641039144316567552, 17871294396410971406991360, 27498324179049580572180480, 105530114426103505807736832, 27498965247034763369250816,
    105530114426103505807736832, 3688009428548929358718304256, 44497128364352531814324109312, 3688096353598319847882620928, 105533218892153166135033856, 823569209639170951027359744,
    37949211509350239543410819072, 37949151422474318803816677376, 823490634493736137711943680, 960996578020808730701987840, 3688009428548929358718304256, 961018981718431465448931328,
    27498965247034763369250816, 961018981718431465448931328, 11595031362739659150832173056, 961041632588519924054360064, 27499774206680779748016128, 823567905641039144316567552,
    37949151422474318803816677376, 37949091335693536606350737408, 823489330620016270707261440, 11594761054263428599439687680, 44497128364352531814324109312, 11595031362739659150832173056,
    17871294396410971406991360, 823490634493736137711943680, 823489330620016270707261440, 17869589330777299170099200, 961019228362850132998225920, 3688096353598319847882620928,
    961041632588519924054360064, 27499133119836773511331840, 105533218892153166135033856, 27499774206680779748016128, 158456325028528675187087900672, 316912650057057350374175801344,
    158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    36, 41, 45, 41, 35, 32,
    39, 37, 33, 36, 38, 35,
    38, 43, 47, 43, 37, 39,
    45, 43, 40, 41, 43, 40,
    35, 40, 44, 40, 34, 37,
    43, 41, 38, 45, 47, 44,
    33, 40, 38, 34, 41, 43,
    40, 35, 37, 34, 0, 0,
    0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 21454596001948191, 23394835147151449, 20454629635082216, 16442992077164403, 22969028282700040,
    20969025998407381, 17442854425854227, 15052950069882485, 20180065758888953, 23772863743993937, 20180099762288957,
    14052992510203163
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    36507546071831029, 41634661760851500, 45227459745964928, 41634695764251517, 35507588512151708, 32885984157718580,
    39412020360748205, 37412018076455513, 33885846506399903, 36507546071831029, 38447785217033979, 35507579704965054,
    38447785217033979, 43574900906043184, 47167698891168183, 43574934909443191, 37447827657354657, 39412020360748205,
    45938056575675662, 43938054291382637, 40411882709438029, 41634661760851500, 43574900906043184, 40634695393985538,
    35507579704965054, 40634695393985538, 44227493379098953, 40634729397385554, 34507622145285733, 37412018076455513,
    43938054291382637, 41938052007089611, 38411880425145336, 45227459745964928, 47167698891168183, 44227493379098953,
    33885846506399903, 40411882709438029, 38411880425145336, 34885708855081245, 41634695764251517, 43574934909443191,
    40634729397385554, 35507588512151708, 37447827657354657, 34507622145285733, 0, 0,
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
noncomputable def positiveFloor : ℝ := 85363433 / 500000000000
noncomputable def negativeCeiling : ℝ := 170726867 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 27498324179049580572180480, coefficient := (-27498324179049580572180480) }, { argument := 960996578020808730701987840, coefficient := (-960996578020808730701987840) }, { argument := 11594761054263428599439687680, coefficient := (-11594761054263428599439687680) }, { argument := 961019228362850132998225920, coefficient := (-961019228362850132998225920) }, { argument := 27499133119836773511331840, coefficient := (-27499133119836773511331840) }, { argument := 17872999624737180182642688, coefficient := (-17872999624737180182642688) }, { argument := 823569209639170951027359744, coefficient := (-823569209639170951027359744) }, { argument := 823567905641039144316567552, coefficient := (-823567905641039144316567552) }, { argument := 17871294396410971406991360, coefficient := (-17871294396410971406991360) }, { argument := 27498324179049580572180480, coefficient := (-27498324179049580572180480) }, { argument := 105530114426103505807736832, coefficient := (-105530114426103505807736832) }, { argument := 27498965247034763369250816, coefficient := (-27498965247034763369250816) }, { argument := 105530114426103505807736832, coefficient := (-105530114426103505807736832) }, { argument := 3688009428548929358718304256, coefficient := (-3688009428548929358718304256) }, { argument := 44497128364352531814324109312, coefficient := (-44497128364352531814324109312) }, { argument := 3688096353598319847882620928, coefficient := (-3688096353598319847882620928) }, { argument := 105533218892153166135033856, coefficient := (-105533218892153166135033856) }, { argument := 823569209639170951027359744, coefficient := (-823569209639170951027359744) }, { argument := 37949211509350239543410819072, coefficient := (-37949211509350239543410819072) }, { argument := 37949151422474318803816677376, coefficient := (-37949151422474318803816677376) }, { argument := 823490634493736137711943680, coefficient := (-823490634493736137711943680) }, { argument := 960996578020808730701987840, coefficient := (-960996578020808730701987840) }, { argument := 3688009428548929358718304256, coefficient := (-3688009428548929358718304256) }, { argument := 961018981718431465448931328, coefficient := (-961018981718431465448931328) }, { argument := 27498965247034763369250816, coefficient := (-27498965247034763369250816) }, { argument := 961018981718431465448931328, coefficient := (-961018981718431465448931328) }, { argument := 11595031362739659150832173056, coefficient := (-11595031362739659150832173056) }, { argument := 961041632588519924054360064, coefficient := (-961041632588519924054360064) }, { argument := 27499774206680779748016128, coefficient := (-27499774206680779748016128) }, { argument := 823567905641039144316567552, coefficient := (-823567905641039144316567552) }, { argument := 37949151422474318803816677376, coefficient := (-37949151422474318803816677376) }, { argument := 37949091335693536606350737408, coefficient := (-37949091335693536606350737408) }, { argument := 823489330620016270707261440, coefficient := (-823489330620016270707261440) }, { argument := 11594761054263428599439687680, coefficient := (-11594761054263428599439687680) }, { argument := 44497128364352531814324109312, coefficient := (-44497128364352531814324109312) }, { argument := 11595031362739659150832173056, coefficient := (-11595031362739659150832173056) }, { argument := 17871294396410971406991360, coefficient := (-17871294396410971406991360) }, { argument := 823490634493736137711943680, coefficient := (-823490634493736137711943680) }, { argument := 823489330620016270707261440, coefficient := (-823489330620016270707261440) }, { argument := 17869589330777299170099200, coefficient := (-17869589330777299170099200) }, { argument := 961019228362850132998225920, coefficient := (-961019228362850132998225920) }, { argument := 3688096353598319847882620928, coefficient := (-3688096353598319847882620928) }, { argument := 961041632588519924054360064, coefficient := (-961041632588519924054360064) }, { argument := 27499133119836773511331840, coefficient := (-27499133119836773511331840) }, { argument := 105533218892153166135033856, coefficient := (-105533218892153166135033856) }, { argument := 27499774206680779748016128, coefficient := (-27499774206680779748016128) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 27143548635891947634446827520, coefficient := 27143548635891947634446827520 }, { argument := 104168594959636075385735610368, coefficient := 104168594959636075385735610368 }, { argument := 27144181433000652166905462784, coefficient := 27144181433000652166905462784 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 3365762818602716493867122688, coefficient := 3365762818602716493867122688 }, { argument := 155090845551914930871933599744, coefficient := 155090845551914930871933599744 }, { argument := 155090599988857821650382487552, coefficient := 155090599988857821650382487552 }, { argument := 3365441697681881357992591360, coefficient := 3365441697681881357992591360 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 321054807704375699498336256, coefficient := 321054807704375699498336256 }, { argument := 11220049976576339109738446848, coefficient := 11220049976576339109738446848 }, { argument := 135373841562711239129191940096, coefficient := 135373841562711239129191940096 }, { argument := 11220314429099379809870413824, coefficient := 11220314429099379809870413824 }, { argument := 321064252437341438788763648, coefficient := 321064252437341438788763648 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk9
