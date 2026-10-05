import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 18, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-36013656181225491361827435510235136)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    65846229174749255, 73665049815, 2797406955, 144532692675, 2797406955, 73665049815,
    73665049815, 100599714125133, 6031138280233173, 414174096635, 221419761654671805, 4333675303815,
    191934337465, 221419721361961479, 191934337465, 373766867695, 7061163257265, 373766867695,
    4333675303815, 7061163257265, 6031151874714471, 373766867695, 373766867695, 414174096635,
    26763165, 1096491825, 22577615775, 1096491825, 26763165, 874211481,
    136852904331, 34213238631, 3496896117, 4535381651064595, 5963825, 4941455,
    16426587708082505, 33227025, 1133826256309225, 133078495, 133078495, 95250805,
    4941455, 38717991, 6061084341, 1515271641, 154874187, 157599613701,
    585443290635, 9847902447, 359940353323925, 3149, 359940289563755, 3149,
    27522768544953, 4544672120929605, 1239140043, 81398028729547311, 392132925, 47055951,
    1239140043, 2462594769, 392132925, 38005523091
  ]
def negativeCoefficients : Array ℕ := #[
    18534065823447064197553486561280, 2717760642228740303267907502080, 103206100337800264681059778560, 2666157592059840170927377612800, 103206100337800264681059778560, 2717760642228740303267907502080,
    2717760642228740303267907502080, 226530417523763700904948137984, 6790458027869513001024935165952, 477510222661605837120481525760, 249296489020110994954856505016320, 4996387451751924490846014013440,
    442570450271732239282397511680, 249296443654552192474622403280896, 442570450271732239282397511680, 430923859475107706669702840320, 16281933933681096592547150561280, 430923859475107706669702840320,
    4996387451751924490846014013440, 16281933933681096592547150561280, 6790473333894739993019132411904, 430923859475107706669702840320, 430923859475107706669702840320, 477510222661605837120481525760,
    246846627678730445987512320, 40453408149379441542719078400, 416483499995972535333578342400, 40453408149379441542719078400, 246846627678730445987512320, 129010843650444802256554426368,
    5048981003875628959170708897792, 5048982855670479542577757421568, 129012695445295385663602950144, 5106385778429373738774723297280, 28163367289700061866570547200, 1458460091788038918090260480,
    18494693570272284860679842693120, 39227547296367943314151833600, 5106299505417110199316617625600, 39277839023670979138913566720, 39277839023670979138913566720, 28113075562397026041808814080,
    1458460091788038918090260480, 11427533936403036097317175296, 447229086590382052327475380224, 447229250618830355752808349696, 11427697964851339522650144768, 726799935014459101188880072704,
    2699880638003551222325355479040, 726646944410668166905916817408, 101314202569077081332567244800, 237931712872904204446859264, 101314184622184715515099873280, 237931712872904204446859264,
    61975765081627369593680953344, 5116845917584912703343317483520, 731459175830606366686750703616, 45823016481885274718829419692032, 462948845462409092839715635200, 27776930727744545570382938112,
    731459175830606366686750703616, 726829687375982275758353547264, 462948845462409092839715635200, 11217250525554172319506309840896
  ]
def negativeScales : Array ℕ := #[
    55, 36, 31, 37, 31, 36,
    36, 46, 52, 38, 57, 41,
    37, 57, 37, 38, 42, 38,
    41, 42, 52, 38, 38, 38,
    24, 30, 34, 30, 24, 29,
    36, 34, 31, 52, 22, 22,
    53, 24, 50, 26, 26, 26,
    22, 25, 32, 30, 27, 37,
    39, 33, 48, 11, 48, 11,
    44, 52, 30, 56, 28, 25,
    30, 31, 28, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    55869950344548479, 36100261247731467, 31381443000275523, 37072604904828601, 31381443000275523, 36100261247731467,
    36100261247731467, 46515619533856838, 52421351736591568, 38591446370803283, 57619561601108113, 41978728220477403,
    37481821879624476, 57619561338574641, 37481821879624476, 38443347731809731, 42683043011604505, 38443347731809731,
    41978728220477403, 42683043011604505, 52421354988493239, 38443347731809731, 38443347731809731, 38591446370803283,
    24673745402792965, 30030247909886573, 34394174092593209, 30030247909886573, 24673745402792965, 29703407084307298,
    36993835117523039, 34993835646654694, 31703427792303646, 52010145381546244, 22507806493723827, 22236504471906082,
    53866882341226880, 24985853809389571, 50010121006831172, 26987702234354710, 26987702234354710, 26505227949622022,
    22236504471906082, 25206500760172926, 32496928772014783, 30496929301146257, 27206521468169236, 37197473042309498,
    39090738473612960, 33197169324589461, 48354751181940982, 11620678042145331, 48354750926380614, 11620678042145331,
    44645690833143453, 52013097637075911, 30206692098707967, 56175843374402553, 28546767540306794, 25487873851252200,
    30206692098707967, 31197532099422491, 28546767540306794, 35145490039982211
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
noncomputable def negativeCeiling : ℝ := 18425613123 / 40000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 18534065823447064197553486561280, coefficient := (-18534065823447064197553486561280) }, { argument := 2717760642228740303267907502080, coefficient := (-2717760642228740303267907502080) }, { argument := 103206100337800264681059778560, coefficient := (-103206100337800264681059778560) }, { argument := 2666157592059840170927377612800, coefficient := (-2666157592059840170927377612800) }, { argument := 103206100337800264681059778560, coefficient := (-103206100337800264681059778560) }, { argument := 2717760642228740303267907502080, coefficient := (-2717760642228740303267907502080) }, { argument := 2717760642228740303267907502080, coefficient := (-2717760642228740303267907502080) }, { argument := 226530417523763700904948137984, coefficient := (-226530417523763700904948137984) }, { argument := 6790458027869513001024935165952, coefficient := (-6790458027869513001024935165952) }, { argument := 477510222661605837120481525760, coefficient := (-477510222661605837120481525760) }, { argument := 249296489020110994954856505016320, coefficient := (-249296489020110994954856505016320) }, { argument := 4996387451751924490846014013440, coefficient := (-4996387451751924490846014013440) }, { argument := 442570450271732239282397511680, coefficient := (-442570450271732239282397511680) }, { argument := 249296443654552192474622403280896, coefficient := (-249296443654552192474622403280896) }, { argument := 442570450271732239282397511680, coefficient := (-442570450271732239282397511680) }, { argument := 430923859475107706669702840320, coefficient := (-430923859475107706669702840320) }, { argument := 16281933933681096592547150561280, coefficient := (-16281933933681096592547150561280) }, { argument := 430923859475107706669702840320, coefficient := (-430923859475107706669702840320) }, { argument := 4996387451751924490846014013440, coefficient := (-4996387451751924490846014013440) }, { argument := 16281933933681096592547150561280, coefficient := (-16281933933681096592547150561280) }, { argument := 6790473333894739993019132411904, coefficient := (-6790473333894739993019132411904) }, { argument := 430923859475107706669702840320, coefficient := (-430923859475107706669702840320) }, { argument := 430923859475107706669702840320, coefficient := (-430923859475107706669702840320) }, { argument := 477510222661605837120481525760, coefficient := (-477510222661605837120481525760) }, { argument := 246846627678730445987512320, coefficient := (-246846627678730445987512320) }, { argument := 40453408149379441542719078400, coefficient := (-40453408149379441542719078400) }, { argument := 416483499995972535333578342400, coefficient := (-416483499995972535333578342400) }, { argument := 40453408149379441542719078400, coefficient := (-40453408149379441542719078400) }, { argument := 246846627678730445987512320, coefficient := (-246846627678730445987512320) }, { argument := 129010843650444802256554426368, coefficient := (-129010843650444802256554426368) }, { argument := 5048981003875628959170708897792, coefficient := (-5048981003875628959170708897792) }, { argument := 5048982855670479542577757421568, coefficient := (-5048982855670479542577757421568) }, { argument := 129012695445295385663602950144, coefficient := (-129012695445295385663602950144) }, { argument := 5106385778429373738774723297280, coefficient := (-5106385778429373738774723297280) }, { argument := 28163367289700061866570547200, coefficient := (-28163367289700061866570547200) }, { argument := 1458460091788038918090260480, coefficient := (-1458460091788038918090260480) }, { argument := 18494693570272284860679842693120, coefficient := (-18494693570272284860679842693120) }, { argument := 39227547296367943314151833600, coefficient := (-39227547296367943314151833600) }, { argument := 5106299505417110199316617625600, coefficient := (-5106299505417110199316617625600) }, { argument := 39277839023670979138913566720, coefficient := (-39277839023670979138913566720) }, { argument := 39277839023670979138913566720, coefficient := (-39277839023670979138913566720) }, { argument := 28113075562397026041808814080, coefficient := (-28113075562397026041808814080) }, { argument := 1458460091788038918090260480, coefficient := (-1458460091788038918090260480) }, { argument := 11427533936403036097317175296, coefficient := (-11427533936403036097317175296) }, { argument := 447229086590382052327475380224, coefficient := (-447229086590382052327475380224) }, { argument := 447229250618830355752808349696, coefficient := (-447229250618830355752808349696) }, { argument := 11427697964851339522650144768, coefficient := (-11427697964851339522650144768) }, { argument := 726799935014459101188880072704, coefficient := (-726799935014459101188880072704) }, { argument := 2699880638003551222325355479040, coefficient := (-2699880638003551222325355479040) }, { argument := 726646944410668166905916817408, coefficient := (-726646944410668166905916817408) }, { argument := 101314202569077081332567244800, coefficient := (-101314202569077081332567244800) }, { argument := 237931712872904204446859264, coefficient := (-237931712872904204446859264) }, { argument := 101314184622184715515099873280, coefficient := (-101314184622184715515099873280) }, { argument := 237931712872904204446859264, coefficient := (-237931712872904204446859264) }, { argument := 61975765081627369593680953344, coefficient := (-61975765081627369593680953344) }, { argument := 5116845917584912703343317483520, coefficient := (-5116845917584912703343317483520) }, { argument := 731459175830606366686750703616, coefficient := (-731459175830606366686750703616) }, { argument := 45823016481885274718829419692032, coefficient := (-45823016481885274718829419692032) }, { argument := 462948845462409092839715635200, coefficient := (-462948845462409092839715635200) }, { argument := 27776930727744545570382938112, coefficient := (-27776930727744545570382938112) }, { argument := 731459175830606366686750703616, coefficient := (-731459175830606366686750703616) }, { argument := 726829687375982275758353547264, coefficient := (-726829687375982275758353547264) }, { argument := 462948845462409092839715635200, coefficient := (-462948845462409092839715635200) }, { argument := 11217250525554172319506309840896, coefficient := (-11217250525554172319506309840896) }] }

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


end Parent0

namespace Parent0

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-41475774333122045432841035382259712)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2431224135, 9089354262930815, 1239140043, 47055951, 2431224135, 47055951,
    1239140043, 1239140043, 27522768544953, 12062274760980921, 103543562135, 442839442439170923,
    1083419223315, 47983601965, 442839361853750271, 47983601965, 93441751195, 1765291461765,
    93441751195, 1083419223315, 1765291461765, 12062301949943517, 93441751195, 93441751195,
    103543562135, 162500535040799833, 122799775, 101748385, 587458473058772525, 684170175,
    81250271218594493, 2740189265, 2740189265, 1961287835, 101748385, 38717991,
    6061084341, 1515271641, 154874187, 49873295475, 185266864125, 3116424825,
    8631146002369643, 2345, 8631147798344597, 2345, 5984795457, 22232023695,
    373970979, 30197452295, 2479, 30197445113, 2479, 93,
    3149, 2345, 2479, 201, 43081, 77921,
    2345, 43081, 1273, 1273
  ]
def negativeCoefficients : Array ℕ := #[
    717570710466734093901559234560, 5116851558946705969725602529280, 731459175830606366686750703616, 27776930727744545570382938112, 717570710466734093901559234560, 27776930727744545570382938112,
    731459175830606366686750703616, 731459175830606366686750703616, 61975765081627369593680953344, 6790457014849276814945106788352, 477510397796146994423571415040, 249296443494251047634748598910976,
    4996389284257245380675905781760, 442570612591550872880383262720, 249296398128692245154514497175552, 442570612591550872880383262720, 430924017523352165699320545280, 16281939905341792639125678981120,
    430924017523352165699320545280, 4996389284257245380675905781760, 16281939905341792639125678981120, 6790472320874503806939304034304, 430924017523352165699320545280, 430924017523352165699320545280,
    477510397796146994423571415040, 45739834316078272244433654120448, 289952770781966893285847859200, 15015411344066142688017121280, 165354860022695531693889447526400, 403862787874882458505288089600,
    45739836397976736828057312034816, 404380560679850256529012817920, 404380560679850256529012817920, 289434997976999095262123130880, 15015411344066142688017121280, 11427533936403036097317175296,
    447229086590382052327475380224, 447229250618830355752808349696, 11427697964851339522650144768, 459999958869910823537265868800, 1708785213926298241978073088000, 459903129373840611965770137600,
    2429451620003266900013569015808, 177183190437269088417873920, 2429452125525275250085049925632, 177183190437269088417873920, 27599997532194649412235952128, 102527112835577894518684385280,
    27594187762430436717946208256, 69630584270489768576250019840, 187307944176541607756038144, 69630567709925276403500056576, 187307944176541607756038144, 1798881619586568211962789888,
    237931712872904204446859264, 177183190437269088417873920, 187307944176541607756038144, 242994089742540464115941376, 3255108327176114967219798016, 5887544299386969995142496256,
    177183190437269088417873920, 3255108327176114967219798016, 192370321046177867425120256, 192370321046177867425120256
  ]
def negativeScales : Array ℕ := #[
    31, 53, 30, 25, 31, 25,
    30, 30, 44, 53, 36, 58,
    39, 35, 58, 35, 36, 40,
    36, 39, 40, 53, 36, 36,
    36, 57, 26, 26, 59, 29,
    56, 31, 31, 30, 26, 25,
    32, 30, 27, 35, 37, 31,
    52, 11, 52, 11, 32, 34,
    28, 34, 11, 34, 11, 6,
    11, 11, 11, 7, 15, 16,
    11, 15, 10, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31179035755805102, 53013099227657360, 30206692098707967, 25487873851252200, 31179035755805102, 25487873851252200,
    30206692098707967, 30206692098707967, 44645690833143453, 53421351521366119, 36591446899934757, 58619561337646968,
    39978728749609021, 35481822408755950, 58619561075113448, 35481822408755950, 36443348260941204, 40683043540735979,
    36443348260941204, 39978728749609021, 40683043540735979, 53421354773268274, 36443348260941204, 36443348260941204,
    36591446899934757, 57173222081376639, 26871732679037850, 26600430654618434, 59027264485478302, 29349779973234751,
    56173222147042477, 31351628397627120, 31351628397627120, 30869154134813967, 26600430654618434, 25206500760172926,
    32496928772014783, 30496929301146257, 27206521468169236, 35537548483908027, 37430813915210604, 31537244766187981,
    52938473558163189, 11195372207402739, 52938473858360205, 11195372207402739, 32478654794853681, 34371920226157015,
    28478351077133643, 34813707786812049, 11275542556086723, 34813707443689156, 11275542556086723, 6539158811108986,
    11620678042145331, 11195372207402739, 11275542556086723, 7651051691200812, 15394764117785726, 16249724571930991,
    11195372207402739, 15394764117785726, 10314016703901359, 10314016703901359
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
noncomputable def negativeCeiling : ℝ := 572765116791 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 717570710466734093901559234560, coefficient := (-717570710466734093901559234560) }, { argument := 5116851558946705969725602529280, coefficient := (-5116851558946705969725602529280) }, { argument := 731459175830606366686750703616, coefficient := (-731459175830606366686750703616) }, { argument := 27776930727744545570382938112, coefficient := (-27776930727744545570382938112) }, { argument := 717570710466734093901559234560, coefficient := (-717570710466734093901559234560) }, { argument := 27776930727744545570382938112, coefficient := (-27776930727744545570382938112) }, { argument := 731459175830606366686750703616, coefficient := (-731459175830606366686750703616) }, { argument := 731459175830606366686750703616, coefficient := (-731459175830606366686750703616) }, { argument := 61975765081627369593680953344, coefficient := (-61975765081627369593680953344) }, { argument := 6790457014849276814945106788352, coefficient := (-6790457014849276814945106788352) }, { argument := 477510397796146994423571415040, coefficient := (-477510397796146994423571415040) }, { argument := 249296443494251047634748598910976, coefficient := (-249296443494251047634748598910976) }, { argument := 4996389284257245380675905781760, coefficient := (-4996389284257245380675905781760) }, { argument := 442570612591550872880383262720, coefficient := (-442570612591550872880383262720) }, { argument := 249296398128692245154514497175552, coefficient := (-249296398128692245154514497175552) }, { argument := 442570612591550872880383262720, coefficient := (-442570612591550872880383262720) }, { argument := 430924017523352165699320545280, coefficient := (-430924017523352165699320545280) }, { argument := 16281939905341792639125678981120, coefficient := (-16281939905341792639125678981120) }, { argument := 430924017523352165699320545280, coefficient := (-430924017523352165699320545280) }, { argument := 4996389284257245380675905781760, coefficient := (-4996389284257245380675905781760) }, { argument := 16281939905341792639125678981120, coefficient := (-16281939905341792639125678981120) }, { argument := 6790472320874503806939304034304, coefficient := (-6790472320874503806939304034304) }, { argument := 430924017523352165699320545280, coefficient := (-430924017523352165699320545280) }, { argument := 430924017523352165699320545280, coefficient := (-430924017523352165699320545280) }, { argument := 477510397796146994423571415040, coefficient := (-477510397796146994423571415040) }, { argument := 45739834316078272244433654120448, coefficient := (-45739834316078272244433654120448) }, { argument := 289952770781966893285847859200, coefficient := (-289952770781966893285847859200) }, { argument := 15015411344066142688017121280, coefficient := (-15015411344066142688017121280) }, { argument := 165354860022695531693889447526400, coefficient := (-165354860022695531693889447526400) }, { argument := 403862787874882458505288089600, coefficient := (-403862787874882458505288089600) }, { argument := 45739836397976736828057312034816, coefficient := (-45739836397976736828057312034816) }, { argument := 404380560679850256529012817920, coefficient := (-404380560679850256529012817920) }, { argument := 404380560679850256529012817920, coefficient := (-404380560679850256529012817920) }, { argument := 289434997976999095262123130880, coefficient := (-289434997976999095262123130880) }, { argument := 15015411344066142688017121280, coefficient := (-15015411344066142688017121280) }, { argument := 11427533936403036097317175296, coefficient := (-11427533936403036097317175296) }, { argument := 447229086590382052327475380224, coefficient := (-447229086590382052327475380224) }, { argument := 447229250618830355752808349696, coefficient := (-447229250618830355752808349696) }, { argument := 11427697964851339522650144768, coefficient := (-11427697964851339522650144768) }, { argument := 459999958869910823537265868800, coefficient := (-459999958869910823537265868800) }, { argument := 1708785213926298241978073088000, coefficient := (-1708785213926298241978073088000) }, { argument := 459903129373840611965770137600, coefficient := (-459903129373840611965770137600) }, { argument := 2429451620003266900013569015808, coefficient := (-2429451620003266900013569015808) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 2429452125525275250085049925632, coefficient := (-2429452125525275250085049925632) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 27599997532194649412235952128, coefficient := (-27599997532194649412235952128) }, { argument := 102527112835577894518684385280, coefficient := (-102527112835577894518684385280) }, { argument := 27594187762430436717946208256, coefficient := (-27594187762430436717946208256) }, { argument := 69630584270489768576250019840, coefficient := (-69630584270489768576250019840) }, { argument := 187307944176541607756038144, coefficient := (-187307944176541607756038144) }, { argument := 69630567709925276403500056576, coefficient := (-69630567709925276403500056576) }, { argument := 187307944176541607756038144, coefficient := (-187307944176541607756038144) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 237931712872904204446859264, coefficient := (-237931712872904204446859264) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 187307944176541607756038144, coefficient := (-187307944176541607756038144) }, { argument := 242994089742540464115941376, coefficient := (-242994089742540464115941376) }, { argument := 3255108327176114967219798016, coefficient := (-3255108327176114967219798016) }, { argument := 5887544299386969995142496256, coefficient := (-5887544299386969995142496256) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 3255108327176114967219798016, coefficient := (-3255108327176114967219798016) }, { argument := 192370321046177867425120256, coefficient := (-192370321046177867425120256) }, { argument := 192370321046177867425120256, coefficient := (-192370321046177867425120256) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18
