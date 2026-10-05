import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 7, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-12151690529261428529362147020374016)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    10165, 19795, 613645, 19795, 1605, 26215,
    18043713, 8530604127, 323814930813, 34122439911, 18043713, 4268506725,
    167047840155, 167047840155, 4268506725, 18803919, 8890010001, 337457691219,
    35560064393, 18803919, 176960093085, 6925326173283, 6925326173283, 176960093085,
    53678198547, 199401130845, 3354181209, 1097616015, 42955158897, 42955158897,
    1097616015, 1754189495, 6516376825, 109613765, 2648545221, 26215,
    2648545851, 26215, 11201859, 5295951261, 201030087159, 21183819573,
    11201859, 48173147325, 1885254196035, 1885254196035, 48173147325, 1052513697,
    3909826095, 65768259, 176960093085, 6925326173283, 6925326173283, 176960093085,
    859903690449, 3194327919615, 53732667603, 567670732869, 21935, 567670867899,
    21935, 55081550143, 204614232305, 3441872221
  ]
def negativeCoefficients : Array ℕ := #[
    192011421193479774388879360, 186958489056809254010224640, 5795713160761086874316963840, 186958489056809254010224640, 242540742560184978175426560, 247593674696855498554081280,
    332847755850465994717790208, 39340467781224873303692279808, 373333197247086014299518271488, 39340494763046845617732059136, 332847755850465994717790208, 9842506391622889596203827200,
    385186094425653339530786242560, 385186094425653339530786242560, 9842506391622889596203827200, 346871081375764438113583104, 40997934825291348758866427904, 389062229101362252820191903744,
    40997962943893924615257325568, 346871081375764438113583104, 408042193549851794402621521920, 15968714943189228447404881084416, 15968714943189228447404881084416, 408042193549851794402621521920,
    990187990934276914453992701952, 3678301628705986626308297195520, 989979557428299023267244539904, 10123720859954972156095365120, 396191411409243434945951563776, 396191411409243434945951563776,
    10123720859954972156095365120, 1035490709473753636030319165440, 3846589938516064445812598374400, 1035272739794299632174896250880, 97714071718867009349219254272, 247593674696855498554081280,
    97714094961764542223254290432, 247593674696855498554081280, 206637826122780004155654144, 24423264384626594207124946944, 231771910558599867613455581184, 24423281135423134640004661248,
    206637826122780004155654144, 111079714991172611157157478400, 4347100208518087688990301880320, 4347100208518087688990301880320, 111079714991172611157157478400, 621294425684252181618191499264,
    2307953963109638667487559024640, 621163643876579779304937750528, 408042193549851794402621521920, 15968714943189228447404881084416, 15968714943189228447404881084416, 408042193549851794402621521920,
    15862423305751063511939451715584, 58924949620642962229291741347840, 15859084282723927490379191943168, 1308959590921197965162512908288, 3314723481655861368397496320, 1308959902279179499287607246848,
    3314723481655861368397496320, 1016075258671120755354750681088, 3774466377168888237453612154880, 1015861375923156514071616946176
  ]
def negativeScales : Array ℕ := #[
    13, 14, 19, 14, 10, 14,
    24, 32, 38, 34, 24, 31,
    37, 37, 31, 24, 33, 38,
    35, 24, 37, 42, 42, 37,
    35, 37, 31, 30, 35, 35,
    30, 30, 32, 26, 31, 14,
    31, 14, 23, 32, 37, 34,
    23, 35, 40, 40, 35, 29,
    31, 25, 37, 42, 42, 37,
    39, 41, 35, 39, 14, 39,
    14, 35, 37, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    13311322594732096, 14272848446917460, 19227044757304335, 14272848446917460, 10648357582030099, 14678104925446590,
    24104992908320387, 32990000789223410, 38236378552296014, 34990001778701733, 24104992908320387, 31991084326739097,
    37281470373229352, 37281470373229352, 31991084326739097, 24164530035297751, 33049537896031744, 38295915679273378,
    35049538885509745, 24164530035297751, 37364633093336574, 42655019160375326, 42655019160375326, 37364633093336574,
    35643617204056500, 37536882635342755, 31643313486336323, 30031726290712141, 35322112357726698, 35322112357726698,
    30031726290712141, 30708157456320712, 32601422887542458, 26707853738600059, 31302552995264751, 14678104925446590,
    31302553338433431, 14678104925446590, 23417234838237829, 32302242698971809, 37548620482214717, 34302243688449809,
    23417234838237829, 35487510132334471, 40777896199757704, 40777896199757704, 35487510132334471, 29971191876910660,
    31864457295647178, 25970888159116519, 37364633093336574, 42655019160375326, 42655019160375326, 37364633093336574,
    39645384130231528, 41538649561516993, 35645080412511344, 39046263406946463, 14420947085906609, 39046263750115623,
    14420947085906609, 35680850110283206, 37574115541543558, 31680546392562833
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
noncomputable def negativeCeiling : ℝ := 92799022291 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 5795713160761086874316963840, coefficient := (-5795713160761086874316963840) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 242540742560184978175426560, coefficient := (-242540742560184978175426560) }, { argument := 247593674696855498554081280, coefficient := (-247593674696855498554081280) }, { argument := 332847755850465994717790208, coefficient := (-332847755850465994717790208) }, { argument := 39340467781224873303692279808, coefficient := (-39340467781224873303692279808) }, { argument := 373333197247086014299518271488, coefficient := (-373333197247086014299518271488) }, { argument := 39340494763046845617732059136, coefficient := (-39340494763046845617732059136) }, { argument := 332847755850465994717790208, coefficient := (-332847755850465994717790208) }, { argument := 9842506391622889596203827200, coefficient := (-9842506391622889596203827200) }, { argument := 385186094425653339530786242560, coefficient := (-385186094425653339530786242560) }, { argument := 385186094425653339530786242560, coefficient := (-385186094425653339530786242560) }, { argument := 9842506391622889596203827200, coefficient := (-9842506391622889596203827200) }, { argument := 346871081375764438113583104, coefficient := (-346871081375764438113583104) }, { argument := 40997934825291348758866427904, coefficient := (-40997934825291348758866427904) }, { argument := 389062229101362252820191903744, coefficient := (-389062229101362252820191903744) }, { argument := 40997962943893924615257325568, coefficient := (-40997962943893924615257325568) }, { argument := 346871081375764438113583104, coefficient := (-346871081375764438113583104) }, { argument := 408042193549851794402621521920, coefficient := (-408042193549851794402621521920) }, { argument := 15968714943189228447404881084416, coefficient := (-15968714943189228447404881084416) }, { argument := 15968714943189228447404881084416, coefficient := (-15968714943189228447404881084416) }, { argument := 408042193549851794402621521920, coefficient := (-408042193549851794402621521920) }, { argument := 990187990934276914453992701952, coefficient := (-990187990934276914453992701952) }, { argument := 3678301628705986626308297195520, coefficient := (-3678301628705986626308297195520) }, { argument := 989979557428299023267244539904, coefficient := (-989979557428299023267244539904) }, { argument := 10123720859954972156095365120, coefficient := (-10123720859954972156095365120) }, { argument := 396191411409243434945951563776, coefficient := (-396191411409243434945951563776) }, { argument := 396191411409243434945951563776, coefficient := (-396191411409243434945951563776) }, { argument := 10123720859954972156095365120, coefficient := (-10123720859954972156095365120) }, { argument := 1035490709473753636030319165440, coefficient := (-1035490709473753636030319165440) }, { argument := 3846589938516064445812598374400, coefficient := (-3846589938516064445812598374400) }, { argument := 1035272739794299632174896250880, coefficient := (-1035272739794299632174896250880) }, { argument := 97714071718867009349219254272, coefficient := (-97714071718867009349219254272) }, { argument := 247593674696855498554081280, coefficient := (-247593674696855498554081280) }, { argument := 97714094961764542223254290432, coefficient := (-97714094961764542223254290432) }, { argument := 247593674696855498554081280, coefficient := (-247593674696855498554081280) }, { argument := 206637826122780004155654144, coefficient := (-206637826122780004155654144) }, { argument := 24423264384626594207124946944, coefficient := (-24423264384626594207124946944) }, { argument := 231771910558599867613455581184, coefficient := (-231771910558599867613455581184) }, { argument := 24423281135423134640004661248, coefficient := (-24423281135423134640004661248) }, { argument := 206637826122780004155654144, coefficient := (-206637826122780004155654144) }, { argument := 111079714991172611157157478400, coefficient := (-111079714991172611157157478400) }, { argument := 4347100208518087688990301880320, coefficient := (-4347100208518087688990301880320) }, { argument := 4347100208518087688990301880320, coefficient := (-4347100208518087688990301880320) }, { argument := 111079714991172611157157478400, coefficient := (-111079714991172611157157478400) }, { argument := 621294425684252181618191499264, coefficient := (-621294425684252181618191499264) }, { argument := 2307953963109638667487559024640, coefficient := (-2307953963109638667487559024640) }, { argument := 621163643876579779304937750528, coefficient := (-621163643876579779304937750528) }, { argument := 408042193549851794402621521920, coefficient := (-408042193549851794402621521920) }, { argument := 15968714943189228447404881084416, coefficient := (-15968714943189228447404881084416) }, { argument := 15968714943189228447404881084416, coefficient := (-15968714943189228447404881084416) }, { argument := 408042193549851794402621521920, coefficient := (-408042193549851794402621521920) }, { argument := 15862423305751063511939451715584, coefficient := (-15862423305751063511939451715584) }, { argument := 58924949620642962229291741347840, coefficient := (-58924949620642962229291741347840) }, { argument := 15859084282723927490379191943168, coefficient := (-15859084282723927490379191943168) }, { argument := 1308959590921197965162512908288, coefficient := (-1308959590921197965162512908288) }, { argument := 3314723481655861368397496320, coefficient := (-3314723481655861368397496320) }, { argument := 1308959902279179499287607246848, coefficient := (-1308959902279179499287607246848) }, { argument := 3314723481655861368397496320, coefficient := (-3314723481655861368397496320) }, { argument := 1016075258671120755354750681088, coefficient := (-1016075258671120755354750681088) }, { argument := 3774466377168888237453612154880, coefficient := (-3774466377168888237453612154880) }, { argument := 1015861375923156514071616946176, coefficient := (-1015861375923156514071616946176) }] }

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

end TermShard4


end Parent2

namespace Parent2

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3343012330987326807087926235627520)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1026672120573, 613645, 1026672364803, 613645, 285, 626589607133565,
    523047525, 23602340567762273, 5902964925, 523047525, 11801170924854343, 523047525,
    523047525, 21684055965, 134497935, 5902964925, 21684055965, 156648413978661,
    523047525, 134497935, 523047525, 270748371508235, 10957148055, 284317215,
    3913192211875587, 17649537885, 1083207266373841, 17649537885, 18393136755, 10957148055,
    546763875, 3977239196372779, 18725, 3977241780515029, 18725, 53678198547,
    199401130845, 3354181209, 567670732869, 21935, 567670867899, 21935,
    843, 16772325429, 19795, 16772329419, 19795, 1881,
    558975, 264269025, 10031441475, 1057076825, 558975, 4268506725,
    167047840155, 167047840155, 4268506725, 1754189495, 6516376825, 109613765,
    1097616015, 42955158897, 42955158897, 1097616015
  ]
def negativeCoefficients : Array ℕ := #[
    2367344731977850747010464874496, 5795713160761086874316963840, 2367345295133888887270938771456, 5795713160761086874316963840, 44101613899541672293281300480, 176369295075059301016550768640,
    9648523832062198541608550400, 6643468261627857104904113881088, 108890483247559097826725068800, 9648523832062198541608550400, 6643468622463693848388111958016, 9648523832062198541608550400,
    9648523832062198541608550400, 400000230866350002396400189440, 9924195941549689928511651840, 108890483247559097826725068800, 400000230866350002396400189440, 176370434705619219086221246464,
    9648523832062198541608550400, 9924195941549689928511651840, 9648523832062198541608550400, 4877369060142623048314640138240, 25265463243541173765522063360, 1311181725213713608589967360,
    17623450987232020645337106481152, 40697063547979495466619371520, 4878331841206243929519749595136, 40697063547979495466619371520, 42411685804028197877852405760, 25265463243541173765522063360,
    1260751658859340008259584000, 2238986620343472308831595266048, 176852624783468213252915200, 2238988075086231580375984898048, 176852624783468213252915200, 990187990934276914453992701952,
    3678301628705986626308297195520, 989979557428299023267244539904, 1308959590921197965162512908288, 3314723481655861368397496320, 1308959902279179499287607246848, 3314723481655861368397496320,
    32611982909924236616873803776, 77348698677433440732306210816, 186958489056809254010224640, 77348717078060654257583947776, 186958489056809254010224640, 36383831467121879641957072896,
    10311268768601796614553600, 1218725767695937834686873600, 11565464598732528324024729600, 1218726603564028674650931200, 10311268768601796614553600, 9842506391622889596203827200,
    385186094425653339530786242560, 385186094425653339530786242560, 9842506391622889596203827200, 32359084671054801125947473920, 120205935578627013931643699200, 32352273118571863505465507840,
    10123720859954972156095365120, 396191411409243434945951563776, 396191411409243434945951563776, 10123720859954972156095365120
  ]
def negativeScales : Array ℕ := #[
    39, 19, 39, 19, 8, 49,
    28, 54, 32, 28, 53, 28,
    28, 34, 27, 32, 34, 47,
    28, 27, 28, 47, 33, 28,
    51, 34, 49, 34, 34, 33,
    29, 51, 14, 51, 14, 35,
    37, 31, 39, 14, 39, 14,
    9, 33, 14, 33, 14, 10,
    19, 27, 33, 29, 19, 31,
    37, 37, 31, 30, 32, 26,
    30, 35, 35, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    39901112657234143, 19227044757304335, 39901113000429784, 19227044757304335, 8154818109052105, 49154514169212136,
    28962366810111394, 54389779452279346, 32458792623405399, 28962366810111394, 53389779530638426, 28962366810111394,
    28962366810111394, 34335915584407614, 27003008781783182, 32458792623405399, 34335915584407614, 47154523491322567,
    28962366810111394, 27003008781783182, 28962366810111394, 47943945998197818, 33351153288930756, 28082926213876639,
    51797267399559846, 34038911359013327, 49944230754712441, 34038911359013327, 34098448485990691, 33351153288930756,
    29026342685510272, 51820688754610785, 14192678098233476, 51820689691976602, 14192678098233476, 35643617204056500,
    37536882635342755, 31643313486336323, 39046263406946463, 14420947085906609, 39046263750115623, 14420947085906609,
    9719388821055554, 33965363690153296, 14272848446917460, 33965364033358765, 14272848446917460, 10877284136413052,
    19092424234817332, 27977432111996322, 33223809878792958, 29977433101474589, 19092424234817332, 31991084326739097,
    37281470373229352, 37281470373229352, 31991084326739097, 30708157456320712, 32601422887542458, 26707853738600059,
    30031726290712141, 35322112357726698, 35322112357726698, 30031726290712141
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
noncomputable def negativeCeiling : ℝ := 7137474663 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2367344731977850747010464874496, coefficient := (-2367344731977850747010464874496) }, { argument := 5795713160761086874316963840, coefficient := (-5795713160761086874316963840) }, { argument := 2367345295133888887270938771456, coefficient := (-2367345295133888887270938771456) }, { argument := 5795713160761086874316963840, coefficient := (-5795713160761086874316963840) }, { argument := 44101613899541672293281300480, coefficient := (-44101613899541672293281300480) }, { argument := 176369295075059301016550768640, coefficient := (-176369295075059301016550768640) }, { argument := 9648523832062198541608550400, coefficient := (-9648523832062198541608550400) }, { argument := 6643468261627857104904113881088, coefficient := (-6643468261627857104904113881088) }, { argument := 108890483247559097826725068800, coefficient := (-108890483247559097826725068800) }, { argument := 9648523832062198541608550400, coefficient := (-9648523832062198541608550400) }, { argument := 6643468622463693848388111958016, coefficient := (-6643468622463693848388111958016) }, { argument := 9648523832062198541608550400, coefficient := (-9648523832062198541608550400) }, { argument := 9648523832062198541608550400, coefficient := (-9648523832062198541608550400) }, { argument := 400000230866350002396400189440, coefficient := (-400000230866350002396400189440) }, { argument := 9924195941549689928511651840, coefficient := (-9924195941549689928511651840) }, { argument := 108890483247559097826725068800, coefficient := (-108890483247559097826725068800) }, { argument := 400000230866350002396400189440, coefficient := (-400000230866350002396400189440) }, { argument := 176370434705619219086221246464, coefficient := (-176370434705619219086221246464) }, { argument := 9648523832062198541608550400, coefficient := (-9648523832062198541608550400) }, { argument := 9924195941549689928511651840, coefficient := (-9924195941549689928511651840) }, { argument := 9648523832062198541608550400, coefficient := (-9648523832062198541608550400) }, { argument := 4877369060142623048314640138240, coefficient := (-4877369060142623048314640138240) }, { argument := 25265463243541173765522063360, coefficient := (-25265463243541173765522063360) }, { argument := 1311181725213713608589967360, coefficient := (-1311181725213713608589967360) }, { argument := 17623450987232020645337106481152, coefficient := (-17623450987232020645337106481152) }, { argument := 40697063547979495466619371520, coefficient := (-40697063547979495466619371520) }, { argument := 4878331841206243929519749595136, coefficient := (-4878331841206243929519749595136) }, { argument := 40697063547979495466619371520, coefficient := (-40697063547979495466619371520) }, { argument := 42411685804028197877852405760, coefficient := (-42411685804028197877852405760) }, { argument := 25265463243541173765522063360, coefficient := (-25265463243541173765522063360) }, { argument := 1260751658859340008259584000, coefficient := (-1260751658859340008259584000) }, { argument := 2238986620343472308831595266048, coefficient := (-2238986620343472308831595266048) }, { argument := 176852624783468213252915200, coefficient := (-176852624783468213252915200) }, { argument := 2238988075086231580375984898048, coefficient := (-2238988075086231580375984898048) }, { argument := 176852624783468213252915200, coefficient := (-176852624783468213252915200) }, { argument := 990187990934276914453992701952, coefficient := (-990187990934276914453992701952) }, { argument := 3678301628705986626308297195520, coefficient := (-3678301628705986626308297195520) }, { argument := 989979557428299023267244539904, coefficient := (-989979557428299023267244539904) }, { argument := 1308959590921197965162512908288, coefficient := (-1308959590921197965162512908288) }, { argument := 3314723481655861368397496320, coefficient := (-3314723481655861368397496320) }, { argument := 1308959902279179499287607246848, coefficient := (-1308959902279179499287607246848) }, { argument := 3314723481655861368397496320, coefficient := (-3314723481655861368397496320) }, { argument := 32611982909924236616873803776, coefficient := (-32611982909924236616873803776) }, { argument := 77348698677433440732306210816, coefficient := (-77348698677433440732306210816) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 77348717078060654257583947776, coefficient := (-77348717078060654257583947776) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 36383831467121879641957072896, coefficient := (-36383831467121879641957072896) }, { argument := 10311268768601796614553600, coefficient := (-10311268768601796614553600) }, { argument := 1218725767695937834686873600, coefficient := (-1218725767695937834686873600) }, { argument := 11565464598732528324024729600, coefficient := (-11565464598732528324024729600) }, { argument := 1218726603564028674650931200, coefficient := (-1218726603564028674650931200) }, { argument := 10311268768601796614553600, coefficient := (-10311268768601796614553600) }, { argument := 9842506391622889596203827200, coefficient := (-9842506391622889596203827200) }, { argument := 385186094425653339530786242560, coefficient := (-385186094425653339530786242560) }, { argument := 385186094425653339530786242560, coefficient := (-385186094425653339530786242560) }, { argument := 9842506391622889596203827200, coefficient := (-9842506391622889596203827200) }, { argument := 32359084671054801125947473920, coefficient := (-32359084671054801125947473920) }, { argument := 120205935578627013931643699200, coefficient := (-120205935578627013931643699200) }, { argument := 32352273118571863505465507840, coefficient := (-32352273118571863505465507840) }, { argument := 10123720859954972156095365120, coefficient := (-10123720859954972156095365120) }, { argument := 396191411409243434945951563776, coefficient := (-396191411409243434945951563776) }, { argument := 396191411409243434945951563776, coefficient := (-396191411409243434945951563776) }, { argument := 10123720859954972156095365120, coefficient := (-10123720859954972156095365120) }] }

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

end TermShard5


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7
