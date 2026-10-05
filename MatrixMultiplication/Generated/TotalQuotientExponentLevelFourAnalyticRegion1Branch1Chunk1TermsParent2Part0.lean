import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 1, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1

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
def constantNumerator : ℤ := (-156165320595964499149208349048832)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    69127551, 211842495, 626607801, 1398160467, 69127551, 697965273,
    1420459677, 69127551, 211842495, 69127551, 1101844015, 7522562535,
    840707007, 68165433, 14610124473, 26425466193, 7522562535, 14610124473,
    431714409, 431714409, 840707007, 840707007, 26425466193, 840707007,
    1101844015, 68165433, 19147765, 3797668875, 3797668875, 19147765,
    14361027, 1283661051, 91909741, 12152620195, 3580899, 5968165,
    182625849, 5968165, 3580899, 2925594483, 187400381, 1283661051,
    182625849, 5968165, 187400381, 5968165, 182625849, 5968165,
    14361027, 503630247, 1543383015, 4565164497, 10186327899, 503630247,
    5085040881, 10348789269, 503630247, 1543383015, 503630247, 5341034097,
    2394048255, 8402827539, 681310341, 146027516421
  ]
def negativeCoefficients : Array ℕ := #[
    637589120869652394261086208, 15631217156804381278658887680, 11558873739636924050797756416, 12895754154363614554893582336, 637589120869652394261086208, 12875186763367819316369031168,
    13101428064321566940139094016, 637589120869652394261086208, 15631217156804381278658887680, 637589120869652394261086208, 2540679319231698537052897280, 17345848232702593932271288320,
    1938538374887918065799921664, 2514860594449191004280979456, 33688653379808954494847287296, 60932976486341857041224564736, 17345848232702593932271288320, 33688653379808954494847287296,
    1990931303938942878389108736, 1990931303938942878389108736, 1938538374887918065799921664, 1938538374887918065799921664, 60932976486341857041224564736, 1938538374887918065799921664,
    2540679319231698537052897280, 2514860594449191004280979456, 88303480134633293149634560, 17513656453454367490572288000, 17513656453454367490572288000, 88303480134633293149634560,
    66228547426158215228817408, 5919841721296506124033327104, 847717735053964899126345728, 56044068640539816383249121280, 528447419254419677377462272, 27523303086167691530076160,
    842213074436731360820330496, 880745698757366128962437120, 528447419254419677377462272, 13491923172839402388043333632, 864231716905665514044391424, 5919841721296506124033327104,
    842213074436731360820330496, 27523303086167691530076160, 864231716905665514044391424, 27523303086167691530076160, 842213074436731360820330496, 880745698757366128962437120,
    66228547426158215228817408, 2322584568547031921656332288, 56940782970830460014800404480, 42106210565271998063576088576, 46976145950935129512210333696, 2322584568547031921656332288,
    46901223868078773643769806848, 47725366779498688196615602176, 2322584568547031921656332288, 56940782970830460014800404480, 2322584568547031921656332288, 98524689076315396455637450752,
    88324790920191886846234460160, 77502404553725833103133376512, 100543659961590269971632488448, 1346866111568802991494993543168
  ]
def negativeScales : Array ℕ := #[
    26, 27, 29, 30, 26, 29,
    30, 26, 27, 26, 30, 32,
    29, 26, 33, 34, 32, 33,
    28, 28, 29, 29, 34, 29,
    30, 26, 24, 31, 31, 24,
    23, 30, 26, 33, 21, 22,
    27, 22, 21, 31, 27, 30,
    27, 22, 27, 22, 27, 22,
    23, 28, 30, 32, 33, 28,
    32, 33, 28, 30, 28, 32,
    31, 32, 29, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    26042757480023858, 27658416777994287, 29222987489857909, 30380882802439025, 26042757480023858, 29378580016569604,
    30403710731893291, 26042757480023858, 27658416777994287, 26042757480023858, 30037272854016694, 32808577049475346,
    29647027856630440, 26022536991702896, 33766249418629144, 34621209872465021, 32808577049475346, 33766249418629144,
    28685502004476598, 28685502004476598, 29647027856630440, 29647027856630440, 34621209872465021, 29647027856630440,
    30037272854016694, 26022536991702896, 24190672669333438, 31822466975016500, 31822466975016500, 24190672669333438,
    23775655588889764, 30257617165016852, 26453714437016999, 33500548351988085, 21771890397403388, 22508855991209770,
    27444315739014734, 22508855991209770, 21771890397403388, 31446082665188924, 27481548645213816, 30257617165016852,
    27444315739014734, 22508855991209770, 27481548645213816, 22508855991209770, 27444315739014734, 22508855991209770,
    23775655588889764, 28907789695082770, 30523448988008537, 32088019699897932, 33245915012479045, 28907789695082770,
    32243612226609625, 33268742941933307, 28907789695082770, 30523448988008537, 28907789695082770, 32314471948367178,
    31156805085861487, 32968227742450962, 29343736863408078, 37087449290014869
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
noncomputable def negativeCeiling : ℝ := 516592443 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 637589120869652394261086208, coefficient := (-637589120869652394261086208) }, { argument := 15631217156804381278658887680, coefficient := (-15631217156804381278658887680) }, { argument := 11558873739636924050797756416, coefficient := (-11558873739636924050797756416) }, { argument := 12895754154363614554893582336, coefficient := (-12895754154363614554893582336) }, { argument := 637589120869652394261086208, coefficient := (-637589120869652394261086208) }, { argument := 12875186763367819316369031168, coefficient := (-12875186763367819316369031168) }, { argument := 13101428064321566940139094016, coefficient := (-13101428064321566940139094016) }, { argument := 637589120869652394261086208, coefficient := (-637589120869652394261086208) }, { argument := 15631217156804381278658887680, coefficient := (-15631217156804381278658887680) }, { argument := 637589120869652394261086208, coefficient := (-637589120869652394261086208) }, { argument := 2540679319231698537052897280, coefficient := (-2540679319231698537052897280) }, { argument := 17345848232702593932271288320, coefficient := (-17345848232702593932271288320) }, { argument := 1938538374887918065799921664, coefficient := (-1938538374887918065799921664) }, { argument := 2514860594449191004280979456, coefficient := (-2514860594449191004280979456) }, { argument := 33688653379808954494847287296, coefficient := (-33688653379808954494847287296) }, { argument := 60932976486341857041224564736, coefficient := (-60932976486341857041224564736) }, { argument := 17345848232702593932271288320, coefficient := (-17345848232702593932271288320) }, { argument := 33688653379808954494847287296, coefficient := (-33688653379808954494847287296) }, { argument := 1990931303938942878389108736, coefficient := (-1990931303938942878389108736) }, { argument := 1990931303938942878389108736, coefficient := (-1990931303938942878389108736) }, { argument := 1938538374887918065799921664, coefficient := (-1938538374887918065799921664) }, { argument := 1938538374887918065799921664, coefficient := (-1938538374887918065799921664) }, { argument := 60932976486341857041224564736, coefficient := (-60932976486341857041224564736) }, { argument := 1938538374887918065799921664, coefficient := (-1938538374887918065799921664) }, { argument := 2540679319231698537052897280, coefficient := (-2540679319231698537052897280) }, { argument := 2514860594449191004280979456, coefficient := (-2514860594449191004280979456) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 66228547426158215228817408, coefficient := (-66228547426158215228817408) }, { argument := 5919841721296506124033327104, coefficient := (-5919841721296506124033327104) }, { argument := 847717735053964899126345728, coefficient := (-847717735053964899126345728) }, { argument := 56044068640539816383249121280, coefficient := (-56044068640539816383249121280) }, { argument := 528447419254419677377462272, coefficient := (-528447419254419677377462272) }, { argument := 27523303086167691530076160, coefficient := (-27523303086167691530076160) }, { argument := 842213074436731360820330496, coefficient := (-842213074436731360820330496) }, { argument := 880745698757366128962437120, coefficient := (-880745698757366128962437120) }, { argument := 528447419254419677377462272, coefficient := (-528447419254419677377462272) }, { argument := 13491923172839402388043333632, coefficient := (-13491923172839402388043333632) }, { argument := 864231716905665514044391424, coefficient := (-864231716905665514044391424) }, { argument := 5919841721296506124033327104, coefficient := (-5919841721296506124033327104) }, { argument := 842213074436731360820330496, coefficient := (-842213074436731360820330496) }, { argument := 27523303086167691530076160, coefficient := (-27523303086167691530076160) }, { argument := 864231716905665514044391424, coefficient := (-864231716905665514044391424) }, { argument := 27523303086167691530076160, coefficient := (-27523303086167691530076160) }, { argument := 842213074436731360820330496, coefficient := (-842213074436731360820330496) }, { argument := 880745698757366128962437120, coefficient := (-880745698757366128962437120) }, { argument := 66228547426158215228817408, coefficient := (-66228547426158215228817408) }, { argument := 2322584568547031921656332288, coefficient := (-2322584568547031921656332288) }, { argument := 56940782970830460014800404480, coefficient := (-56940782970830460014800404480) }, { argument := 42106210565271998063576088576, coefficient := (-42106210565271998063576088576) }, { argument := 46976145950935129512210333696, coefficient := (-46976145950935129512210333696) }, { argument := 2322584568547031921656332288, coefficient := (-2322584568547031921656332288) }, { argument := 46901223868078773643769806848, coefficient := (-46901223868078773643769806848) }, { argument := 47725366779498688196615602176, coefficient := (-47725366779498688196615602176) }, { argument := 2322584568547031921656332288, coefficient := (-2322584568547031921656332288) }, { argument := 56940782970830460014800404480, coefficient := (-56940782970830460014800404480) }, { argument := 2322584568547031921656332288, coefficient := (-2322584568547031921656332288) }, { argument := 98524689076315396455637450752, coefficient := (-98524689076315396455637450752) }, { argument := 88324790920191886846234460160, coefficient := (-88324790920191886846234460160) }, { argument := 77502404553725833103133376512, coefficient := (-77502404553725833103133376512) }, { argument := 100543659961590269971632488448, coefficient := (-100543659961590269971632488448) }, { argument := 1346866111568802991494993543168, coefficient := (-1346866111568802991494993543168) }] }

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
def constantNumerator : ℤ := (-885496907447792702940840066023424)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    264121308861, 2394048255, 146027516421, 4314965493, 4314965493, 8402827539,
    8402827539, 264121308861, 8402827539, 5341034097, 681310341, 216096205,
    42859405875, 42859405875, 216096205, 2556139161, 17062844115, 3765559105,
    177104521735, 146710095, 244516825, 7482214845, 244516825, 146710095,
    119862147615, 7677828305, 17062844115, 7482214845, 244516825, 7677828305,
    244516825, 7482214845, 244516825, 2556139161, 19147765, 3797668875,
    3797668875, 19147765, 184780211, 7570479455, 155882034385, 7570479455,
    184780211, 2194067083, 19147765, 21267975469, 216096205, 19147765,
    42535940551, 19147765, 19147765, 793811629, 4923711, 216096205,
    793811629, 2194067083, 19147765, 4923711, 19147765, 138255195,
    423685275, 1253216445, 2796322815, 138255195
  ]
def negativeCoefficients : Array ℕ := #[
    2436089094486030916187678834688, 88324790920191886846234460160, 1346866111568802991494993543168, 79597064136258963727542386688, 79597064136258963727542386688, 77502404553725833103133376512,
    77502404553725833103133376512, 2436089094486030916187678834688, 77502404553725833103133376512, 98524689076315396455637450752, 100543659961590269971632488448, 996567847233718594117304320,
    197654122831842147393601536000, 197654122831842147393601536000, 996567847233718594117304320, 5894055614969206928176054272, 157376959279503074505177169920, 138924610208723586426192527360,
    816750446685568931563244093440, 86602354415827690239704432640, 4510539292491025533317939200, 138022502350225381319528939520, 144337257359712817066174054400, 86602354415827690239704432640,
    2211066361179100716432453795840, 141630933784218201746183290880, 157376959279503074505177169920, 138022502350225381319528939520, 4510539292491025533317939200, 141630933784218201746183290880,
    4510539292491025533317939200, 138022502350225381319528939520, 144337257359712817066174054400, 5894055614969206928176054272, 88303480134633293149634560, 17513656453454367490572288000,
    17513656453454367490572288000, 88303480134633293149634560, 852148315550762625079967744, 139650697021661166146190049280, 1437757996994643649754122158080, 139650697021661166146190049280,
    852148315550762625079967744, 2529587122540715806459691008, 88303480134633293149634560, 98081225110643967900019326976, 996567847233718594117304320, 88303480134633293149634560,
    98081201159852631197380247552, 88303480134633293149634560, 88303480134633293149634560, 3660809990724368810289135616, 90826436709908530096766976, 996567847233718594117304320,
    3660809990724368810289135616, 2529587122540715806459691008, 88303480134633293149634560, 90826436709908530096766976, 88303480134633293149634560, 637589549756452108008161280,
    15631227671448503293103308800, 11558881514939551119373762560, 12895762828945015216810229760, 637589549756452108008161280
  ]
def negativeScales : Array ℕ := #[
    37, 31, 37, 32, 32, 32,
    32, 37, 32, 32, 29, 27,
    35, 35, 27, 31, 33, 31,
    37, 27, 27, 32, 27, 27,
    36, 32, 33, 32, 27, 32,
    27, 32, 27, 31, 24, 31,
    31, 24, 27, 32, 37, 32,
    27, 31, 24, 34, 27, 24,
    35, 24, 24, 29, 22, 27,
    29, 31, 24, 22, 24, 27,
    28, 30, 31, 27
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    37942409753324979, 31156805085861487, 37087449290014869, 32006701876130507, 32006701876130507, 32968227742450962,
    32968227742450962, 37942409753324979, 32968227742450962, 32314471948367178, 29343736863408078, 27687098495506215,
    35318892800121588, 35318892800121588, 27687098495506215, 31251319235427438, 33990139110973531, 31810216944943606,
    37365810090415372, 27128392904175353, 27865358500657122, 32800818246803744, 27865358500657122, 27128392904175353,
    36802585173001970, 32838051153722268, 33990139110973531, 32800818246803744, 27865358500657122, 32838051153722268,
    27865358500657122, 32800818246803744, 27865358500657122, 31251319235427438, 24190672669333438, 31822466975016500,
    31822466975016500, 24190672669333438, 27461235018986811, 32817737527042421, 37181663708825523, 32817737527042421,
    27461235018986811, 31030960490407357, 24190672669333438, 34307963656368439, 27687098495506215, 24190672669333438,
    35307963304071737, 24190672669333438, 24190672669333438, 29564221456457250, 22231314653830784, 27687098495506215,
    29564221456457250, 31030960490407357, 24190672669333438, 22231314653830784, 24190672669333438, 27042758450480585,
    28658417748451014, 30222988460314636, 31380883772895751, 27042758450480585
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
noncomputable def negativeCeiling : ℝ := 6092663581 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2436089094486030916187678834688, coefficient := (-2436089094486030916187678834688) }, { argument := 88324790920191886846234460160, coefficient := (-88324790920191886846234460160) }, { argument := 1346866111568802991494993543168, coefficient := (-1346866111568802991494993543168) }, { argument := 79597064136258963727542386688, coefficient := (-79597064136258963727542386688) }, { argument := 79597064136258963727542386688, coefficient := (-79597064136258963727542386688) }, { argument := 77502404553725833103133376512, coefficient := (-77502404553725833103133376512) }, { argument := 77502404553725833103133376512, coefficient := (-77502404553725833103133376512) }, { argument := 2436089094486030916187678834688, coefficient := (-2436089094486030916187678834688) }, { argument := 77502404553725833103133376512, coefficient := (-77502404553725833103133376512) }, { argument := 98524689076315396455637450752, coefficient := (-98524689076315396455637450752) }, { argument := 100543659961590269971632488448, coefficient := (-100543659961590269971632488448) }, { argument := 996567847233718594117304320, coefficient := (-996567847233718594117304320) }, { argument := 197654122831842147393601536000, coefficient := (-197654122831842147393601536000) }, { argument := 197654122831842147393601536000, coefficient := (-197654122831842147393601536000) }, { argument := 996567847233718594117304320, coefficient := (-996567847233718594117304320) }, { argument := 5894055614969206928176054272, coefficient := (-5894055614969206928176054272) }, { argument := 157376959279503074505177169920, coefficient := (-157376959279503074505177169920) }, { argument := 138924610208723586426192527360, coefficient := (-138924610208723586426192527360) }, { argument := 816750446685568931563244093440, coefficient := (-816750446685568931563244093440) }, { argument := 86602354415827690239704432640, coefficient := (-86602354415827690239704432640) }, { argument := 4510539292491025533317939200, coefficient := (-4510539292491025533317939200) }, { argument := 138022502350225381319528939520, coefficient := (-138022502350225381319528939520) }, { argument := 144337257359712817066174054400, coefficient := (-144337257359712817066174054400) }, { argument := 86602354415827690239704432640, coefficient := (-86602354415827690239704432640) }, { argument := 2211066361179100716432453795840, coefficient := (-2211066361179100716432453795840) }, { argument := 141630933784218201746183290880, coefficient := (-141630933784218201746183290880) }, { argument := 157376959279503074505177169920, coefficient := (-157376959279503074505177169920) }, { argument := 138022502350225381319528939520, coefficient := (-138022502350225381319528939520) }, { argument := 4510539292491025533317939200, coefficient := (-4510539292491025533317939200) }, { argument := 141630933784218201746183290880, coefficient := (-141630933784218201746183290880) }, { argument := 4510539292491025533317939200, coefficient := (-4510539292491025533317939200) }, { argument := 138022502350225381319528939520, coefficient := (-138022502350225381319528939520) }, { argument := 144337257359712817066174054400, coefficient := (-144337257359712817066174054400) }, { argument := 5894055614969206928176054272, coefficient := (-5894055614969206928176054272) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 17513656453454367490572288000, coefficient := (-17513656453454367490572288000) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 852148315550762625079967744, coefficient := (-852148315550762625079967744) }, { argument := 139650697021661166146190049280, coefficient := (-139650697021661166146190049280) }, { argument := 1437757996994643649754122158080, coefficient := (-1437757996994643649754122158080) }, { argument := 139650697021661166146190049280, coefficient := (-139650697021661166146190049280) }, { argument := 852148315550762625079967744, coefficient := (-852148315550762625079967744) }, { argument := 2529587122540715806459691008, coefficient := (-2529587122540715806459691008) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 98081225110643967900019326976, coefficient := (-98081225110643967900019326976) }, { argument := 996567847233718594117304320, coefficient := (-996567847233718594117304320) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 98081201159852631197380247552, coefficient := (-98081201159852631197380247552) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 3660809990724368810289135616, coefficient := (-3660809990724368810289135616) }, { argument := 90826436709908530096766976, coefficient := (-90826436709908530096766976) }, { argument := 996567847233718594117304320, coefficient := (-996567847233718594117304320) }, { argument := 3660809990724368810289135616, coefficient := (-3660809990724368810289135616) }, { argument := 2529587122540715806459691008, coefficient := (-2529587122540715806459691008) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 90826436709908530096766976, coefficient := (-90826436709908530096766976) }, { argument := 88303480134633293149634560, coefficient := (-88303480134633293149634560) }, { argument := 637589549756452108008161280, coefficient := (-637589549756452108008161280) }, { argument := 15631227671448503293103308800, coefficient := (-15631227671448503293103308800) }, { argument := 11558881514939551119373762560, coefficient := (-11558881514939551119373762560) }, { argument := 12895762828945015216810229760, coefficient := (-12895762828945015216810229760) }, { argument := 637589549756452108008161280, coefficient := (-637589549756452108008161280) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1
