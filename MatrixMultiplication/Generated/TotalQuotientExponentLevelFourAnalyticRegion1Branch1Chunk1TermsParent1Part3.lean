import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 1, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 16336750361947898553002931844546560
def positiveArguments : Array ℕ := #[
    431, 9, 1503, 39, 1617, 2421,
    75, 2421, 2523, 1503, 75, 15221,
    17185, 7365, 193945, 17185, 7365, 17185,
    17185, 712441, 4419, 193945, 712441
  ]
def positiveCoefficients : Array ℕ := #[
    136589352174591718011269770379264, 5570730176784211237046059008, 116288992440370409573336481792, 6034957691516228840133230592, 125109315220278744031992741888, 187315802194369102845673734144,
    5802843934150220038589644800, 187315802194369102845673734144, 195207669944813402098155651072, 116288992440370409573336481792, 5802843934150220038589644800, 294416958405668330691243278336,
    332406243361238437877210152960, 284919637166775803894751559680, 3751441889362548084614228869120, 332406243361238437877210152960, 284919637166775803894751559680, 332406243361238437877210152960,
    332406243361238437877210152960, 13780613117633056381709483769856, 341903564600130964673701871616, 3751441889362548084614228869120, 13780613117633056381709483769856
  ]
def positiveScales : Array ℕ := #[
    8, 3, 10, 5, 10, 11,
    6, 11, 11, 10, 6, 13,
    14, 12, 17, 14, 12, 14,
    14, 19, 12, 17, 19
  ]
def negativeArguments : Array ℕ := #[
    1375118875, 568045275, 5677586175, 11355169575, 568045275, 21611651025,
    157452144425, 43223331125, 687558975, 5009225575, 1375118875, 372285841,
    8879465, 3414162675, 100211105, 8879465, 6828323685, 8879465,
    8879465, 368117249, 2283291, 100211105, 368117249, 372285841,
    8879465, 2283291, 8879465, 218567367, 147585081, 3829553,
    25611060459, 237726867, 6994455025, 237726867, 247742621, 147585081,
    7364525, 55748025, 406153425, 111496125, 3
  ]
def negativeCoefficients : Array ℕ := #[
    6341616489513098923737088000, 20957171620409925035674828800, 837863833013252249763604070400, 837863628254393031587581132800, 20957171620409925035674828800, 199332297734248853367108403200,
    726119853016182291636106035200, 199332431819019839143411712000, 6341612223703531878403276800, 23100975547376392769162444800, 6341616489513098923737088000, 858432703899090801636933632,
    81898609183230691869982720, 31490092545868299959166566400, 924284303639317808246947840, 81898609183230691869982720, 31490084867411079277565706240, 81898609183230691869982720,
    81898609183230691869982720, 3395282340710506682952712192, 84238569445608711637696512, 924284303639317808246947840, 3395282340710506682952712192, 858432703899090801636933632,
    81898609183230691869982720, 84238569445608711637696512, 81898609183230691869982720, 8063712563827101238919430144, 170154013644043384107565056, 8830348013463329314963456,
    29527542358967204927697321984, 274080417187111798352904192, 8064057611327921480689254400, 274080417187111798352904192, 285627795358563844380164096, 170154013644043384107565056,
    8490719243714739725926400, 8226956398318095409820467200, 29968833142542347376210739200, 8226961932341317522685952000, 950737950171172051122527404032
  ]
def negativeScales : Array ℕ := #[
    30, 29, 32, 33, 29, 34,
    37, 35, 29, 32, 30, 28,
    23, 31, 26, 23, 32, 23,
    23, 28, 21, 26, 28, 28,
    23, 21, 23, 27, 27, 21,
    34, 27, 32, 27, 27, 27,
    22, 25, 28, 26, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8751544059074671, 3169925001442312, 10553629293916271, 5285402218862248, 10659103963471994, 11241387363998936,
    6228818690495880, 11241387363998936, 11300924490976300, 10553629293916271, 6228818690495880, 13893775524460172,
    14068862231259659, 12846469809823008, 17565288057379027, 14068862231259659, 12846469809823008, 14068862231259659,
    14068862231259659, 19442411018381434, 12109504215757005, 17565288057379027, 19442411018381434
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    30356909194776229, 29081430680756464, 32402630552461654, 33402630199892877, 29081430680756464, 34331090240163770,
    37196122450203793, 35331091210620497, 29356908224319502, 32221940434359524, 30356909194776229, 28471835506882499,
    23082041324154209, 31668884654279649, 26578467150276789, 23082041324154209, 32668884302496830, 23082041324154209,
    23082041324154209, 28455590111276045, 21122683308651555, 26578467150276789, 28455590111276045, 28471835506882499,
    23082041324154209, 21122683308651555, 23082041324154209, 27703502776007649, 27136971649500192, 21868744576912816,
    34576047939698087, 27824729720643549, 32703564507829704, 27824729720643549, 27884266849845248, 27136971649500192,
    22812161046905850, 25732417359564092, 28597449569456999, 26732418330020822, 1584962500724866
  ]

abbrev PositiveTerm := Fin 23
abbrev NegativeTerm := Fin 41
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
noncomputable def positiveFloor : ℝ := 5740473927 / 250000000000
noncomputable def negativeCeiling : ℝ := 1266704383 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 6341616489513098923737088000, coefficient := (-6341616489513098923737088000) }, { argument := 20957171620409925035674828800, coefficient := (-20957171620409925035674828800) }, { argument := 837863833013252249763604070400, coefficient := (-837863833013252249763604070400) }, { argument := 837863628254393031587581132800, coefficient := (-837863628254393031587581132800) }, { argument := 20957171620409925035674828800, coefficient := (-20957171620409925035674828800) }, { argument := 199332297734248853367108403200, coefficient := (-199332297734248853367108403200) }, { argument := 726119853016182291636106035200, coefficient := (-726119853016182291636106035200) }, { argument := 199332431819019839143411712000, coefficient := (-199332431819019839143411712000) }, { argument := 6341612223703531878403276800, coefficient := (-6341612223703531878403276800) }, { argument := 23100975547376392769162444800, coefficient := (-23100975547376392769162444800) }, { argument := 6341616489513098923737088000, coefficient := (-6341616489513098923737088000) }, { argument := 858432703899090801636933632, coefficient := (-858432703899090801636933632) }, { argument := 81898609183230691869982720, coefficient := (-81898609183230691869982720) }, { argument := 31490092545868299959166566400, coefficient := (-31490092545868299959166566400) }, { argument := 924284303639317808246947840, coefficient := (-924284303639317808246947840) }, { argument := 81898609183230691869982720, coefficient := (-81898609183230691869982720) }, { argument := 31490084867411079277565706240, coefficient := (-31490084867411079277565706240) }, { argument := 81898609183230691869982720, coefficient := (-81898609183230691869982720) }, { argument := 81898609183230691869982720, coefficient := (-81898609183230691869982720) }, { argument := 3395282340710506682952712192, coefficient := (-3395282340710506682952712192) }, { argument := 84238569445608711637696512, coefficient := (-84238569445608711637696512) }, { argument := 924284303639317808246947840, coefficient := (-924284303639317808246947840) }, { argument := 3395282340710506682952712192, coefficient := (-3395282340710506682952712192) }, { argument := 858432703899090801636933632, coefficient := (-858432703899090801636933632) }, { argument := 81898609183230691869982720, coefficient := (-81898609183230691869982720) }, { argument := 84238569445608711637696512, coefficient := (-84238569445608711637696512) }, { argument := 81898609183230691869982720, coefficient := (-81898609183230691869982720) }, { argument := 8063712563827101238919430144, coefficient := (-8063712563827101238919430144) }, { argument := 170154013644043384107565056, coefficient := (-170154013644043384107565056) }, { argument := 8830348013463329314963456, coefficient := (-8830348013463329314963456) }, { argument := 29527542358967204927697321984, coefficient := (-29527542358967204927697321984) }, { argument := 274080417187111798352904192, coefficient := (-274080417187111798352904192) }, { argument := 8064057611327921480689254400, coefficient := (-8064057611327921480689254400) }, { argument := 274080417187111798352904192, coefficient := (-274080417187111798352904192) }, { argument := 285627795358563844380164096, coefficient := (-285627795358563844380164096) }, { argument := 170154013644043384107565056, coefficient := (-170154013644043384107565056) }, { argument := 8490719243714739725926400, coefficient := (-8490719243714739725926400) }, { argument := 8226956398318095409820467200, coefficient := (-8226956398318095409820467200) }, { argument := 29968833142542347376210739200, coefficient := (-29968833142542347376210739200) }, { argument := 8226961932341317522685952000, coefficient := (-8226961932341317522685952000) }, { argument := 136589352174591718011269770379264, coefficient := 136589352174591718011269770379264 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 116288992440370409573336481792, coefficient := 116288992440370409573336481792 }, { argument := 6034957691516228840133230592, coefficient := 6034957691516228840133230592 }, { argument := 125109315220278744031992741888, coefficient := 125109315220278744031992741888 }, { argument := 187315802194369102845673734144, coefficient := 187315802194369102845673734144 }, { argument := 5802843934150220038589644800, coefficient := 5802843934150220038589644800 }, { argument := 187315802194369102845673734144, coefficient := 187315802194369102845673734144 }, { argument := 195207669944813402098155651072, coefficient := 195207669944813402098155651072 }, { argument := 116288992440370409573336481792, coefficient := 116288992440370409573336481792 }, { argument := 5802843934150220038589644800, coefficient := 5802843934150220038589644800 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 294416958405668330691243278336, coefficient := 294416958405668330691243278336 }, { argument := 332406243361238437877210152960, coefficient := 332406243361238437877210152960 }, { argument := 284919637166775803894751559680, coefficient := 284919637166775803894751559680 }, { argument := 3751441889362548084614228869120, coefficient := 3751441889362548084614228869120 }, { argument := 332406243361238437877210152960, coefficient := 332406243361238437877210152960 }, { argument := 284919637166775803894751559680, coefficient := 284919637166775803894751559680 }, { argument := 332406243361238437877210152960, coefficient := 332406243361238437877210152960 }, { argument := 332406243361238437877210152960, coefficient := 332406243361238437877210152960 }, { argument := 13780613117633056381709483769856, coefficient := 13780613117633056381709483769856 }, { argument := 341903564600130964673701871616, coefficient := 341903564600130964673701871616 }, { argument := 3751441889362548084614228869120, coefficient := 3751441889362548084614228869120 }, { argument := 13780613117633056381709483769856, coefficient := 13780613117633056381709483769856 }] }

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


end Parent1

namespace Parent1

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-7780000668556689793123546638057472)
def positiveArguments : Array ℕ := #[
    15221, 17185, 4419, 17185, 3369, 97701,
    86471, 5615, 3369, 5615, 171819, 5615,
    3369, 2752473, 176311, 97701, 171819, 5615,
    176311, 5615, 171819, 5615, 3369, 2303,
    1715, 1813, 147, 31507, 56987, 1715,
    31507, 931, 931, 1813, 1813, 56987,
    1813, 2303, 147, 36422043, 265353571, 72844135,
    229879223, 2297632171, 4595263219, 229879223, 2042069, 83663945,
    1722705415, 83663945, 2042069, 126249, 25039575, 25039575,
    126249
  ]
def positiveCoefficients : Array ℕ := #[
    294416958405668330691243278336, 332406243361238437877210152960, 341903564600130964673701871616, 332406243361238437877210152960, 130331874761013942066723422208, 1889812184034702159967489622016,
    3345184785532691179712567836672, 108609895634178285055602851840, 2085309996176223073067574755328, 108609895634178285055602851840, 3323462806405855522701447266304, 3475516660293705121779291258880,
    2085309996176223073067574755328, 53240570839874195334256517971968, 3410350722913198150745929547776, 1889812184034702159967489622016, 3323462806405855522701447266304, 108609895634178285055602851840,
    3410350722913198150745929547776, 108609895634178285055602851840, 3323462806405855522701447266304, 3475516660293705121779291258880, 130331874761013942066723422208, 89092997202319711659146346496,
    66345848980450849107874938880, 70137040350762326199753506816, 90988592887475450205085630464, 1218868025555139885038959591424, 2204577781836123928927387254784, 66345848980450849107874938880,
    1218868025555139885038959591424, 72032636035918064745692790784, 72032636035918064745692790784, 70137040350762326199753506816, 70137040350762326199753506816, 2204577781836123928927387254784,
    70137040350762326199753506816, 89092997202319711659146346496, 90988592887475450205085630464, 1375985880806695850943839207424, 5012387239200682739829166833664, 1375986806390526493394301091840,
    1085573937803316852010105438208, 43401044617173668969376397656064, 43401034010738548444153247694848, 1085573937803316852010105438208, 19286796402614267063773954048, 3160734477541195514625403125760,
    32540985246616170195051725455360, 3160734477541195514625403125760, 19286796402614267063773954048, 2384776184383239354335625216, 472984198901202786206928076800, 472984198901202786206928076800,
    2384776184383239354335625216
  ]
def positiveScales : Array ℕ := #[
    13, 14, 12, 14, 11, 16,
    16, 12, 11, 12, 17, 12,
    11, 21, 17, 16, 17, 12,
    17, 12, 17, 12, 11, 11,
    10, 10, 7, 14, 15, 10,
    14, 9, 9, 10, 10, 15,
    10, 11, 7, 25, 27, 26,
    27, 31, 32, 27, 20, 26,
    30, 26, 20, 16, 24, 24,
    16
  ]
def negativeArguments : Array ℕ := #[
    491, 1123, 49, 49, 1123, 491,
    3
  ]
def negativeCoefficients : Array ℕ := #[
    38901027794503789758430079614976, 88973226503518851117549856227328, 7764359926397905084167307132928, 7764359926397905084167307132928, 88973226503518851117549856227328, 38901027794503789758430079614976,
    950737950171172051122527404032
  ]
def negativeScales : Array ℕ := #[
    8, 10, 5, 5, 10, 8,
    1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13893775524460172, 14068862231259659, 12109504215757005, 14068862231259659, 11718104713114918, 16576085708249149,
    16399928753095501, 12455070307287959, 11718104713114918, 12455070307287959, 17390530055093252, 12455070307287959,
    11718104713114918, 21392296981267440, 17427762961292226, 16576085708249149, 17390530055093252, 12455070307287959,
    17427762961292226, 12455070307287959, 17390530055093252, 12455070307287959, 11718104713114918, 11169298695792845,
    10743992861047947, 10824163209679199, 7199672344836364, 14943384770867824, 15798345225549727, 10743992861047947,
    14943384770867824, 9862637357422660, 9862637357422660, 10824163209679199, 10824163209679199, 15798345225549727,
    10824163209679199, 11169298695792845, 7199672344836364, 25118308513031034, 27983340721954241, 26118309483487760,
    27776300837007725, 31097500708737416, 32097500356168639, 27776300837007725, 20961600183179594, 26318102691093201,
    30682028873796902, 26318102691093201, 20961600183179594, 16945912434367994, 24577706739636997, 24577706739636997,
    16945912434367994
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    8939579223047345, 10133142212400602, 5614709844123661, 5614709844123661, 10133142212400602, 8939579223047345,
    1584962500724866
  ]

abbrev PositiveTerm := Fin 55
abbrev NegativeTerm := Fin 7
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
noncomputable def positiveFloor : ℝ := 36280951381 / 500000000000
noncomputable def negativeCeiling : ℝ := 31144339453 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 294416958405668330691243278336, coefficient := 294416958405668330691243278336 }, { argument := 332406243361238437877210152960, coefficient := 332406243361238437877210152960 }, { argument := 341903564600130964673701871616, coefficient := 341903564600130964673701871616 }, { argument := 332406243361238437877210152960, coefficient := 332406243361238437877210152960 }, { argument := 38901027794503789758430079614976, coefficient := (-38901027794503789758430079614976) }, { argument := 130331874761013942066723422208, coefficient := 130331874761013942066723422208 }, { argument := 1889812184034702159967489622016, coefficient := 1889812184034702159967489622016 }, { argument := 3345184785532691179712567836672, coefficient := 3345184785532691179712567836672 }, { argument := 108609895634178285055602851840, coefficient := 108609895634178285055602851840 }, { argument := 2085309996176223073067574755328, coefficient := 2085309996176223073067574755328 }, { argument := 108609895634178285055602851840, coefficient := 108609895634178285055602851840 }, { argument := 3323462806405855522701447266304, coefficient := 3323462806405855522701447266304 }, { argument := 3475516660293705121779291258880, coefficient := 3475516660293705121779291258880 }, { argument := 2085309996176223073067574755328, coefficient := 2085309996176223073067574755328 }, { argument := 53240570839874195334256517971968, coefficient := 53240570839874195334256517971968 }, { argument := 3410350722913198150745929547776, coefficient := 3410350722913198150745929547776 }, { argument := 1889812184034702159967489622016, coefficient := 1889812184034702159967489622016 }, { argument := 3323462806405855522701447266304, coefficient := 3323462806405855522701447266304 }, { argument := 108609895634178285055602851840, coefficient := 108609895634178285055602851840 }, { argument := 3410350722913198150745929547776, coefficient := 3410350722913198150745929547776 }, { argument := 108609895634178285055602851840, coefficient := 108609895634178285055602851840 }, { argument := 3323462806405855522701447266304, coefficient := 3323462806405855522701447266304 }, { argument := 3475516660293705121779291258880, coefficient := 3475516660293705121779291258880 }, { argument := 130331874761013942066723422208, coefficient := 130331874761013942066723422208 }, { argument := 88973226503518851117549856227328, coefficient := (-88973226503518851117549856227328) }, { argument := 89092997202319711659146346496, coefficient := 89092997202319711659146346496 }, { argument := 66345848980450849107874938880, coefficient := 66345848980450849107874938880 }, { argument := 70137040350762326199753506816, coefficient := 70137040350762326199753506816 }, { argument := 90988592887475450205085630464, coefficient := 90988592887475450205085630464 }, { argument := 1218868025555139885038959591424, coefficient := 1218868025555139885038959591424 }, { argument := 2204577781836123928927387254784, coefficient := 2204577781836123928927387254784 }, { argument := 66345848980450849107874938880, coefficient := 66345848980450849107874938880 }, { argument := 1218868025555139885038959591424, coefficient := 1218868025555139885038959591424 }, { argument := 72032636035918064745692790784, coefficient := 72032636035918064745692790784 }, { argument := 72032636035918064745692790784, coefficient := 72032636035918064745692790784 }, { argument := 70137040350762326199753506816, coefficient := 70137040350762326199753506816 }, { argument := 70137040350762326199753506816, coefficient := 70137040350762326199753506816 }, { argument := 2204577781836123928927387254784, coefficient := 2204577781836123928927387254784 }, { argument := 70137040350762326199753506816, coefficient := 70137040350762326199753506816 }, { argument := 89092997202319711659146346496, coefficient := 89092997202319711659146346496 }, { argument := 90988592887475450205085630464, coefficient := 90988592887475450205085630464 }, { argument := 7764359926397905084167307132928, coefficient := (-7764359926397905084167307132928) }, { argument := 1375985880806695850943839207424, coefficient := 1375985880806695850943839207424 }, { argument := 5012387239200682739829166833664, coefficient := 5012387239200682739829166833664 }, { argument := 1375986806390526493394301091840, coefficient := 1375986806390526493394301091840 }, { argument := 7764359926397905084167307132928, coefficient := (-7764359926397905084167307132928) }, { argument := 1085573937803316852010105438208, coefficient := 1085573937803316852010105438208 }, { argument := 43401044617173668969376397656064, coefficient := 43401044617173668969376397656064 }, { argument := 43401034010738548444153247694848, coefficient := 43401034010738548444153247694848 }, { argument := 1085573937803316852010105438208, coefficient := 1085573937803316852010105438208 }, { argument := 88973226503518851117549856227328, coefficient := (-88973226503518851117549856227328) }, { argument := 19286796402614267063773954048, coefficient := 19286796402614267063773954048 }, { argument := 3160734477541195514625403125760, coefficient := 3160734477541195514625403125760 }, { argument := 32540985246616170195051725455360, coefficient := 32540985246616170195051725455360 }, { argument := 3160734477541195514625403125760, coefficient := 3160734477541195514625403125760 }, { argument := 19286796402614267063773954048, coefficient := 19286796402614267063773954048 }, { argument := 38901027794503789758430079614976, coefficient := (-38901027794503789758430079614976) }, { argument := 2384776184383239354335625216, coefficient := 2384776184383239354335625216 }, { argument := 472984198901202786206928076800, coefficient := 472984198901202786206928076800 }, { argument := 472984198901202786206928076800, coefficient := 472984198901202786206928076800 }, { argument := 2384776184383239354335625216, coefficient := 2384776184383239354335625216 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1
