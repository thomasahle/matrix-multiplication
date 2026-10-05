import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 10, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10

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
def constantNumerator : ℤ := (-10102665893034594742159367653556224)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1828125, 285, 62005131, 1881, 93, 939,
    1911, 229227, 285, 93, 277970525966281, 16874133226934327,
    36792439017, 2982936927, 639337833951, 1155879015303, 33748164171571025, 639337833951,
    18880661679, 18886953135, 36792439017, 36779856105, 1155879015303, 36779856105,
    555940255015087, 2982936927, 19290352604923, 10589874976108491, 319728401797, 26547666951728279,
    12456983115, 20762183293, 635305192689, 20761430653, 12456983115, 10177265662299,
    651909571925, 10589887248302593, 635305192689, 20762183293, 651909571925, 20762183293,
    635305192689, 20761452157, 19290352604923, 10521, 157815, 277053,
    10521, 87675, 10521, 277053, 550599, 87675,
    8497461, 543585, 157815, 277053, 10521, 543585,
    10521, 277053, 277053, 10521
  ]
def negativeCoefficients : Array ℕ := #[
    8633076226496070156288000000, 88203227799083344586562600960, 292810952400341607398743474176, 72767662934243759283914145792, 3597763239173136423925579776, 72651606055560754883142352896,
    73928231721073803291632074752, 8659951214150081307199143936, 88203227799083344586562600960, 3597763239173136423925579776, 156483494645215486770698780672, 9499292514127692536842786177024,
    84837588299270603850261725184, 110050948160773262775957848064, 1474212674941738826959108964352, 2665275546933230921540966547456, 9499263724220349501682378342400, 1474212674941738826959108964352,
    87071683483702070643120930816, 87100697703372821743313879040, 84837588299270603850261725184, 84808574079599852750068776960, 2665275546933230921540966547456, 84808574079599852750068776960,
    156483270332887770830913667072, 110050948160773262775957848064, 86876024803376699642434551808, 11923139249075585074570287120384, 737243500130679512919644831744, 119560062991359508724699453456384,
    459581558905852399789465927680, 23937167601088700818514771968, 732457018639544719276416958464, 765961595719919152678616170496, 459581558905852399789465927680, 11733588440161362068810785357824,
    751600564531376527548140748800, 11923153066337781270969982124032, 732457018639544719276416958464, 23937167601088700818514771968, 751600564531376527548140748800, 23937167601088700818514771968,
    732457018639544719276416958464, 765962389077488274779012071424, 86876024803376699642434551808, 99368035532543074586591232, 1490520532988146118798868480, 2616691602356967630780235776,
    99368035532543074586591232, 1656133925542384576443187200, 99368035532543074586591232, 2616691602356967630780235776, 2600130263101543785015803904, 1656133925542384576443187200,
    40128125015891978287218425856, 2567007584590696093486940160, 1490520532988146118798868480, 2616691602356967630780235776, 99368035532543074586591232, 2567007584590696093486940160,
    99368035532543074586591232, 2616691602356967630780235776, 2616691602356967630780235776, 99368035532543074586591232
  ]
def negativeScales : Array ℕ := #[
    20, 8, 25, 10, 6, 9,
    10, 17, 8, 6, 47, 53,
    35, 31, 39, 40, 54, 39,
    34, 34, 35, 35, 40, 35,
    48, 31, 44, 53, 38, 54,
    33, 34, 39, 34, 33, 43,
    39, 53, 39, 34, 39, 34,
    39, 34, 44, 13, 17, 18,
    13, 16, 13, 18, 19, 16,
    23, 19, 17, 18, 13, 19,
    13, 18, 18, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    20801933289579550, 8154818109052105, 25885884272803755, 10877284136413052, 6539158811108986, 9874981350423323,
    10900112067353854, 17806417460244627, 8154818109052105, 6539158811108986, 47981925263972134, 53905662920226800,
    35098690266421166, 31474086326776383, 39217787514168432, 40072127538946507, 54905658547782957, 39217787514168432,
    34136190274181673, 34136670932147490, 35098690266421166, 35098196784332855, 40072127538946507, 35098196784332855,
    48981923195929056, 31474086326776383, 44132944747929702, 53233535075194431, 38218055949630121, 54559434598623848,
    33536235661535553, 34273239110313381, 39208658854865772, 34273186810915881, 33536235661535553, 43210415236469658,
    39245880902108177, 53233536747076616, 39208658854865772, 34273239110313381, 39245880902108177, 34273239110313381,
    39208658854865772, 34273188305210692, 44132944747929702, 13360984215973970, 17267874811582488, 18079802463429916,
    13360984215973970, 16419877905027552, 13360984215973970, 18079802463429916, 19070642464144440, 16419877905027552,
    23018600404704159, 19052146120527051, 17267874811582488, 18079802463429916, 13360984215973970, 19052146120527051,
    13360984215973970, 18079802463429916, 18079802463429916, 13360984215973970
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
noncomputable def negativeCeiling : ℝ := 120157646117 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8633076226496070156288000000, coefficient := (-8633076226496070156288000000) }, { argument := 88203227799083344586562600960, coefficient := (-88203227799083344586562600960) }, { argument := 292810952400341607398743474176, coefficient := (-292810952400341607398743474176) }, { argument := 72767662934243759283914145792, coefficient := (-72767662934243759283914145792) }, { argument := 3597763239173136423925579776, coefficient := (-3597763239173136423925579776) }, { argument := 72651606055560754883142352896, coefficient := (-72651606055560754883142352896) }, { argument := 73928231721073803291632074752, coefficient := (-73928231721073803291632074752) }, { argument := 8659951214150081307199143936, coefficient := (-8659951214150081307199143936) }, { argument := 88203227799083344586562600960, coefficient := (-88203227799083344586562600960) }, { argument := 3597763239173136423925579776, coefficient := (-3597763239173136423925579776) }, { argument := 156483494645215486770698780672, coefficient := (-156483494645215486770698780672) }, { argument := 9499292514127692536842786177024, coefficient := (-9499292514127692536842786177024) }, { argument := 84837588299270603850261725184, coefficient := (-84837588299270603850261725184) }, { argument := 110050948160773262775957848064, coefficient := (-110050948160773262775957848064) }, { argument := 1474212674941738826959108964352, coefficient := (-1474212674941738826959108964352) }, { argument := 2665275546933230921540966547456, coefficient := (-2665275546933230921540966547456) }, { argument := 9499263724220349501682378342400, coefficient := (-9499263724220349501682378342400) }, { argument := 1474212674941738826959108964352, coefficient := (-1474212674941738826959108964352) }, { argument := 87071683483702070643120930816, coefficient := (-87071683483702070643120930816) }, { argument := 87100697703372821743313879040, coefficient := (-87100697703372821743313879040) }, { argument := 84837588299270603850261725184, coefficient := (-84837588299270603850261725184) }, { argument := 84808574079599852750068776960, coefficient := (-84808574079599852750068776960) }, { argument := 2665275546933230921540966547456, coefficient := (-2665275546933230921540966547456) }, { argument := 84808574079599852750068776960, coefficient := (-84808574079599852750068776960) }, { argument := 156483270332887770830913667072, coefficient := (-156483270332887770830913667072) }, { argument := 110050948160773262775957848064, coefficient := (-110050948160773262775957848064) }, { argument := 86876024803376699642434551808, coefficient := (-86876024803376699642434551808) }, { argument := 11923139249075585074570287120384, coefficient := (-11923139249075585074570287120384) }, { argument := 737243500130679512919644831744, coefficient := (-737243500130679512919644831744) }, { argument := 119560062991359508724699453456384, coefficient := (-119560062991359508724699453456384) }, { argument := 459581558905852399789465927680, coefficient := (-459581558905852399789465927680) }, { argument := 23937167601088700818514771968, coefficient := (-23937167601088700818514771968) }, { argument := 732457018639544719276416958464, coefficient := (-732457018639544719276416958464) }, { argument := 765961595719919152678616170496, coefficient := (-765961595719919152678616170496) }, { argument := 459581558905852399789465927680, coefficient := (-459581558905852399789465927680) }, { argument := 11733588440161362068810785357824, coefficient := (-11733588440161362068810785357824) }, { argument := 751600564531376527548140748800, coefficient := (-751600564531376527548140748800) }, { argument := 11923153066337781270969982124032, coefficient := (-11923153066337781270969982124032) }, { argument := 732457018639544719276416958464, coefficient := (-732457018639544719276416958464) }, { argument := 23937167601088700818514771968, coefficient := (-23937167601088700818514771968) }, { argument := 751600564531376527548140748800, coefficient := (-751600564531376527548140748800) }, { argument := 23937167601088700818514771968, coefficient := (-23937167601088700818514771968) }, { argument := 732457018639544719276416958464, coefficient := (-732457018639544719276416958464) }, { argument := 765962389077488274779012071424, coefficient := (-765962389077488274779012071424) }, { argument := 86876024803376699642434551808, coefficient := (-86876024803376699642434551808) }, { argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }, { argument := 1490520532988146118798868480, coefficient := (-1490520532988146118798868480) }, { argument := 2616691602356967630780235776, coefficient := (-2616691602356967630780235776) }, { argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }, { argument := 1656133925542384576443187200, coefficient := (-1656133925542384576443187200) }, { argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }, { argument := 2616691602356967630780235776, coefficient := (-2616691602356967630780235776) }, { argument := 2600130263101543785015803904, coefficient := (-2600130263101543785015803904) }, { argument := 1656133925542384576443187200, coefficient := (-1656133925542384576443187200) }, { argument := 40128125015891978287218425856, coefficient := (-40128125015891978287218425856) }, { argument := 2567007584590696093486940160, coefficient := (-2567007584590696093486940160) }, { argument := 1490520532988146118798868480, coefficient := (-1490520532988146118798868480) }, { argument := 2616691602356967630780235776, coefficient := (-2616691602356967630780235776) }, { argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }, { argument := 2567007584590696093486940160, coefficient := (-2567007584590696093486940160) }, { argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }, { argument := 2616691602356967630780235776, coefficient := (-2616691602356967630780235776) }, { argument := 2616691602356967630780235776, coefficient := (-2616691602356967630780235776) }, { argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }] }

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
def constantNumerator : ℤ := (-3018073399788445222014840312168448)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    667281244884519, 2840210415, 26042394602294297, 32053803255, 2840210415, 26042398252171877,
    2840210415, 2840210415, 117747008919, 730339821, 32053803255, 117747008919,
    667286444946267, 2840210415, 730339821, 2840210415, 273, 4095,
    7189, 273, 2275, 273, 7189, 14287,
    2275, 220493, 14105, 4095, 7189, 273,
    14105, 273, 7189, 7189, 273, 2928278955,
    57109322865, 114218603835, 366036615, 38661964921245, 10521, 273,
    141198381609639, 16947, 9665035101423, 16947, 17661, 10521,
    525, 277970510590007, 16874138767306697, 36792430359, 2982936225, 639337683489,
    1155878743161, 33748175252316335, 639337683489, 18880657233, 18886948689, 36792430359,
    36779847447, 1155878743161, 36779847447, 555940224261969
  ]
def negativeCoefficients : Array ℕ := #[
    375645945726655057322393468928, 3274539665061837261546455040, 14660564828341001542999855857664, 36955519077126449094595706880, 3274539665061837261546455040, 14660566883039415197490818842624,
    3274539665061837261546455040, 3274539665061837261546455040, 135753058685849310471540178944, 3368097941206461183304925184, 36955519077126449094595706880, 135753058685849310471540178944,
    375648873101173881868652642304, 3274539665061837261546455040, 3368097941206461183304925184, 3274539665061837261546455040, 5156824199293652573356032, 77352362989404788600340480,
    135796370581399517765042176, 5156824199293652573356032, 85947069988227542889267200, 5156824199293652573356032, 135796370581399517765042176, 134936899881517242336149504,
    85947069988227542889267200, 2082497505814753364206944256, 133217958481752691478364160, 77352362989404788600340480, 135796370581399517765042176, 5156824199293652573356032,
    133217958481752691478364160, 5156824199293652573356032, 135796370581399517765042176, 135796370581399517765042176, 5156824199293652573356032, 3376075778707165548726190080,
    131685132889188017684065812480, 131685084587541582180211752960, 3376091879255977383344209920, 87059005406365084865538293760, 99368035532543074586591232, 5156824199293652573356032,
    317950489401243647798748905472, 160059889570383754873012224, 87054896962582773628315631616, 160059889570383754873012224, 166803428907921608238170112, 99368035532543074586591232,
    4958484807013127474380800, 156483485989142754677368029184, 9499295633080060165066760126464, 84837568335281830078099488768, 110050922261544583287747379200, 1474212327999987974648289558528,
    2665274919416502708107867062272, 9499266843172877570643077365760, 1474212327999987974648289558528, 87071662980146032714954309632, 87100677199816783815147257856, 84837568335281830078099488768,
    84808554115611078977906540544, 2665274919416502708107867062272, 84808554115611078977906540544, 156483261676654598000857841664
  ]
def negativeScales : Array ℕ := #[
    49, 31, 54, 34, 31, 54,
    31, 31, 36, 29, 34, 36,
    49, 31, 29, 31, 8, 11,
    12, 8, 11, 8, 12, 13,
    11, 17, 13, 11, 12, 8,
    13, 8, 12, 12, 8, 31,
    35, 36, 28, 45, 13, 8,
    47, 14, 43, 14, 14, 13,
    9, 47, 53, 35, 31, 39,
    40, 54, 39, 34, 34, 35,
    35, 40, 35, 48
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    49245288283356954, 31403350668727516, 54531711628838078, 34899776499197153, 31403350668727516, 54531711831033767,
    31403350668727516, 31403350668727516, 36776899456249659, 29443992653224892, 34899776499197153, 36776899456249659,
    49245299526103730, 31403350668727516, 29443992653224892, 31403350668727516, 8092757140919853, 11999647760072134,
    12811575389192290, 8092757140919853, 11151650829973422, 8092757140919853, 12811575389192290, 13802415389768912,
    11151650829973422, 17750373329876765, 13783919045936705, 11999647760072134, 12811575389192290, 8092757140919853,
    13783919045936705, 8092757140919853, 12811575389192290, 12811575389192290, 8092757140919853, 31447405848805486,
    35733007227947319, 36733006698771722, 28447412729020287, 45135980195195011, 13360984215973970, 8092757140919853,
    47004716881216807, 14048742286056541, 43135912110666539, 14048742286056541, 14108279413033905, 13360984215973970,
    9036173612553486, 47981925184167698, 53905663393914368, 35098689926926002, 31474085987254608, 39217787174644012,
    40072127199276045, 54905659021471985, 39217787174644012, 34136189934457197, 34136670592536180, 35098689926926002,
    35098196444721544, 40072127199276045, 35098196444721544, 48981923116123026
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
noncomputable def negativeCeiling : ℝ := 37087470571 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 375645945726655057322393468928, coefficient := (-375645945726655057322393468928) }, { argument := 3274539665061837261546455040, coefficient := (-3274539665061837261546455040) }, { argument := 14660564828341001542999855857664, coefficient := (-14660564828341001542999855857664) }, { argument := 36955519077126449094595706880, coefficient := (-36955519077126449094595706880) }, { argument := 3274539665061837261546455040, coefficient := (-3274539665061837261546455040) }, { argument := 14660566883039415197490818842624, coefficient := (-14660566883039415197490818842624) }, { argument := 3274539665061837261546455040, coefficient := (-3274539665061837261546455040) }, { argument := 3274539665061837261546455040, coefficient := (-3274539665061837261546455040) }, { argument := 135753058685849310471540178944, coefficient := (-135753058685849310471540178944) }, { argument := 3368097941206461183304925184, coefficient := (-3368097941206461183304925184) }, { argument := 36955519077126449094595706880, coefficient := (-36955519077126449094595706880) }, { argument := 135753058685849310471540178944, coefficient := (-135753058685849310471540178944) }, { argument := 375648873101173881868652642304, coefficient := (-375648873101173881868652642304) }, { argument := 3274539665061837261546455040, coefficient := (-3274539665061837261546455040) }, { argument := 3368097941206461183304925184, coefficient := (-3368097941206461183304925184) }, { argument := 3274539665061837261546455040, coefficient := (-3274539665061837261546455040) }, { argument := 5156824199293652573356032, coefficient := (-5156824199293652573356032) }, { argument := 77352362989404788600340480, coefficient := (-77352362989404788600340480) }, { argument := 135796370581399517765042176, coefficient := (-135796370581399517765042176) }, { argument := 5156824199293652573356032, coefficient := (-5156824199293652573356032) }, { argument := 85947069988227542889267200, coefficient := (-85947069988227542889267200) }, { argument := 5156824199293652573356032, coefficient := (-5156824199293652573356032) }, { argument := 135796370581399517765042176, coefficient := (-135796370581399517765042176) }, { argument := 134936899881517242336149504, coefficient := (-134936899881517242336149504) }, { argument := 85947069988227542889267200, coefficient := (-85947069988227542889267200) }, { argument := 2082497505814753364206944256, coefficient := (-2082497505814753364206944256) }, { argument := 133217958481752691478364160, coefficient := (-133217958481752691478364160) }, { argument := 77352362989404788600340480, coefficient := (-77352362989404788600340480) }, { argument := 135796370581399517765042176, coefficient := (-135796370581399517765042176) }, { argument := 5156824199293652573356032, coefficient := (-5156824199293652573356032) }, { argument := 133217958481752691478364160, coefficient := (-133217958481752691478364160) }, { argument := 5156824199293652573356032, coefficient := (-5156824199293652573356032) }, { argument := 135796370581399517765042176, coefficient := (-135796370581399517765042176) }, { argument := 135796370581399517765042176, coefficient := (-135796370581399517765042176) }, { argument := 5156824199293652573356032, coefficient := (-5156824199293652573356032) }, { argument := 3376075778707165548726190080, coefficient := (-3376075778707165548726190080) }, { argument := 131685132889188017684065812480, coefficient := (-131685132889188017684065812480) }, { argument := 131685084587541582180211752960, coefficient := (-131685084587541582180211752960) }, { argument := 3376091879255977383344209920, coefficient := (-3376091879255977383344209920) }, { argument := 87059005406365084865538293760, coefficient := (-87059005406365084865538293760) }, { argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }, { argument := 5156824199293652573356032, coefficient := (-5156824199293652573356032) }, { argument := 317950489401243647798748905472, coefficient := (-317950489401243647798748905472) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 87054896962582773628315631616, coefficient := (-87054896962582773628315631616) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 166803428907921608238170112, coefficient := (-166803428907921608238170112) }, { argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 156483485989142754677368029184, coefficient := (-156483485989142754677368029184) }, { argument := 9499295633080060165066760126464, coefficient := (-9499295633080060165066760126464) }, { argument := 84837568335281830078099488768, coefficient := (-84837568335281830078099488768) }, { argument := 110050922261544583287747379200, coefficient := (-110050922261544583287747379200) }, { argument := 1474212327999987974648289558528, coefficient := (-1474212327999987974648289558528) }, { argument := 2665274919416502708107867062272, coefficient := (-2665274919416502708107867062272) }, { argument := 9499266843172877570643077365760, coefficient := (-9499266843172877570643077365760) }, { argument := 1474212327999987974648289558528, coefficient := (-1474212327999987974648289558528) }, { argument := 87071662980146032714954309632, coefficient := (-87071662980146032714954309632) }, { argument := 87100677199816783815147257856, coefficient := (-87100677199816783815147257856) }, { argument := 84837568335281830078099488768, coefficient := (-84837568335281830078099488768) }, { argument := 84808554115611078977906540544, coefficient := (-84808554115611078977906540544) }, { argument := 2665274919416502708107867062272, coefficient := (-2665274919416502708107867062272) }, { argument := 84808554115611078977906540544, coefficient := (-84808554115611078977906540544) }, { argument := 156483261676654598000857841664, coefficient := (-156483261676654598000857841664) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10
