import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 7, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent0

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 26862115177800343840631078078382080
def positiveArguments : Array ℕ := #[
    3703, 3, 13203, 14445, 13203, 14445,
    483, 80661, 2093, 86779, 129927, 4025,
    129927, 135401, 80661, 4025, 3813, 4305,
    1845, 48585
  ]
def positiveCoefficients : Array ℕ := #[
    293381885790320842108893248094208, 475368975085586025561263702016, 510766323083902367796660535296, 558813870858666189716182794240, 510766323083902367796660535296, 558813870858666189716182794240,
    74740629871854834097034625024, 1560210648574969661775597797376, 80969015694509403605120843776, 1678549979205406482429235953664, 2513153679441118796512789266432, 77854822783182118851077734400,
    2513153679441118796512789266432, 2619036238426246478150254985216, 1560210648574969661775597797376, 77854822783182118851077734400, 295016585612197186761897541632, 333083241820222630215045611520,
    285499921560190825898610524160, 3759082300542512540998371901440
  ]
def positiveScales : Array ℕ := #[
    11, 1, 13, 13, 13, 13,
    8, 16, 11, 16, 16, 11,
    16, 17, 16, 11, 11, 12,
    10, 15
  ]
def negativeArguments : Array ℕ := #[
    71932322175, 6172691905, 22930012175, 385712035, 2982107845465, 2982108556455,
    1071, 18496878435, 18496882845, 35, 3677192205, 13659852675,
    229776135, 811807442425, 811807635975, 21, 2982107845465, 2982108556455,
    17157, 1099, 1301365954769643, 391371225, 1301366629862677, 391371225,
    69098007, 1071, 183492625, 681629375, 11465875, 71932305025,
    71932322175, 35, 18496878435, 18496882845, 1099, 35,
    71932305025, 71932322175, 1071, 35, 831285, 3,
    27, 161
  ]
def negativeCoefficients : Array ℕ := #[
    82932321111865463388556492800, 227732135634787345162525736960, 845968132398538231937341849600, 227684198265430436887836753920, 3438136264093390507486310563840, 3438137083809051067908442030080,
    165729222759330284302120255488, 85301795663240563934877450240, 85301816000775905199658106880, 173311605499953238485877391360, 135664447030949417272800706560, 503959612760603631629736345600,
    135635889810916348253039493120, 935950257971667298729905356800, 935950481119624515385137561600, 103986963299971943091526434816, 3438136264093390507486310563840, 3438137083809051067908442030080,
    2654917156752408672055534288896, 170062012896829115264267190272, 366301951810825872906343415808, 3609762412694598755077324800, 366302141832621895582442586112, 3609762412694598755077324800,
    326306112289892125063482703872, 165729222759330284302120255488, 6769682985576318227185664000, 25147685267495191199088640000, 6768257974596624164323328000, 82932301339261659381130854400,
    82932321111865463388556492800, 5415987671873538702683668480, 85301795663240563934877450240, 85301816000775905199658106880, 170062012896829115264267190272, 5415987671873538702683668480,
    82932301339261659381130854400, 82932321111865463388556492800, 165729222759330284302120255488, 173311605499953238485877391360, 7851264843424586042934558720, 475368975085586025561263702016,
    2139160387885137115025686659072, 12755734164796558352560576004096
  ]
def negativeScales : Array ℕ := #[
    36, 32, 34, 28, 41, 41,
    10, 34, 34, 5, 31, 33,
    27, 39, 39, 4, 41, 41,
    14, 10, 50, 28, 50, 28,
    26, 10, 27, 29, 23, 36,
    36, 5, 34, 34, 10, 5,
    36, 36, 10, 5, 19, 1,
    4, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11854478834054907, 1584962500720924, 13688578157112273, 13818282583394157, 13688578157112273, 13818282583394157,
    8915879378478017, 16299583671309825, 11031356596255709, 16405058340867121, 16987341740200876, 11974773066918090,
    16987341740200876, 17046878868369761, 16299583671309825, 11974773066918090, 11896710815471615, 12071797522284206,
    10849405100841772, 15568223348403562
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    36065921127930178, 32523252638508089, 34416518069810985, 28522948920788046, 41439469571086686, 41439469915051987,
    10064742764750256, 34106562768462222, 34106563112427524, 5129283016944967, 31775957441840083, 33669222872785524,
    27775653724117542, 39562346610086300, 39562346954051602, 4392317422778766, 41439469571086686, 41439469915051987,
    14066509690924444, 10101975670949232, 50208948140086280, 28543962446909700, 50208948888494609, 28543962446909700,
    26042140763642983, 10064742764750256, 27451146838027139, 29344412269330553, 23450843120307101, 36065920783964876,
    36065921127930178, 5129283016944967, 34106562768462222, 34106563112427524, 10101975670949232, 5129283016944967,
    36065920783964876, 36065921127930178, 10064742764750256, 5129283016944967, 19664983653744600, 1584962500724866,
    4754887502413606, 7330916878114618
  ]

abbrev PositiveTerm := Fin 20
abbrev NegativeTerm := Fin 44
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
noncomputable def positiveFloor : ℝ := 9121860567 / 200000000000
noncomputable def negativeCeiling : ℝ := 1411113203 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 82932321111865463388556492800, coefficient := (-82932321111865463388556492800) }, { argument := 227732135634787345162525736960, coefficient := (-227732135634787345162525736960) }, { argument := 845968132398538231937341849600, coefficient := (-845968132398538231937341849600) }, { argument := 227684198265430436887836753920, coefficient := (-227684198265430436887836753920) }, { argument := 3438136264093390507486310563840, coefficient := (-3438136264093390507486310563840) }, { argument := 3438137083809051067908442030080, coefficient := (-3438137083809051067908442030080) }, { argument := 165729222759330284302120255488, coefficient := (-165729222759330284302120255488) }, { argument := 85301795663240563934877450240, coefficient := (-85301795663240563934877450240) }, { argument := 85301816000775905199658106880, coefficient := (-85301816000775905199658106880) }, { argument := 173311605499953238485877391360, coefficient := (-173311605499953238485877391360) }, { argument := 135664447030949417272800706560, coefficient := (-135664447030949417272800706560) }, { argument := 503959612760603631629736345600, coefficient := (-503959612760603631629736345600) }, { argument := 135635889810916348253039493120, coefficient := (-135635889810916348253039493120) }, { argument := 935950257971667298729905356800, coefficient := (-935950257971667298729905356800) }, { argument := 935950481119624515385137561600, coefficient := (-935950481119624515385137561600) }, { argument := 103986963299971943091526434816, coefficient := (-103986963299971943091526434816) }, { argument := 3438136264093390507486310563840, coefficient := (-3438136264093390507486310563840) }, { argument := 3438137083809051067908442030080, coefficient := (-3438137083809051067908442030080) }, { argument := 2654917156752408672055534288896, coefficient := (-2654917156752408672055534288896) }, { argument := 170062012896829115264267190272, coefficient := (-170062012896829115264267190272) }, { argument := 366301951810825872906343415808, coefficient := (-366301951810825872906343415808) }, { argument := 3609762412694598755077324800, coefficient := (-3609762412694598755077324800) }, { argument := 366302141832621895582442586112, coefficient := (-366302141832621895582442586112) }, { argument := 3609762412694598755077324800, coefficient := (-3609762412694598755077324800) }, { argument := 326306112289892125063482703872, coefficient := (-326306112289892125063482703872) }, { argument := 165729222759330284302120255488, coefficient := (-165729222759330284302120255488) }, { argument := 6769682985576318227185664000, coefficient := (-6769682985576318227185664000) }, { argument := 25147685267495191199088640000, coefficient := (-25147685267495191199088640000) }, { argument := 6768257974596624164323328000, coefficient := (-6768257974596624164323328000) }, { argument := 82932301339261659381130854400, coefficient := (-82932301339261659381130854400) }, { argument := 82932321111865463388556492800, coefficient := (-82932321111865463388556492800) }, { argument := 5415987671873538702683668480, coefficient := (-5415987671873538702683668480) }, { argument := 85301795663240563934877450240, coefficient := (-85301795663240563934877450240) }, { argument := 85301816000775905199658106880, coefficient := (-85301816000775905199658106880) }, { argument := 170062012896829115264267190272, coefficient := (-170062012896829115264267190272) }, { argument := 5415987671873538702683668480, coefficient := (-5415987671873538702683668480) }, { argument := 82932301339261659381130854400, coefficient := (-82932301339261659381130854400) }, { argument := 82932321111865463388556492800, coefficient := (-82932321111865463388556492800) }, { argument := 165729222759330284302120255488, coefficient := (-165729222759330284302120255488) }, { argument := 173311605499953238485877391360, coefficient := (-173311605499953238485877391360) }, { argument := 7851264843424586042934558720, coefficient := (-7851264843424586042934558720) }, { argument := 293381885790320842108893248094208, coefficient := 293381885790320842108893248094208 }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 510766323083902367796660535296, coefficient := 510766323083902367796660535296 }, { argument := 558813870858666189716182794240, coefficient := 558813870858666189716182794240 }, { argument := 510766323083902367796660535296, coefficient := 510766323083902367796660535296 }, { argument := 558813870858666189716182794240, coefficient := 558813870858666189716182794240 }, { argument := 2139160387885137115025686659072, coefficient := (-2139160387885137115025686659072) }, { argument := 74740629871854834097034625024, coefficient := 74740629871854834097034625024 }, { argument := 1560210648574969661775597797376, coefficient := 1560210648574969661775597797376 }, { argument := 80969015694509403605120843776, coefficient := 80969015694509403605120843776 }, { argument := 1678549979205406482429235953664, coefficient := 1678549979205406482429235953664 }, { argument := 2513153679441118796512789266432, coefficient := 2513153679441118796512789266432 }, { argument := 77854822783182118851077734400, coefficient := 77854822783182118851077734400 }, { argument := 2513153679441118796512789266432, coefficient := 2513153679441118796512789266432 }, { argument := 2619036238426246478150254985216, coefficient := 2619036238426246478150254985216 }, { argument := 1560210648574969661775597797376, coefficient := 1560210648574969661775597797376 }, { argument := 77854822783182118851077734400, coefficient := 77854822783182118851077734400 }, { argument := 12755734164796558352560576004096, coefficient := (-12755734164796558352560576004096) }, { argument := 295016585612197186761897541632, coefficient := 295016585612197186761897541632 }, { argument := 333083241820222630215045611520, coefficient := 333083241820222630215045611520 }, { argument := 285499921560190825898610524160, coefficient := 285499921560190825898610524160 }, { argument := 3759082300542512540998371901440, coefficient := 3759082300542512540998371901440 }] }

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
def constantNumerator : ℤ := (-12905287163907900619648683885985792)
def positiveArguments : Array ℕ := #[
    4305, 1845, 4305, 4305, 178473, 1107,
    48585, 178473, 3813, 4305, 1107, 4305,
    339, 9831, 8701, 565, 339, 565,
    17289, 565, 339, 276963, 17741, 9831,
    17289, 565, 17741, 565, 17289, 565,
    339, 45, 1765801549, 1765802419, 10305458877, 37285914785,
    5153399377, 125245125, 4987611655, 4987610953, 125245419, 144187,
    24902919, 512179931, 49805867, 144187
  ]
def positiveCoefficients : Array ℕ := #[
    333083241820222630215045611520, 285499921560190825898610524160, 333083241820222630215045611520, 333083241820222630215045611520, 13808679539461229612629462351872, 342599905872228991078332628992,
    3759082300542512540998371901440, 13808679539461229612629462351872, 295016585612197186761897541632, 333083241820222630215045611520, 342599905872228991078332628992, 333083241820222630215045611520,
    13114427291179497287212597248, 190159195722102710664582660096, 336603633806940430371789996032, 10928689409316247739343831040, 209830836658871956595401555968, 10928689409316247739343831040,
    334417895925077180823921229824, 349718061098119927659002593280, 209830836658871956595401555968, 5357243548446824641826345975808, 343160847452530179015396294656, 190159195722102710664582660096,
    334417895925077180823921229824, 10928689409316247739343831040, 343160847452530179015396294656, 10928689409316247739343831040, 334417895925077180823921229824, 349718061098119927659002593280,
    13114427291179497287212597248, 14261069252567580766837911060480, 66710096403175211867398662520832, 66710129270845932640129349844992, 48666153591336253701324005179392, 176077754263817753701052170895360,
    48672480981572221632943996534784, 1182906760885638146990014464000, 47106660218284000627090270453760, 47106653588081458678108390424576, 1182909537637130074341400117248, 2723615424262102137708740608,
    470402840044870649261636714496, 4837402678705775135090595069952, 470403113942126655701059108864, 2723615424262102137708740608
  ]
def positiveScales : Array ℕ := #[
    12, 10, 12, 12, 17, 10,
    15, 17, 11, 12, 10, 12,
    8, 13, 13, 9, 8, 9,
    14, 9, 8, 18, 14, 13,
    14, 9, 14, 9, 14, 9,
    8, 5, 30, 30, 33, 35,
    32, 26, 32, 32, 26, 17,
    24, 28, 25, 17
  ]
def negativeArguments : Array ℕ := #[
    123, 113, 45, 421, 3451, 1219,
    73
  ]
def negativeCoefficients : Array ℕ := #[
    38980255957018054096023623565312, 8952782364111870148070466387968, 14261069252567580766837911060480, 133420225674021144507528012365824, 273416388836726229035320172609536, 96579130104888227526530075459584,
    5783655863541296644328708374528
  ]
def negativeScales : Array ℕ := #[
    6, 6, 5, 8, 11, 10,
    6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12071797522284206, 10849405100841772, 12071797522284206, 12071797522284206, 17445346309405981, 10112439506781552,
    15568223348403562, 17445346309405981, 11896710815471615, 12071797522284206, 10112439506781552, 12071797522284206,
    8405141463136342, 13263122458263915, 13086965503110088, 9142107057302549, 8405141463136342, 9142107057302549,
    14077566805107839, 9142107057302549, 8405141463136342, 18079333731282027, 14114799711306814, 13263122458263915,
    14077566805107839, 9142107057302549, 14114799711306814, 9142107057302549, 14077566805107839, 9142107057302549,
    8405141463136342, 5491853096329661, 30717676067656001, 30717676778463157, 33262689694879661, 35117911686390619,
    32262877256469530, 26900179208354731, 32215701992526602, 32215701789469095, 26900182594928398, 17137581570492733,
    24569811522167589, 28932075482833052, 25569812362192487, 17137581570492733
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6942514514520450, 6820178963384638, 5491853096329881, 8717676423175508, 11752798758674552, 10251482410620213,
    6189824558880018
  ]

abbrev PositiveTerm := Fin 46
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
noncomputable def positiveFloor : ℝ := 8438597963 / 40000000000
noncomputable def negativeCeiling : ℝ := 69964237963 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 333083241820222630215045611520, coefficient := 333083241820222630215045611520 }, { argument := 285499921560190825898610524160, coefficient := 285499921560190825898610524160 }, { argument := 333083241820222630215045611520, coefficient := 333083241820222630215045611520 }, { argument := 333083241820222630215045611520, coefficient := 333083241820222630215045611520 }, { argument := 13808679539461229612629462351872, coefficient := 13808679539461229612629462351872 }, { argument := 342599905872228991078332628992, coefficient := 342599905872228991078332628992 }, { argument := 3759082300542512540998371901440, coefficient := 3759082300542512540998371901440 }, { argument := 13808679539461229612629462351872, coefficient := 13808679539461229612629462351872 }, { argument := 295016585612197186761897541632, coefficient := 295016585612197186761897541632 }, { argument := 333083241820222630215045611520, coefficient := 333083241820222630215045611520 }, { argument := 342599905872228991078332628992, coefficient := 342599905872228991078332628992 }, { argument := 333083241820222630215045611520, coefficient := 333083241820222630215045611520 }, { argument := 38980255957018054096023623565312, coefficient := (-38980255957018054096023623565312) }, { argument := 13114427291179497287212597248, coefficient := 13114427291179497287212597248 }, { argument := 190159195722102710664582660096, coefficient := 190159195722102710664582660096 }, { argument := 336603633806940430371789996032, coefficient := 336603633806940430371789996032 }, { argument := 10928689409316247739343831040, coefficient := 10928689409316247739343831040 }, { argument := 209830836658871956595401555968, coefficient := 209830836658871956595401555968 }, { argument := 10928689409316247739343831040, coefficient := 10928689409316247739343831040 }, { argument := 334417895925077180823921229824, coefficient := 334417895925077180823921229824 }, { argument := 349718061098119927659002593280, coefficient := 349718061098119927659002593280 }, { argument := 209830836658871956595401555968, coefficient := 209830836658871956595401555968 }, { argument := 5357243548446824641826345975808, coefficient := 5357243548446824641826345975808 }, { argument := 343160847452530179015396294656, coefficient := 343160847452530179015396294656 }, { argument := 190159195722102710664582660096, coefficient := 190159195722102710664582660096 }, { argument := 334417895925077180823921229824, coefficient := 334417895925077180823921229824 }, { argument := 10928689409316247739343831040, coefficient := 10928689409316247739343831040 }, { argument := 343160847452530179015396294656, coefficient := 343160847452530179015396294656 }, { argument := 10928689409316247739343831040, coefficient := 10928689409316247739343831040 }, { argument := 334417895925077180823921229824, coefficient := 334417895925077180823921229824 }, { argument := 349718061098119927659002593280, coefficient := 349718061098119927659002593280 }, { argument := 13114427291179497287212597248, coefficient := 13114427291179497287212597248 }, { argument := 8952782364111870148070466387968, coefficient := (-8952782364111870148070466387968) }, { argument := 14261069252567580766837911060480, coefficient := 14261069252567580766837911060480 }, { argument := 14261069252567580766837911060480, coefficient := (-14261069252567580766837911060480) }, { argument := 66710096403175211867398662520832, coefficient := 66710096403175211867398662520832 }, { argument := 66710129270845932640129349844992, coefficient := 66710129270845932640129349844992 }, { argument := 133420225674021144507528012365824, coefficient := (-133420225674021144507528012365824) }, { argument := 48666153591336253701324005179392, coefficient := 48666153591336253701324005179392 }, { argument := 176077754263817753701052170895360, coefficient := 176077754263817753701052170895360 }, { argument := 48672480981572221632943996534784, coefficient := 48672480981572221632943996534784 }, { argument := 273416388836726229035320172609536, coefficient := (-273416388836726229035320172609536) }, { argument := 1182906760885638146990014464000, coefficient := 1182906760885638146990014464000 }, { argument := 47106660218284000627090270453760, coefficient := 47106660218284000627090270453760 }, { argument := 47106653588081458678108390424576, coefficient := 47106653588081458678108390424576 }, { argument := 1182909537637130074341400117248, coefficient := 1182909537637130074341400117248 }, { argument := 96579130104888227526530075459584, coefficient := (-96579130104888227526530075459584) }, { argument := 2723615424262102137708740608, coefficient := 2723615424262102137708740608 }, { argument := 470402840044870649261636714496, coefficient := 470402840044870649261636714496 }, { argument := 4837402678705775135090595069952, coefficient := 4837402678705775135090595069952 }, { argument := 470403113942126655701059108864, coefficient := 470403113942126655701059108864 }, { argument := 2723615424262102137708740608, coefficient := 2723615424262102137708740608 }, { argument := 5783655863541296644328708374528, coefficient := (-5783655863541296644328708374528) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7
