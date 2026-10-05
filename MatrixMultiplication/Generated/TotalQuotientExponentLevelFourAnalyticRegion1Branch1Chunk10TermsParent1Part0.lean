import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 10, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-19606513649422019558034870271737856)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3366387, 114749965, 1073, 87, 18647, 33727,
    458999865, 18647, 551, 551, 1073, 1073,
    33727, 1073, 13465543, 87, 145624831578347, 7316209747413677,
    449232875787, 17613417160593691, 17502768165, 29174451603, 892635668319, 29170070163,
    17502768165, 14299240324629, 915943983675, 1829053653201151, 892635668319, 29174451603,
    915943983675, 29174451603, 892635668319, 29170195347, 145624831578347, 675043975309933,
    68299245105, 416750781490079403, 770805766185, 68299245105, 104187705086972873, 68299245105,
    68299245105, 2831491561353, 17562663027, 770805766185, 2831491561353, 10800783142798177,
    68299245105, 17562663027, 68299245105, 1605, 24075, 42265,
    1605, 13375, 1605, 42265, 83995, 13375,
    1296305, 82925, 24075, 42265
  ]
def negativeCoefficients : Array ℕ := #[
    63589252548672385367993745408, 2167565554505859551336134082560, 41509676942287907342711259136, 53850391708914041958111903744, 721370872267327687063874043904, 1304750115780563141610086334464,
    2167565578117691965684360151040, 721370872267327687063874043904, 42631560102890283216838590464, 42631560102890283216838590464, 41509676942287907342711259136, 41509676942287907342711259136,
    1304750115780563141610086334464, 41509676942287907342711259136, 63589228936839971019767676928, 53850391708914041958111903744, 81979492154016848509627531264, 8237319873054156599619064168448,
    1035860486142417671678249140224, 79323778961170846490484577140736, 645738169842451906961898209280, 33635852638210398643738902528, 1029138857784079887765124153344, 1076185637818024128643980066816,
    645738169842451906961898209280, 16485901669806165672114366971904, 1056011515794170283878567116800, 8237325350997348061867090640896, 1029138857784079887765124153344, 33635852638210398643738902528,
    1056011515794170283878567116800, 33635852638210398643738902528, 1029138857784079887765124153344, 1076190256292444375156999061504, 81979492154016848509627531264, 3040127795664512560871419936768,
    78743668429968428275052052480, 117304916514067787568133196218368, 888678543709643690532730306560, 78743668429968428275052052480, 117304927451569540346455368138752, 78743668429968428275052052480,
    78743668429968428275052052480, 3264487511196691126488586518528, 80993487527967526225767825408, 888678543709643690532730306560, 3264487511196691126488586518528, 3040150183575962789047133274112,
    78743668429968428275052052480, 80993487527967526225767825408, 78743668429968428275052052480, 30317592820023122271928320, 454763892300346834078924800, 798363277593942219827445760,
    30317592820023122271928320, 505293213667052037865472000, 30317592820023122271928320, 798363277593942219827445760, 793310345457271699448791040, 505293213667052037865472000,
    12243254567152670877480386560, 783204481183930658691481600, 454763892300346834078924800, 798363277593942219827445760
  ]
def negativeScales : Array ℕ := #[
    21, 26, 10, 6, 14, 15,
    28, 14, 9, 9, 10, 10,
    15, 10, 23, 6, 47, 52,
    38, 53, 34, 34, 39, 34,
    34, 43, 39, 50, 39, 34,
    39, 34, 39, 34, 47, 49,
    35, 58, 39, 35, 56, 35,
    35, 41, 34, 39, 41, 53,
    35, 34, 35, 10, 14, 15,
    10, 13, 10, 15, 16, 13,
    20, 16, 14, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    21682769607860356, 26773918473076193, 10067434360756522, 6442943495848765, 14186655922455520, 15041616376600791,
    28773918488791830, 14186655922455520, 9105908508571158, 9105908508571158, 10067434360756522, 10067434360756522,
    15041616376600791, 10067434360756522, 23682769072161656, 6442943495848765, 47049249709649397, 52700017859488604,
    38708672554845777, 53967524364245240, 34026864059622326, 34763986486787793, 39699280499401115, 34763769805542608,
    34026864059622326, 43701003736627271, 39736468414143679, 50700018818902465, 39699280499401115, 34763986486787793,
    39736468414143679, 34763986486787793, 39699280499401115, 34763775996886977, 47049249709649397, 49261974817097714,
    35991150602264763, 58531962517638479, 39487576407838219, 35991150602264763, 56531962652155252, 35991150602264763,
    35991150602264763, 41364699368840322, 34031792566215888, 39487576407838219, 41364699368840322, 53261985441259615,
    35991150602264763, 34031792566215888, 35991150602264763, 10648357582030099, 14555248177619742, 15367175829465614,
    10648357582030099, 13707251271149006, 10648357582030099, 15367175829465614, 16358015830180138, 13707251271149006,
    20305973770739856, 16339519486562748, 14555248177619742, 15367175829465614
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
noncomputable def negativeCeiling : ℝ := 123910654287 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 63589252548672385367993745408, coefficient := (-63589252548672385367993745408) }, { argument := 2167565554505859551336134082560, coefficient := (-2167565554505859551336134082560) }, { argument := 41509676942287907342711259136, coefficient := (-41509676942287907342711259136) }, { argument := 53850391708914041958111903744, coefficient := (-53850391708914041958111903744) }, { argument := 721370872267327687063874043904, coefficient := (-721370872267327687063874043904) }, { argument := 1304750115780563141610086334464, coefficient := (-1304750115780563141610086334464) }, { argument := 2167565578117691965684360151040, coefficient := (-2167565578117691965684360151040) }, { argument := 721370872267327687063874043904, coefficient := (-721370872267327687063874043904) }, { argument := 42631560102890283216838590464, coefficient := (-42631560102890283216838590464) }, { argument := 42631560102890283216838590464, coefficient := (-42631560102890283216838590464) }, { argument := 41509676942287907342711259136, coefficient := (-41509676942287907342711259136) }, { argument := 41509676942287907342711259136, coefficient := (-41509676942287907342711259136) }, { argument := 1304750115780563141610086334464, coefficient := (-1304750115780563141610086334464) }, { argument := 41509676942287907342711259136, coefficient := (-41509676942287907342711259136) }, { argument := 63589228936839971019767676928, coefficient := (-63589228936839971019767676928) }, { argument := 53850391708914041958111903744, coefficient := (-53850391708914041958111903744) }, { argument := 81979492154016848509627531264, coefficient := (-81979492154016848509627531264) }, { argument := 8237319873054156599619064168448, coefficient := (-8237319873054156599619064168448) }, { argument := 1035860486142417671678249140224, coefficient := (-1035860486142417671678249140224) }, { argument := 79323778961170846490484577140736, coefficient := (-79323778961170846490484577140736) }, { argument := 645738169842451906961898209280, coefficient := (-645738169842451906961898209280) }, { argument := 33635852638210398643738902528, coefficient := (-33635852638210398643738902528) }, { argument := 1029138857784079887765124153344, coefficient := (-1029138857784079887765124153344) }, { argument := 1076185637818024128643980066816, coefficient := (-1076185637818024128643980066816) }, { argument := 645738169842451906961898209280, coefficient := (-645738169842451906961898209280) }, { argument := 16485901669806165672114366971904, coefficient := (-16485901669806165672114366971904) }, { argument := 1056011515794170283878567116800, coefficient := (-1056011515794170283878567116800) }, { argument := 8237325350997348061867090640896, coefficient := (-8237325350997348061867090640896) }, { argument := 1029138857784079887765124153344, coefficient := (-1029138857784079887765124153344) }, { argument := 33635852638210398643738902528, coefficient := (-33635852638210398643738902528) }, { argument := 1056011515794170283878567116800, coefficient := (-1056011515794170283878567116800) }, { argument := 33635852638210398643738902528, coefficient := (-33635852638210398643738902528) }, { argument := 1029138857784079887765124153344, coefficient := (-1029138857784079887765124153344) }, { argument := 1076190256292444375156999061504, coefficient := (-1076190256292444375156999061504) }, { argument := 81979492154016848509627531264, coefficient := (-81979492154016848509627531264) }, { argument := 3040127795664512560871419936768, coefficient := (-3040127795664512560871419936768) }, { argument := 78743668429968428275052052480, coefficient := (-78743668429968428275052052480) }, { argument := 117304916514067787568133196218368, coefficient := (-117304916514067787568133196218368) }, { argument := 888678543709643690532730306560, coefficient := (-888678543709643690532730306560) }, { argument := 78743668429968428275052052480, coefficient := (-78743668429968428275052052480) }, { argument := 117304927451569540346455368138752, coefficient := (-117304927451569540346455368138752) }, { argument := 78743668429968428275052052480, coefficient := (-78743668429968428275052052480) }, { argument := 78743668429968428275052052480, coefficient := (-78743668429968428275052052480) }, { argument := 3264487511196691126488586518528, coefficient := (-3264487511196691126488586518528) }, { argument := 80993487527967526225767825408, coefficient := (-80993487527967526225767825408) }, { argument := 888678543709643690532730306560, coefficient := (-888678543709643690532730306560) }, { argument := 3264487511196691126488586518528, coefficient := (-3264487511196691126488586518528) }, { argument := 3040150183575962789047133274112, coefficient := (-3040150183575962789047133274112) }, { argument := 78743668429968428275052052480, coefficient := (-78743668429968428275052052480) }, { argument := 80993487527967526225767825408, coefficient := (-80993487527967526225767825408) }, { argument := 78743668429968428275052052480, coefficient := (-78743668429968428275052052480) }, { argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 454763892300346834078924800, coefficient := (-454763892300346834078924800) }, { argument := 798363277593942219827445760, coefficient := (-798363277593942219827445760) }, { argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 505293213667052037865472000, coefficient := (-505293213667052037865472000) }, { argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 798363277593942219827445760, coefficient := (-798363277593942219827445760) }, { argument := 793310345457271699448791040, coefficient := (-793310345457271699448791040) }, { argument := 505293213667052037865472000, coefficient := (-505293213667052037865472000) }, { argument := 12243254567152670877480386560, coefficient := (-12243254567152670877480386560) }, { argument := 783204481183930658691481600, coefficient := (-783204481183930658691481600) }, { argument := 454763892300346834078924800, coefficient := (-454763892300346834078924800) }, { argument := 798363277593942219827445760, coefficient := (-798363277593942219827445760) }] }

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
def constantNumerator : ℤ := (-52399410900945069429292296696758272)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1605, 82925, 1605, 42265, 42265, 1605,
    3256648797, 63513418791, 127026790989, 407083041, 2704023060309041, 105053187,
    2725931, 307630345953061, 169217409, 2704214835640111, 169217409, 176346767,
    105053187, 5242175, 84503861, 1648052783, 3296104357, 10563033,
    68718902525, 247179848825, 34359462725, 72450166330733, 1605, 72450168744595,
    1605, 145624836386581, 7316211975533907, 449232768757, 17613423309008613, 17502763995,
    29174444653, 892635455649, 29170063213, 17502763995, 14299236917739, 915943765445,
    1829054210232065, 892635455649, 29174444653, 915943765445, 29174444653, 892635455649,
    29170188397, 145624836386581, 4915162311334719, 245670353565, 1517904409607857857, 2772565418805,
    245670353565, 379476135853938325, 245670353565, 245670353565, 10184790943509, 63172376631,
    2772565418805, 10184790943509, 39321583643215091, 245670353565
  ]
def negativeCoefficients : Array ℕ := #[
    30317592820023122271928320, 783204481183930658691481600, 30317592820023122271928320, 798363277593942219827445760, 798363277593942219827445760, 30317592820023122271928320,
    3754660431013318162353487872, 146451972710489015585479852032, 146451918992417351438658699264, 3754678337037206211293872128, 3044459311702256320019991363584, 3875778509433102619203600384,
    201138206078364606984617984, 11083551291216498334099778306048, 6243020473278470686022565888, 3044675231529642746395978891264, 6243020473278470686022565888, 6506047358150178249002450944,
    3875778509433102619203600384, 193402121229196737485209600, 194852637138415713016348672, 7600301976991445918607736832, 7600299189227247779251748864, 194853566393148426135011328,
    79227500494054255791335014400, 284978963215811976587588403200, 79227526924779748903301939200, 81571635522504898565365563392, 30317592820023122271928320, 81571638240271899496315617280,
    30317592820023122271928320, 81979494860811954848396214272, 8237322381694515990785024851968, 1035860239348040395536585457664, 79323806651169998128881806082048, 645738015996606332224237731840,
    33635844625405941626152419328, 1029138612592263503026977767424, 1076185381408281504081212604416, 645738015996606332224237731840, 16485897741929420842093472907264, 1056011264192110333526351544320,
    8237327859641564786113894154240, 1029138612592263503026977767424, 33635844625405941626152419328, 1056011264192110333526351544320, 33635844625405941626152419328, 1029138612592263503026977767424,
    1076189999882701750594231599104, 81979494860811954848396214272, 11067961576896273168125040525312, 283238633669455872913771069440, 427252108343373835824768265224192, 3196550294269573422883987783680,
    283238633669455872913771069440, 427252146006948089345086377164800, 283238633669455872913771069440, 283238633669455872913771069440, 11742264498696584902796623478784, 291331166060011754997021671424,
    3196550294269573422883987783680, 11742264498696584902796623478784, 11068041840200079647615479709696, 283238633669455872913771069440
  ]
def negativeScales : Array ℕ := #[
    10, 16, 10, 15, 15, 10,
    31, 35, 36, 28, 51, 26,
    21, 48, 27, 51, 27, 27,
    26, 22, 26, 30, 31, 23,
    35, 37, 34, 46, 10, 46,
    10, 47, 52, 38, 53, 34,
    34, 39, 34, 34, 43, 39,
    50, 39, 34, 39, 34, 39,
    34, 47, 52, 37, 60, 41,
    37, 58, 37, 37, 43, 35,
    41, 43, 55, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    10648357582030099, 16339519486562748, 10648357582030099, 15367175829465614, 15367175829465614, 10648357582030099,
    31600740999225987, 35886342381619663, 36886341852444035, 28600747879440788, 51264028878499924, 26646544688852848,
    21378317613779227, 48128191152257928, 27334302758915913, 51264131194013605, 27334302758915913, 27393839885893281,
    26646544688852848, 22321734085412857, 26332513924166100, 30618115303162825, 31618114773987230, 23332520804380900,
    35999987968649564, 37846770178658948, 34999988449940585, 46042054235453847, 10648357582030099, 46042054283520909,
    10648357582030099, 47049249757284235, 52700018298855111, 38708672211122783, 53967524867854968, 34026863715903037,
    34763986143105864, 39699280155679704, 34763769461809058, 34026863715903037, 43701003392895451, 39736468070411548,
    50700019258269355, 39699280155679704, 34763986143105864, 39736468070411548, 34763986143105864, 39699280155679704,
    34763775653154902, 47049249757284235, 52126160482173597, 37837932815144707, 60396786647522353, 41334358639890917,
    37837932815144707, 58396786774700308, 37837932815144707, 37837932815144707, 43211481600893196, 35878574801228164,
    41334358639890917, 43211481600893196, 55126170944357596, 37837932815144707
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
noncomputable def negativeCeiling : ℝ := 363496997531 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 783204481183930658691481600, coefficient := (-783204481183930658691481600) }, { argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 798363277593942219827445760, coefficient := (-798363277593942219827445760) }, { argument := 798363277593942219827445760, coefficient := (-798363277593942219827445760) }, { argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 3754660431013318162353487872, coefficient := (-3754660431013318162353487872) }, { argument := 146451972710489015585479852032, coefficient := (-146451972710489015585479852032) }, { argument := 146451918992417351438658699264, coefficient := (-146451918992417351438658699264) }, { argument := 3754678337037206211293872128, coefficient := (-3754678337037206211293872128) }, { argument := 3044459311702256320019991363584, coefficient := (-3044459311702256320019991363584) }, { argument := 3875778509433102619203600384, coefficient := (-3875778509433102619203600384) }, { argument := 201138206078364606984617984, coefficient := (-201138206078364606984617984) }, { argument := 11083551291216498334099778306048, coefficient := (-11083551291216498334099778306048) }, { argument := 6243020473278470686022565888, coefficient := (-6243020473278470686022565888) }, { argument := 3044675231529642746395978891264, coefficient := (-3044675231529642746395978891264) }, { argument := 6243020473278470686022565888, coefficient := (-6243020473278470686022565888) }, { argument := 6506047358150178249002450944, coefficient := (-6506047358150178249002450944) }, { argument := 3875778509433102619203600384, coefficient := (-3875778509433102619203600384) }, { argument := 193402121229196737485209600, coefficient := (-193402121229196737485209600) }, { argument := 194852637138415713016348672, coefficient := (-194852637138415713016348672) }, { argument := 7600301976991445918607736832, coefficient := (-7600301976991445918607736832) }, { argument := 7600299189227247779251748864, coefficient := (-7600299189227247779251748864) }, { argument := 194853566393148426135011328, coefficient := (-194853566393148426135011328) }, { argument := 79227500494054255791335014400, coefficient := (-79227500494054255791335014400) }, { argument := 284978963215811976587588403200, coefficient := (-284978963215811976587588403200) }, { argument := 79227526924779748903301939200, coefficient := (-79227526924779748903301939200) }, { argument := 81571635522504898565365563392, coefficient := (-81571635522504898565365563392) }, { argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 81571638240271899496315617280, coefficient := (-81571638240271899496315617280) }, { argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 81979494860811954848396214272, coefficient := (-81979494860811954848396214272) }, { argument := 8237322381694515990785024851968, coefficient := (-8237322381694515990785024851968) }, { argument := 1035860239348040395536585457664, coefficient := (-1035860239348040395536585457664) }, { argument := 79323806651169998128881806082048, coefficient := (-79323806651169998128881806082048) }, { argument := 645738015996606332224237731840, coefficient := (-645738015996606332224237731840) }, { argument := 33635844625405941626152419328, coefficient := (-33635844625405941626152419328) }, { argument := 1029138612592263503026977767424, coefficient := (-1029138612592263503026977767424) }, { argument := 1076185381408281504081212604416, coefficient := (-1076185381408281504081212604416) }, { argument := 645738015996606332224237731840, coefficient := (-645738015996606332224237731840) }, { argument := 16485897741929420842093472907264, coefficient := (-16485897741929420842093472907264) }, { argument := 1056011264192110333526351544320, coefficient := (-1056011264192110333526351544320) }, { argument := 8237327859641564786113894154240, coefficient := (-8237327859641564786113894154240) }, { argument := 1029138612592263503026977767424, coefficient := (-1029138612592263503026977767424) }, { argument := 33635844625405941626152419328, coefficient := (-33635844625405941626152419328) }, { argument := 1056011264192110333526351544320, coefficient := (-1056011264192110333526351544320) }, { argument := 33635844625405941626152419328, coefficient := (-33635844625405941626152419328) }, { argument := 1029138612592263503026977767424, coefficient := (-1029138612592263503026977767424) }, { argument := 1076189999882701750594231599104, coefficient := (-1076189999882701750594231599104) }, { argument := 81979494860811954848396214272, coefficient := (-81979494860811954848396214272) }, { argument := 11067961576896273168125040525312, coefficient := (-11067961576896273168125040525312) }, { argument := 283238633669455872913771069440, coefficient := (-283238633669455872913771069440) }, { argument := 427252108343373835824768265224192, coefficient := (-427252108343373835824768265224192) }, { argument := 3196550294269573422883987783680, coefficient := (-3196550294269573422883987783680) }, { argument := 283238633669455872913771069440, coefficient := (-283238633669455872913771069440) }, { argument := 427252146006948089345086377164800, coefficient := (-427252146006948089345086377164800) }, { argument := 283238633669455872913771069440, coefficient := (-283238633669455872913771069440) }, { argument := 283238633669455872913771069440, coefficient := (-283238633669455872913771069440) }, { argument := 11742264498696584902796623478784, coefficient := (-11742264498696584902796623478784) }, { argument := 291331166060011754997021671424, coefficient := (-291331166060011754997021671424) }, { argument := 3196550294269573422883987783680, coefficient := (-3196550294269573422883987783680) }, { argument := 11742264498696584902796623478784, coefficient := (-11742264498696584902796623478784) }, { argument := 11068041840200079647615479709696, coefficient := (-11068041840200079647615479709696) }, { argument := 283238633669455872913771069440, coefficient := (-283238633669455872913771069440) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10
