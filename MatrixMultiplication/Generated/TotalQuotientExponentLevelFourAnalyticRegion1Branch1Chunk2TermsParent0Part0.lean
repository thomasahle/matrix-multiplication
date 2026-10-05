import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 2, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-42934316507041824082189554286592)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    743307, 295546641, 1179116049, 585975757, 1179116049, 35,
    35, 35, 35, 13206433, 2765735, 499186795,
    18253851, 902503, 9112369, 18544981, 3314413, 2765735,
    902503, 5415379, 2636944765, 10517089405, 5222740105, 10517089405,
    395, 395, 395, 395, 1461519089, 113312675,
    34029168119, 747863655, 36975715, 373335445, 759791305, 182875555,
    113312675, 36975715, 35, 35, 35, 35,
    246308139, 11132679789, 30952845, 195812199, 20077319865, 4671213,
    378747, 81178107, 146827587, 20077319865, 81178107, 2398731,
    2398731, 4671213, 4671213, 146827587, 4671213, 195812199,
    378747, 1486615, 5273888245, 21034173685
  ]
def negativeCoefficients : Array ℕ := #[
    14040672253129549499426930688, 1362968312092878597431230464, 1359428249319160704688717824, 1351168102847152288289521664, 1359428249319160704688717824, 169249614746048084458864640,
    169249614746048084458864640, 169249614746048084458864640, 169249614746048084458864640, 30451961209699031859593216, 204075222882804346954711040, 1151046381542539354009763840,
    168362058878313586237636608, 8324120933377545731047424, 168093538848204633149538304, 171047259179403117118619648, 30570064182787948050120704, 204075222882804346954711040,
    8324120933377545731047424, 51146808563272272855399661568, 48643045216463176264308490240, 48501514163589316086983557120, 48171275040216975673225379840, 48501514163589316086983557120,
    1910102794991114096035758080, 1910102794991114096035758080, 1910102794991114096035758080, 1910102794991114096035758080, 1685016787101508295525924864, 33443998656518823466552524800,
    39232959708276828744810758144, 27591298891628029359905832960, 1364163103094846746662010880, 27547293630237873013239316480, 28031351505529592826570997760, 1686729280211297580288573440,
    33443998656518823466552524800, 1364163103094846746662010880, 169249614746048084458864640, 169249614746048084458864640, 169249614746048084458864640, 169249614746048084458864640,
    567947900425584810632675328, 25670211865280231441461936128, 570979210068200326189547520, 225756095091455336827060224, 23147573827228737806259978240, 86168670724785015732830208,
    111786383642964344734482432, 1497471764217209868005670912, 2708490920349323602629230592, 23147573827228737806259978240, 1497471764217209868005670912, 88497553717346772914798592,
    88497553717346772914798592, 86168670724785015732830208, 86168670724785015732830208, 2708490920349323602629230592, 86168670724785015732830208, 225756095091455336827060224,
    111786383642964344734482432, 14040681697862515238717358080, 48643033364430108905921576960, 48501502346143893866802053120
  ]
def negativeScales : Array ℕ := #[
    19, 28, 30, 29, 30, 5,
    5, 5, 5, 23, 21, 28,
    24, 19, 23, 24, 21, 21,
    19, 22, 31, 33, 32, 33,
    8, 8, 8, 8, 30, 26,
    34, 29, 25, 28, 29, 27,
    26, 25, 5, 5, 5, 5,
    27, 33, 24, 27, 34, 22,
    18, 26, 27, 34, 26, 21,
    21, 22, 22, 27, 22, 27,
    18, 20, 32, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19503598668916132, 28138810583002944, 30135058569825227, 29126265737774810, 30135058569825227, 5129283016944967,
    5129283016944967, 5129283016944967, 5129283016944967, 23654737517791008, 21399231500034915, 28895004534150419,
    24121697524506000, 19783572202551266, 23119394738636579, 24144525453960261, 21660321953422281, 21399231500034915,
    19783572202551266, 22368630878955852, 31296220205964175, 33292016444191326, 32282159767813865, 33292016444191326,
    8625708843075807, 8625708843075807, 8625708843075807, 8625708843075807, 30444821526391153, 26755734007421834,
    34986052851239296, 29478200031638281, 25140074709222989, 28475897245768850, 29501027961092694, 27446287001833352,
    26755734007421834, 25140074709222989, 5129283016944967, 5129283016944967, 5129283016944967, 5129283016944967,
    27875889062918773, 33374081859877819, 24883568686870500, 27544895406005764, 34224847644679210, 22155365800597485,
    18530874935690428, 26274587362296483, 27129547816441754, 34224847644679210, 26274587362296483, 21193839948412121,
    21193839948412121, 22155365800597485, 22155365800597485, 27129547816441754, 22155365800597485, 27544895406005764,
    18530874935690428, 20503599639372859, 32296219854446885, 34292016092677104
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
noncomputable def negativeCeiling : ℝ := 12044951 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 14040672253129549499426930688, coefficient := (-14040672253129549499426930688) }, { argument := 1362968312092878597431230464, coefficient := (-1362968312092878597431230464) }, { argument := 1359428249319160704688717824, coefficient := (-1359428249319160704688717824) }, { argument := 1351168102847152288289521664, coefficient := (-1351168102847152288289521664) }, { argument := 1359428249319160704688717824, coefficient := (-1359428249319160704688717824) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 30451961209699031859593216, coefficient := (-30451961209699031859593216) }, { argument := 204075222882804346954711040, coefficient := (-204075222882804346954711040) }, { argument := 1151046381542539354009763840, coefficient := (-1151046381542539354009763840) }, { argument := 168362058878313586237636608, coefficient := (-168362058878313586237636608) }, { argument := 8324120933377545731047424, coefficient := (-8324120933377545731047424) }, { argument := 168093538848204633149538304, coefficient := (-168093538848204633149538304) }, { argument := 171047259179403117118619648, coefficient := (-171047259179403117118619648) }, { argument := 30570064182787948050120704, coefficient := (-30570064182787948050120704) }, { argument := 204075222882804346954711040, coefficient := (-204075222882804346954711040) }, { argument := 8324120933377545731047424, coefficient := (-8324120933377545731047424) }, { argument := 51146808563272272855399661568, coefficient := (-51146808563272272855399661568) }, { argument := 48643045216463176264308490240, coefficient := (-48643045216463176264308490240) }, { argument := 48501514163589316086983557120, coefficient := (-48501514163589316086983557120) }, { argument := 48171275040216975673225379840, coefficient := (-48171275040216975673225379840) }, { argument := 48501514163589316086983557120, coefficient := (-48501514163589316086983557120) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 1685016787101508295525924864, coefficient := (-1685016787101508295525924864) }, { argument := 33443998656518823466552524800, coefficient := (-33443998656518823466552524800) }, { argument := 39232959708276828744810758144, coefficient := (-39232959708276828744810758144) }, { argument := 27591298891628029359905832960, coefficient := (-27591298891628029359905832960) }, { argument := 1364163103094846746662010880, coefficient := (-1364163103094846746662010880) }, { argument := 27547293630237873013239316480, coefficient := (-27547293630237873013239316480) }, { argument := 28031351505529592826570997760, coefficient := (-28031351505529592826570997760) }, { argument := 1686729280211297580288573440, coefficient := (-1686729280211297580288573440) }, { argument := 33443998656518823466552524800, coefficient := (-33443998656518823466552524800) }, { argument := 1364163103094846746662010880, coefficient := (-1364163103094846746662010880) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 567947900425584810632675328, coefficient := (-567947900425584810632675328) }, { argument := 25670211865280231441461936128, coefficient := (-25670211865280231441461936128) }, { argument := 570979210068200326189547520, coefficient := (-570979210068200326189547520) }, { argument := 225756095091455336827060224, coefficient := (-225756095091455336827060224) }, { argument := 23147573827228737806259978240, coefficient := (-23147573827228737806259978240) }, { argument := 86168670724785015732830208, coefficient := (-86168670724785015732830208) }, { argument := 111786383642964344734482432, coefficient := (-111786383642964344734482432) }, { argument := 1497471764217209868005670912, coefficient := (-1497471764217209868005670912) }, { argument := 2708490920349323602629230592, coefficient := (-2708490920349323602629230592) }, { argument := 23147573827228737806259978240, coefficient := (-23147573827228737806259978240) }, { argument := 1497471764217209868005670912, coefficient := (-1497471764217209868005670912) }, { argument := 88497553717346772914798592, coefficient := (-88497553717346772914798592) }, { argument := 88497553717346772914798592, coefficient := (-88497553717346772914798592) }, { argument := 86168670724785015732830208, coefficient := (-86168670724785015732830208) }, { argument := 86168670724785015732830208, coefficient := (-86168670724785015732830208) }, { argument := 2708490920349323602629230592, coefficient := (-2708490920349323602629230592) }, { argument := 86168670724785015732830208, coefficient := (-86168670724785015732830208) }, { argument := 225756095091455336827060224, coefficient := (-225756095091455336827060224) }, { argument := 111786383642964344734482432, coefficient := (-111786383642964344734482432) }, { argument := 14040681697862515238717358080, coefficient := (-14040681697862515238717358080) }, { argument := 48643033364430108905921576960, coefficient := (-48643033364430108905921576960) }, { argument := 48501502346143893866802053120, coefficient := (-48501502346143893866802053120) }] }

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


end Parent0

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-254438609751552800599747550248960)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    10445477665, 21034173685, 12197731715, 2333195725, 221566016645, 15399091785,
    761358605, 7687265915, 15644691335, 1524727135, 2333195725, 761358605,
    35, 35, 35, 35, 9596421, 433740771,
    1205955, 18904878555, 28920709125, 926464275, 75118725, 16100446725,
    29121025725, 28920709125, 16100446725, 475751925, 475751925, 926464275,
    926464275, 29121025725, 926464275, 18904878555, 75118725, 15994035,
    722901285, 2009925, 79410621, 15749892675, 15749892675, 79410621,
    13206433, 1461519089, 246308139, 12197731715, 9596421, 15994035,
    489417471, 15994035, 9596421, 7840275957, 502212699, 1461519089,
    489417471, 15994035, 502212699, 15994035, 489417471, 15994035,
    13206433, 35, 35, 35
  ]
def negativeCoefficients : Array ℕ := #[
    48171263303476058775523164160, 48501502346143893866802053120, 14063027201648455965307043840, 344318915303585685776944332800, 255448225280099101265383915520, 284063105125458190765979074560,
    14044587334751521393533255680, 283610053921111367495219937280, 288593617168926423473570447360, 14063125620792696728799150080, 344318915303585685776944332800, 14044587334751521393533255680,
    169249614746048084458864640, 169249614746048084458864640, 169249614746048084458864640, 169249614746048084458864640, 354045444421143778056732672, 16002209993940923495976271872,
    355935091990566437105172480, 21795841028040315102748999680, 33343307478691968876281856000, 17090249374359866298492518400, 22171134323493880603449753600, 297000820208470108917045657600,
    537188108712987148787751321600, 33343307478691968876281856000, 297000820208470108917045657600, 17552148006099322144397721600, 17552148006099322144397721600, 17090249374359866298492518400,
    17090249374359866298492518400, 537188108712987148787751321600, 17090249374359866298492518400, 21795841028040315102748999680, 22171134323493880603449753600, 18439866896934571773788160,
    833448437184423098748764160, 18538286041175335265894400, 91554212645084079216132096, 18158389960257357942148300800, 18158389960257357942148300800, 91554212645084079216132096,
    30451961209699031859593216, 1685016787101508295525924864, 567947900425584810632675328, 14063027201648455965307043840, 354045444421143778056732672, 18439866896934571773788160,
    564259927046197896277917696, 590075740701906296761221120, 354045444421143778056732672, 9039222752877327083510956032, 579011820563745553696948224, 1685016787101508295525924864,
    564259927046197896277917696, 18439866896934571773788160, 579011820563745553696948224, 18439866896934571773788160, 564259927046197896277917696, 590075740701906296761221120,
    30451961209699031859593216, 169249614746048084458864640, 169249614746048084458864640, 169249614746048084458864640
  ]
def negativeScales : Array ℕ := #[
    33, 34, 33, 31, 37, 33,
    29, 32, 33, 30, 31, 29,
    5, 5, 5, 5, 23, 28,
    20, 34, 34, 29, 26, 33,
    34, 34, 33, 28, 28, 29,
    29, 34, 29, 34, 26, 23,
    29, 20, 26, 33, 33, 26,
    23, 30, 27, 33, 23, 23,
    28, 23, 23, 32, 28, 30,
    28, 23, 28, 23, 28, 23,
    23, 5, 5, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33282159416306874, 34292016092677104, 33505893838647929, 31119660189873691, 37688945664475355, 33842126215834057,
    29504000891929928, 32839823429899859, 33864954146097142, 30505903935216217, 31119660189873691, 29504000891929928,
    5129283016944967, 5129283016944967, 5129283016944967, 5129283016944967, 23194065020128625, 28692257819964341,
    20201744643653310, 34138039530351006, 34751383876172385, 29787160105762238, 26162669240358342, 33906381671859979,
    34761342121397971, 34751383876172385, 33906381671859979, 28825634254160643, 28825634254160643, 29787160105762238,
    29787160105762238, 34761342121397971, 29787160105762238, 34138039530351006, 26162669240358342, 23931030621834616,
    29429223414070299, 20938710246423341, 26242828641847825, 33874622949267724, 33874622949267724, 26242828641847825,
    23654737517791008, 30444821526391153, 27875889062918773, 33505893838647929, 23194065020128625, 23931030621834616,
    28866490364465229, 23931030621834616, 23194065020128625, 32868257290718741, 28903723272967495, 30444821526391153,
    28866490364465229, 23931030621834616, 28903723272967495, 23931030621834616, 28866490364465229, 23931030621834616,
    23654737517791008, 5129283016944967, 5129283016944967, 5129283016944967
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
noncomputable def negativeCeiling : ℝ := 320214619 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 48171263303476058775523164160, coefficient := (-48171263303476058775523164160) }, { argument := 48501502346143893866802053120, coefficient := (-48501502346143893866802053120) }, { argument := 14063027201648455965307043840, coefficient := (-14063027201648455965307043840) }, { argument := 344318915303585685776944332800, coefficient := (-344318915303585685776944332800) }, { argument := 255448225280099101265383915520, coefficient := (-255448225280099101265383915520) }, { argument := 284063105125458190765979074560, coefficient := (-284063105125458190765979074560) }, { argument := 14044587334751521393533255680, coefficient := (-14044587334751521393533255680) }, { argument := 283610053921111367495219937280, coefficient := (-283610053921111367495219937280) }, { argument := 288593617168926423473570447360, coefficient := (-288593617168926423473570447360) }, { argument := 14063125620792696728799150080, coefficient := (-14063125620792696728799150080) }, { argument := 344318915303585685776944332800, coefficient := (-344318915303585685776944332800) }, { argument := 14044587334751521393533255680, coefficient := (-14044587334751521393533255680) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 354045444421143778056732672, coefficient := (-354045444421143778056732672) }, { argument := 16002209993940923495976271872, coefficient := (-16002209993940923495976271872) }, { argument := 355935091990566437105172480, coefficient := (-355935091990566437105172480) }, { argument := 21795841028040315102748999680, coefficient := (-21795841028040315102748999680) }, { argument := 33343307478691968876281856000, coefficient := (-33343307478691968876281856000) }, { argument := 17090249374359866298492518400, coefficient := (-17090249374359866298492518400) }, { argument := 22171134323493880603449753600, coefficient := (-22171134323493880603449753600) }, { argument := 297000820208470108917045657600, coefficient := (-297000820208470108917045657600) }, { argument := 537188108712987148787751321600, coefficient := (-537188108712987148787751321600) }, { argument := 33343307478691968876281856000, coefficient := (-33343307478691968876281856000) }, { argument := 297000820208470108917045657600, coefficient := (-297000820208470108917045657600) }, { argument := 17552148006099322144397721600, coefficient := (-17552148006099322144397721600) }, { argument := 17552148006099322144397721600, coefficient := (-17552148006099322144397721600) }, { argument := 17090249374359866298492518400, coefficient := (-17090249374359866298492518400) }, { argument := 17090249374359866298492518400, coefficient := (-17090249374359866298492518400) }, { argument := 537188108712987148787751321600, coefficient := (-537188108712987148787751321600) }, { argument := 17090249374359866298492518400, coefficient := (-17090249374359866298492518400) }, { argument := 21795841028040315102748999680, coefficient := (-21795841028040315102748999680) }, { argument := 22171134323493880603449753600, coefficient := (-22171134323493880603449753600) }, { argument := 18439866896934571773788160, coefficient := (-18439866896934571773788160) }, { argument := 833448437184423098748764160, coefficient := (-833448437184423098748764160) }, { argument := 18538286041175335265894400, coefficient := (-18538286041175335265894400) }, { argument := 91554212645084079216132096, coefficient := (-91554212645084079216132096) }, { argument := 18158389960257357942148300800, coefficient := (-18158389960257357942148300800) }, { argument := 18158389960257357942148300800, coefficient := (-18158389960257357942148300800) }, { argument := 91554212645084079216132096, coefficient := (-91554212645084079216132096) }, { argument := 30451961209699031859593216, coefficient := (-30451961209699031859593216) }, { argument := 1685016787101508295525924864, coefficient := (-1685016787101508295525924864) }, { argument := 567947900425584810632675328, coefficient := (-567947900425584810632675328) }, { argument := 14063027201648455965307043840, coefficient := (-14063027201648455965307043840) }, { argument := 354045444421143778056732672, coefficient := (-354045444421143778056732672) }, { argument := 18439866896934571773788160, coefficient := (-18439866896934571773788160) }, { argument := 564259927046197896277917696, coefficient := (-564259927046197896277917696) }, { argument := 590075740701906296761221120, coefficient := (-590075740701906296761221120) }, { argument := 354045444421143778056732672, coefficient := (-354045444421143778056732672) }, { argument := 9039222752877327083510956032, coefficient := (-9039222752877327083510956032) }, { argument := 579011820563745553696948224, coefficient := (-579011820563745553696948224) }, { argument := 1685016787101508295525924864, coefficient := (-1685016787101508295525924864) }, { argument := 564259927046197896277917696, coefficient := (-564259927046197896277917696) }, { argument := 18439866896934571773788160, coefficient := (-18439866896934571773788160) }, { argument := 579011820563745553696948224, coefficient := (-579011820563745553696948224) }, { argument := 18439866896934571773788160, coefficient := (-18439866896934571773788160) }, { argument := 564259927046197896277917696, coefficient := (-564259927046197896277917696) }, { argument := 590075740701906296761221120, coefficient := (-590075740701906296761221120) }, { argument := 30451961209699031859593216, coefficient := (-30451961209699031859593216) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2
