import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 13, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4974556636775446713364183708073984)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5344098385, 3506898554715, 22325, 16625, 17575, 1425,
    305425, 552425, 16625, 305425, 9025, 9025,
    17575, 17575, 552425, 17575, 22325, 1425,
    131095839, 5371020795, 110593477365, 5371020795, 131095839, 10086655563105,
    5781, 776154651927249, 60489, 2679, 97019348305731, 2679,
    5217, 98559, 5217, 60489, 98559, 20173491599445,
    5217, 5217, 5781, 5477791684209, 20711040919, 200602854973655,
    139572070523, 6831613127, 69775646929, 139580239221, 687211742999, 20711040919,
    6831613127, 781751213759783, 57773281306731225, 5637491055, 14538852005, 12165166845,
    340335892215, 28881784943918865, 12165166845, 10978676265, 5637593455, 5637491055,
    10978471465, 340335892215, 10978471465, 390873285918959
  ]
def negativeCoefficients : Array ℕ := #[
    197162430425639071500279480320, 31587334048481209956465377280, 210853663460129658791526400, 157018685555415703355392000, 165991181872868029261414400, 215339911618855821744537600,
    2884657566060922778786201600, 5217506608598527514352025600, 157018685555415703355392000, 2884657566060922778786201600, 170477430031594192214425600, 170477430031594192214425600,
    165991181872868029261414400, 165991181872868029261414400, 5217506608598527514352025600, 165991181872868029261414400, 210853663460129658791526400, 215339911618855821744537600,
    1209145695580615755706662912, 198155692039874029039323709440, 2040089573173745188228395171840, 198155692039874029039323709440, 1209145695580615755706662912, 11356564558853554625335787520,
    218400005099755351843012608, 436936225150179452682070130688, 2285209809458415754650058752, 202419516921724472439865344, 436936300877418494032217112576, 202419516921724472439865344,
    197092687529047512638816256, 7446907490962389801866625024, 197092687529047512638816256, 2285209809458415754650058752, 7446907490962389801866625024, 11356666156252791668830371840,
    197092687529047512638816256, 197092687529047512638816256, 218400005099755351843012608, 24669780587816854097875697664, 191025635666459637820059287552, 903434942908810308183004282880,
    160915641548470115522941288448, 7876313685272726775321853952, 160891687684597603106614673408, 160925059416058954464620445696, 24759412397559403706457260032, 191025635666459637820059287552,
    7876313685272726775321853952, 440086809373123960511760695296, 32523466020620698391283970867200, 207986709418823715806521589760, 268194482061773982299932590080, 3590523510459066775660469944320,
    6278089102787703973998955069440, 32517998977806950531711379701760, 3590523510459066775660469944320, 202520831328564464830371594240, 207990487312010011522692546560, 207986709418823715806521589760,
    202517053435378169114200637440, 6278089102787703973998955069440, 202517053435378169114200637440, 440084196203426273392030908416
  ]
def negativeScales : Array ℕ := #[
    32, 41, 14, 14, 14, 10,
    18, 19, 14, 18, 13, 13,
    14, 14, 19, 14, 14, 10,
    26, 32, 36, 32, 26, 43,
    12, 49, 15, 11, 46, 11,
    12, 16, 12, 15, 16, 44,
    12, 12, 12, 42, 34, 47,
    37, 32, 36, 37, 39, 34,
    32, 49, 55, 32, 33, 33,
    38, 54, 33, 33, 32, 32,
    33, 38, 33, 48
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32315299422098570, 41673332836535173, 14446372554895989, 14021066720163277, 14101237068847261, 10476746203939589,
    18220458630546258, 19075419084691529, 14021066720163277, 18220458630546258, 13139711216661896, 13139711216661896,
    14101237068847261, 14101237068847261, 19075419084691529, 14101237068847261, 14446372554895989, 10476746203939589,
    26966046667679686, 32322549161177958, 36686475343937075, 32322549161177958, 26966046667679686, 43197513132226888,
    12497103357017124, 49463337472251394, 15884385193190574, 11387478865842383, 46463337722290866, 11387478865842383,
    12349004718027745, 16588699997778354, 12349004718027745, 15884385193190574, 16588699997778354, 44197526038718781,
    12349004718027745, 12349004718027745, 12497103357017124, 42316731541260988, 34269681012858937, 47511335466911069,
    37022219319483052, 32669579131736786, 36022004544258602, 37022303753246894, 39321963733062849, 34269681012858937,
    32669579131736786, 49473702882527270, 55681251954942392, 32392406093233686, 33759194306983470, 33502037055817206,
    38308168351367233, 54681009424255751, 33502037055817206, 33353985063230627, 32392432298265153, 32392406093233686,
    33353958150450514, 38308168351367233, 33353958150450514, 48473694315994312
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
noncomputable def negativeCeiling : ℝ := 27796754579 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 197162430425639071500279480320, coefficient := (-197162430425639071500279480320) }, { argument := 31587334048481209956465377280, coefficient := (-31587334048481209956465377280) }, { argument := 210853663460129658791526400, coefficient := (-210853663460129658791526400) }, { argument := 157018685555415703355392000, coefficient := (-157018685555415703355392000) }, { argument := 165991181872868029261414400, coefficient := (-165991181872868029261414400) }, { argument := 215339911618855821744537600, coefficient := (-215339911618855821744537600) }, { argument := 2884657566060922778786201600, coefficient := (-2884657566060922778786201600) }, { argument := 5217506608598527514352025600, coefficient := (-5217506608598527514352025600) }, { argument := 157018685555415703355392000, coefficient := (-157018685555415703355392000) }, { argument := 2884657566060922778786201600, coefficient := (-2884657566060922778786201600) }, { argument := 170477430031594192214425600, coefficient := (-170477430031594192214425600) }, { argument := 170477430031594192214425600, coefficient := (-170477430031594192214425600) }, { argument := 165991181872868029261414400, coefficient := (-165991181872868029261414400) }, { argument := 165991181872868029261414400, coefficient := (-165991181872868029261414400) }, { argument := 5217506608598527514352025600, coefficient := (-5217506608598527514352025600) }, { argument := 165991181872868029261414400, coefficient := (-165991181872868029261414400) }, { argument := 210853663460129658791526400, coefficient := (-210853663460129658791526400) }, { argument := 215339911618855821744537600, coefficient := (-215339911618855821744537600) }, { argument := 1209145695580615755706662912, coefficient := (-1209145695580615755706662912) }, { argument := 198155692039874029039323709440, coefficient := (-198155692039874029039323709440) }, { argument := 2040089573173745188228395171840, coefficient := (-2040089573173745188228395171840) }, { argument := 198155692039874029039323709440, coefficient := (-198155692039874029039323709440) }, { argument := 1209145695580615755706662912, coefficient := (-1209145695580615755706662912) }, { argument := 11356564558853554625335787520, coefficient := (-11356564558853554625335787520) }, { argument := 218400005099755351843012608, coefficient := (-218400005099755351843012608) }, { argument := 436936225150179452682070130688, coefficient := (-436936225150179452682070130688) }, { argument := 2285209809458415754650058752, coefficient := (-2285209809458415754650058752) }, { argument := 202419516921724472439865344, coefficient := (-202419516921724472439865344) }, { argument := 436936300877418494032217112576, coefficient := (-436936300877418494032217112576) }, { argument := 202419516921724472439865344, coefficient := (-202419516921724472439865344) }, { argument := 197092687529047512638816256, coefficient := (-197092687529047512638816256) }, { argument := 7446907490962389801866625024, coefficient := (-7446907490962389801866625024) }, { argument := 197092687529047512638816256, coefficient := (-197092687529047512638816256) }, { argument := 2285209809458415754650058752, coefficient := (-2285209809458415754650058752) }, { argument := 7446907490962389801866625024, coefficient := (-7446907490962389801866625024) }, { argument := 11356666156252791668830371840, coefficient := (-11356666156252791668830371840) }, { argument := 197092687529047512638816256, coefficient := (-197092687529047512638816256) }, { argument := 197092687529047512638816256, coefficient := (-197092687529047512638816256) }, { argument := 218400005099755351843012608, coefficient := (-218400005099755351843012608) }, { argument := 24669780587816854097875697664, coefficient := (-24669780587816854097875697664) }, { argument := 191025635666459637820059287552, coefficient := (-191025635666459637820059287552) }, { argument := 903434942908810308183004282880, coefficient := (-903434942908810308183004282880) }, { argument := 160915641548470115522941288448, coefficient := (-160915641548470115522941288448) }, { argument := 7876313685272726775321853952, coefficient := (-7876313685272726775321853952) }, { argument := 160891687684597603106614673408, coefficient := (-160891687684597603106614673408) }, { argument := 160925059416058954464620445696, coefficient := (-160925059416058954464620445696) }, { argument := 24759412397559403706457260032, coefficient := (-24759412397559403706457260032) }, { argument := 191025635666459637820059287552, coefficient := (-191025635666459637820059287552) }, { argument := 7876313685272726775321853952, coefficient := (-7876313685272726775321853952) }, { argument := 440086809373123960511760695296, coefficient := (-440086809373123960511760695296) }, { argument := 32523466020620698391283970867200, coefficient := (-32523466020620698391283970867200) }, { argument := 207986709418823715806521589760, coefficient := (-207986709418823715806521589760) }, { argument := 268194482061773982299932590080, coefficient := (-268194482061773982299932590080) }, { argument := 3590523510459066775660469944320, coefficient := (-3590523510459066775660469944320) }, { argument := 6278089102787703973998955069440, coefficient := (-6278089102787703973998955069440) }, { argument := 32517998977806950531711379701760, coefficient := (-32517998977806950531711379701760) }, { argument := 3590523510459066775660469944320, coefficient := (-3590523510459066775660469944320) }, { argument := 202520831328564464830371594240, coefficient := (-202520831328564464830371594240) }, { argument := 207990487312010011522692546560, coefficient := (-207990487312010011522692546560) }, { argument := 207986709418823715806521589760, coefficient := (-207986709418823715806521589760) }, { argument := 202517053435378169114200637440, coefficient := (-202517053435378169114200637440) }, { argument := 6278089102787703973998955069440, coefficient := (-6278089102787703973998955069440) }, { argument := 202517053435378169114200637440, coefficient := (-202517053435378169114200637440) }, { argument := 440084196203426273392030908416, coefficient := (-440084196203426273392030908416) }] }

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


end Parent3

namespace Parent3

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-31401932841825357218262156312576000)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    14538852005, 141632070898485, 37207892755847079, 110039124095, 362951252492253153, 34822507625,
    4178700915, 110039124095, 218685347885, 34822507625, 3374997439015, 215899547275,
    9301989312567529, 110039124095, 4178700915, 215899547275, 4178700915, 110039124095,
    110039124095, 141632070898485, 22325, 16625, 17575, 1425,
    305425, 552425, 16625, 305425, 9025, 9025,
    17575, 17575, 552425, 17575, 22325, 1425,
    41486025, 1699690125, 34997935875, 1699690125, 41486025, 738989132819103,
    4305, 57769018051820847, 45045, 1995, 7221126417844413, 1995,
    3885, 73395, 3885, 45045, 73395, 1477980670977963,
    3885, 3885, 4305, 4978323, 203962815, 4199752305,
    203962815, 4978323, 585224253, 4551
  ]
def negativeCoefficients : Array ℕ := #[
    268194482061773982299932590080, 318927070861064358302350049280, 41892362987618570621977463095296, 2029863560275631177259831787520, 408646781369441526870935938793472, 1284723772326348846366982144000,
    77083426339580930782018928640, 2029863560275631177259831787520, 2017016322552367688796161966080, 1284723772326348846366982144000, 31128857003467432547471977349120, 1991321847105840711868822323200,
    41892435601883459849060702224384, 2029863560275631177259831787520, 77083426339580930782018928640, 1991321847105840711868822323200, 77083426339580930782018928640, 2029863560275631177259831787520,
    2029863560275631177259831787520, 318927070861064358302350049280, 210853663460129658791526400, 157018685555415703355392000, 165991181872868029261414400, 215339911618855821744537600,
    2884657566060922778786201600, 5217506608598527514352025600, 157018685555415703355392000, 2884657566060922778786201600, 170477430031594192214425600, 170477430031594192214425600,
    165991181872868029261414400, 165991181872868029261414400, 5217506608598527514352025600, 165991181872868029261414400, 210853663460129658791526400, 215339911618855821744537600,
    765282085810516301080166400, 125414994961945587999571968000, 1291195932388446321663541248000, 125414994961945587999571968000, 765282085810516301080166400, 832027795798739561756881846272,
    162638301670030581159690240, 32521066021467477916518935691264, 1701751985766905349207490560, 150737938133199075221176320, 32521062244599342984139634638848, 150737938133199075221176320,
    146771150287588573241671680, 5545569408163481767347486720, 146771150287588573241671680, 1701751985766905349207490560, 5545569408163481767347486720, 832029149884643727336806547456,
    146771150287588573241671680, 146771150287588573241671680, 162638301670030581159690240, 45916925148630978064809984, 7524899697716735279974318080, 77471755943306779299812474880,
    7524899697716735279974318080, 45916925148630978064809984, 5397741010409424641719271424, 171931918908318042940243968
  ]
def negativeScales : Array ℕ := #[
    33, 47, 55, 36, 58, 35,
    31, 36, 37, 35, 41, 37,
    53, 36, 31, 37, 31, 36,
    36, 47, 14, 14, 14, 10,
    18, 19, 14, 18, 13, 13,
    14, 14, 19, 14, 14, 10,
    25, 30, 35, 30, 25, 49,
    12, 55, 15, 10, 52, 10,
    11, 16, 11, 15, 16, 50,
    11, 11, 12, 22, 27, 31,
    27, 22, 29, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33759194306983470, 47009141311974823, 55046458204905099, 36679225604849256, 58332553407834321, 35019301046402822,
    31960407369762814, 36679225604849256, 37670065605554936, 35019301046402822, 41618023546088684, 37651569261924507,
    53046460705603117, 36679225604849256, 31960407369762814, 37651569261924507, 31960407369762814, 36679225604849256,
    36679225604849256, 47009141311974823, 14446372554895989, 14021066720163277, 14101237068847261, 10476746203939589,
    18220458630546258, 19075419084691529, 14021066720163277, 18220458630546258, 13139711216661896, 13139711216661896,
    14101237068847261, 14101237068847261, 19075419084691529, 14101237068847261, 14446372554895989, 10476746203939589,
    25306122095643427, 30662624602804861, 35026550785482210, 30662624602804861, 25306122095643427, 49392546477445026,
    12071797522284207, 55681145490439590, 15459079355165734, 10962173043893966, 52681145322890677, 10962173043893966,
    11923698889934521, 16163394163041560, 11923698889934521, 15459079355165734, 16163394163041560, 50392548825361092,
    11923698889934521, 11923698889934521, 12071797522284207, 22247228406589859, 27603730913728279, 31967657110430971,
    27603730913728279, 22247228406589859, 29124414318318620, 12151967870968190
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
noncomputable def negativeCeiling : ℝ := 5124701879 / 12500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 268194482061773982299932590080, coefficient := (-268194482061773982299932590080) }, { argument := 318927070861064358302350049280, coefficient := (-318927070861064358302350049280) }, { argument := 41892362987618570621977463095296, coefficient := (-41892362987618570621977463095296) }, { argument := 2029863560275631177259831787520, coefficient := (-2029863560275631177259831787520) }, { argument := 408646781369441526870935938793472, coefficient := (-408646781369441526870935938793472) }, { argument := 1284723772326348846366982144000, coefficient := (-1284723772326348846366982144000) }, { argument := 77083426339580930782018928640, coefficient := (-77083426339580930782018928640) }, { argument := 2029863560275631177259831787520, coefficient := (-2029863560275631177259831787520) }, { argument := 2017016322552367688796161966080, coefficient := (-2017016322552367688796161966080) }, { argument := 1284723772326348846366982144000, coefficient := (-1284723772326348846366982144000) }, { argument := 31128857003467432547471977349120, coefficient := (-31128857003467432547471977349120) }, { argument := 1991321847105840711868822323200, coefficient := (-1991321847105840711868822323200) }, { argument := 41892435601883459849060702224384, coefficient := (-41892435601883459849060702224384) }, { argument := 2029863560275631177259831787520, coefficient := (-2029863560275631177259831787520) }, { argument := 77083426339580930782018928640, coefficient := (-77083426339580930782018928640) }, { argument := 1991321847105840711868822323200, coefficient := (-1991321847105840711868822323200) }, { argument := 77083426339580930782018928640, coefficient := (-77083426339580930782018928640) }, { argument := 2029863560275631177259831787520, coefficient := (-2029863560275631177259831787520) }, { argument := 2029863560275631177259831787520, coefficient := (-2029863560275631177259831787520) }, { argument := 318927070861064358302350049280, coefficient := (-318927070861064358302350049280) }, { argument := 210853663460129658791526400, coefficient := (-210853663460129658791526400) }, { argument := 157018685555415703355392000, coefficient := (-157018685555415703355392000) }, { argument := 165991181872868029261414400, coefficient := (-165991181872868029261414400) }, { argument := 215339911618855821744537600, coefficient := (-215339911618855821744537600) }, { argument := 2884657566060922778786201600, coefficient := (-2884657566060922778786201600) }, { argument := 5217506608598527514352025600, coefficient := (-5217506608598527514352025600) }, { argument := 157018685555415703355392000, coefficient := (-157018685555415703355392000) }, { argument := 2884657566060922778786201600, coefficient := (-2884657566060922778786201600) }, { argument := 170477430031594192214425600, coefficient := (-170477430031594192214425600) }, { argument := 170477430031594192214425600, coefficient := (-170477430031594192214425600) }, { argument := 165991181872868029261414400, coefficient := (-165991181872868029261414400) }, { argument := 165991181872868029261414400, coefficient := (-165991181872868029261414400) }, { argument := 5217506608598527514352025600, coefficient := (-5217506608598527514352025600) }, { argument := 165991181872868029261414400, coefficient := (-165991181872868029261414400) }, { argument := 210853663460129658791526400, coefficient := (-210853663460129658791526400) }, { argument := 215339911618855821744537600, coefficient := (-215339911618855821744537600) }, { argument := 765282085810516301080166400, coefficient := (-765282085810516301080166400) }, { argument := 125414994961945587999571968000, coefficient := (-125414994961945587999571968000) }, { argument := 1291195932388446321663541248000, coefficient := (-1291195932388446321663541248000) }, { argument := 125414994961945587999571968000, coefficient := (-125414994961945587999571968000) }, { argument := 765282085810516301080166400, coefficient := (-765282085810516301080166400) }, { argument := 832027795798739561756881846272, coefficient := (-832027795798739561756881846272) }, { argument := 162638301670030581159690240, coefficient := (-162638301670030581159690240) }, { argument := 32521066021467477916518935691264, coefficient := (-32521066021467477916518935691264) }, { argument := 1701751985766905349207490560, coefficient := (-1701751985766905349207490560) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 32521062244599342984139634638848, coefficient := (-32521062244599342984139634638848) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 146771150287588573241671680, coefficient := (-146771150287588573241671680) }, { argument := 5545569408163481767347486720, coefficient := (-5545569408163481767347486720) }, { argument := 146771150287588573241671680, coefficient := (-146771150287588573241671680) }, { argument := 1701751985766905349207490560, coefficient := (-1701751985766905349207490560) }, { argument := 5545569408163481767347486720, coefficient := (-5545569408163481767347486720) }, { argument := 832029149884643727336806547456, coefficient := (-832029149884643727336806547456) }, { argument := 146771150287588573241671680, coefficient := (-146771150287588573241671680) }, { argument := 146771150287588573241671680, coefficient := (-146771150287588573241671680) }, { argument := 162638301670030581159690240, coefficient := (-162638301670030581159690240) }, { argument := 45916925148630978064809984, coefficient := (-45916925148630978064809984) }, { argument := 7524899697716735279974318080, coefficient := (-7524899697716735279974318080) }, { argument := 77471755943306779299812474880, coefficient := (-77471755943306779299812474880) }, { argument := 7524899697716735279974318080, coefficient := (-7524899697716735279974318080) }, { argument := 45916925148630978064809984, coefficient := (-45916925148630978064809984) }, { argument := 5397741010409424641719271424, coefficient := (-5397741010409424641719271424) }, { argument := 171931918908318042940243968, coefficient := (-171931918908318042940243968) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
