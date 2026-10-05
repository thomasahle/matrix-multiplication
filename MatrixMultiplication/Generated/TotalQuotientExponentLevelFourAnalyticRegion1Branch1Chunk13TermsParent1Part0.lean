import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 13, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-13226645545333824099602232231591936)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3960663, 4533, 158477985, 3783, 93, 945,
    1905, 497217, 4533, 93, 445254214637589, 52689539162965995,
    31750873847, 320864181, 550015732193, 978908383753, 13171973176574375, 550015732193,
    15896408489, 16097735009, 31750873847, 31348220807, 978908383753, 31348220807,
    111312851113561, 320864181, 148327046868629, 13873447869221139, 8127467159, 569525394325406813,
    2550873165, 284252173, 8098713729, 16553147137, 2550873165, 254414384103,
    16286969875, 55493884227788035, 8098713729, 284252173, 16286969875, 284252173,
    8098713729, 8299987739, 148327046868629, 1790584372722335, 68337, 35066592465585917,
    743013, 32913, 70133192616760951, 32913, 64989, 1290249,
    65961, 743013, 1290249, 111912247202319, 64989, 65961,
    68337, 68337, 38745, 31725
  ]
def negativeCoefficients : Array ℕ := #[
    18703702201141937621012840448, 87680971845009824783089532928, 748391124636718391131436482560, 73173862009634274686615420928, 3597763239173136423925579776, 73115833570292772486229524480,
    73696117963707794490088488960, 18784327164103971073746272256, 87680971845009824783089532928, 3597763239173136423925579776, 125327919695436791630354448384, 14830786808791050674837882142720,
    36606265248265427667409436672, 47351195434619351289160531968, 634124965517390162105747898368, 1128604526668765516973555580928, 14830323372438630940446556160000, 634124965517390162105747898368,
    36654622385965869753620758528, 37118849734677190693321965568, 36606265248265427667409436672, 36142037899554106727708229632, 1128604526668765516973555580928, 36142037899554106727708229632,
    125327128699145205081979224064, 47351195434619351289160531968, 83500704125815457494752821248, 15620113663542080830667527028736, 149925306649552256063655378944, 160307147103871057509127792099328,
    94110608878496954442873569280, 5243527087726812217703661568, 149394899485100933630933336064, 152675834425348490650972061696, 94110608878496954442873569280, 2346558516109240404446464180224,
    150220782510171123334774784000, 15620139770600477474495093800960, 149394899485100933630933336064, 5243527087726812217703661568, 150220782510171123334774784000, 5243527087726812217703661568,
    149394899485100933630933336064, 153107749636260190659987636224, 83500704125815457494752821248, 504004694610483826770323701760, 322712358339862944968343552, 19740736595145722297472834863104,
    3508779687536423699163906048, 310854496101377265836752896, 19740738758446740012719046393856, 310854496101377265836752896, 306901875355215372792889344, 12186057264312153734652100608,
    311492015576564667940601856, 3508779687536423699163906048, 12186057264312153734652100608, 504007954798558681874483380224, 306901875355215372792889344, 311492015576564667940601856,
    322712358339862944968343552, 322712358339862944968343552, 365936178757568807609303040, 299634153338078988809011200
  ]
def negativeScales : Array ℕ := #[
    21, 12, 27, 11, 6, 9,
    10, 18, 12, 6, 48, 55,
    34, 28, 39, 39, 53, 39,
    33, 33, 34, 34, 39, 34,
    46, 28, 47, 53, 32, 58,
    31, 28, 32, 33, 31, 37,
    33, 55, 32, 28, 33, 28,
    32, 32, 47, 50, 16, 54,
    19, 15, 55, 15, 15, 20,
    16, 19, 20, 46, 15, 16,
    16, 16, 15, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    21917310527473222, 12146250445885986, 27239707201121241, 11885315064398008, 6539158811108986, 9884170522387776,
    10895575286414346, 18923516104469719, 12146250445885986, 6539158811108986, 48661622595944660, 55548366079762588,
    34886077250528281, 28257387505471729, 39000681928638685, 39832382889000270, 53548320997341640, 39000681928638685,
    33887981803408484, 33906138665617761, 34886077250528281, 34867664515346945, 39832382889000270, 34867664515346945,
    46661613490471338, 28257387505471729, 47075775020115938, 53623175893156979, 32920158681596382, 58982537802040945,
    31248344020753137, 28082596137114720, 32915045651127698, 33946386491560915, 31248344020753137, 37888389287450831,
    33922999176672344, 55623178304438550, 32915045651127698, 28082596137114720, 33922999176672344, 28082596137114720,
    32915045651127698, 32950462069759098, 47075775020115938, 50669351923707029, 16060379294274153, 54960946776773436,
    19503027927289084, 15006369912783681, 55960946934872102, 15006369912783681, 15987907948136922, 20299218081794152,
    16009325650430725, 19503027927289084, 20299218081794152, 46669361255846214, 15987907948136922, 16009325650430725,
    16060379294274153, 16060379294274153, 15241722523726519, 14953332554642086
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
noncomputable def negativeCeiling : ℝ := 36952935029 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 18703702201141937621012840448, coefficient := (-18703702201141937621012840448) }, { argument := 87680971845009824783089532928, coefficient := (-87680971845009824783089532928) }, { argument := 748391124636718391131436482560, coefficient := (-748391124636718391131436482560) }, { argument := 73173862009634274686615420928, coefficient := (-73173862009634274686615420928) }, { argument := 3597763239173136423925579776, coefficient := (-3597763239173136423925579776) }, { argument := 73115833570292772486229524480, coefficient := (-73115833570292772486229524480) }, { argument := 73696117963707794490088488960, coefficient := (-73696117963707794490088488960) }, { argument := 18784327164103971073746272256, coefficient := (-18784327164103971073746272256) }, { argument := 87680971845009824783089532928, coefficient := (-87680971845009824783089532928) }, { argument := 3597763239173136423925579776, coefficient := (-3597763239173136423925579776) }, { argument := 125327919695436791630354448384, coefficient := (-125327919695436791630354448384) }, { argument := 14830786808791050674837882142720, coefficient := (-14830786808791050674837882142720) }, { argument := 36606265248265427667409436672, coefficient := (-36606265248265427667409436672) }, { argument := 47351195434619351289160531968, coefficient := (-47351195434619351289160531968) }, { argument := 634124965517390162105747898368, coefficient := (-634124965517390162105747898368) }, { argument := 1128604526668765516973555580928, coefficient := (-1128604526668765516973555580928) }, { argument := 14830323372438630940446556160000, coefficient := (-14830323372438630940446556160000) }, { argument := 634124965517390162105747898368, coefficient := (-634124965517390162105747898368) }, { argument := 36654622385965869753620758528, coefficient := (-36654622385965869753620758528) }, { argument := 37118849734677190693321965568, coefficient := (-37118849734677190693321965568) }, { argument := 36606265248265427667409436672, coefficient := (-36606265248265427667409436672) }, { argument := 36142037899554106727708229632, coefficient := (-36142037899554106727708229632) }, { argument := 1128604526668765516973555580928, coefficient := (-1128604526668765516973555580928) }, { argument := 36142037899554106727708229632, coefficient := (-36142037899554106727708229632) }, { argument := 125327128699145205081979224064, coefficient := (-125327128699145205081979224064) }, { argument := 47351195434619351289160531968, coefficient := (-47351195434619351289160531968) }, { argument := 83500704125815457494752821248, coefficient := (-83500704125815457494752821248) }, { argument := 15620113663542080830667527028736, coefficient := (-15620113663542080830667527028736) }, { argument := 149925306649552256063655378944, coefficient := (-149925306649552256063655378944) }, { argument := 160307147103871057509127792099328, coefficient := (-160307147103871057509127792099328) }, { argument := 94110608878496954442873569280, coefficient := (-94110608878496954442873569280) }, { argument := 5243527087726812217703661568, coefficient := (-5243527087726812217703661568) }, { argument := 149394899485100933630933336064, coefficient := (-149394899485100933630933336064) }, { argument := 152675834425348490650972061696, coefficient := (-152675834425348490650972061696) }, { argument := 94110608878496954442873569280, coefficient := (-94110608878496954442873569280) }, { argument := 2346558516109240404446464180224, coefficient := (-2346558516109240404446464180224) }, { argument := 150220782510171123334774784000, coefficient := (-150220782510171123334774784000) }, { argument := 15620139770600477474495093800960, coefficient := (-15620139770600477474495093800960) }, { argument := 149394899485100933630933336064, coefficient := (-149394899485100933630933336064) }, { argument := 5243527087726812217703661568, coefficient := (-5243527087726812217703661568) }, { argument := 150220782510171123334774784000, coefficient := (-150220782510171123334774784000) }, { argument := 5243527087726812217703661568, coefficient := (-5243527087726812217703661568) }, { argument := 149394899485100933630933336064, coefficient := (-149394899485100933630933336064) }, { argument := 153107749636260190659987636224, coefficient := (-153107749636260190659987636224) }, { argument := 83500704125815457494752821248, coefficient := (-83500704125815457494752821248) }, { argument := 504004694610483826770323701760, coefficient := (-504004694610483826770323701760) }, { argument := 322712358339862944968343552, coefficient := (-322712358339862944968343552) }, { argument := 19740736595145722297472834863104, coefficient := (-19740736595145722297472834863104) }, { argument := 3508779687536423699163906048, coefficient := (-3508779687536423699163906048) }, { argument := 310854496101377265836752896, coefficient := (-310854496101377265836752896) }, { argument := 19740738758446740012719046393856, coefficient := (-19740738758446740012719046393856) }, { argument := 310854496101377265836752896, coefficient := (-310854496101377265836752896) }, { argument := 306901875355215372792889344, coefficient := (-306901875355215372792889344) }, { argument := 12186057264312153734652100608, coefficient := (-12186057264312153734652100608) }, { argument := 311492015576564667940601856, coefficient := (-311492015576564667940601856) }, { argument := 3508779687536423699163906048, coefficient := (-3508779687536423699163906048) }, { argument := 12186057264312153734652100608, coefficient := (-12186057264312153734652100608) }, { argument := 504007954798558681874483380224, coefficient := (-504007954798558681874483380224) }, { argument := 306901875355215372792889344, coefficient := (-306901875355215372792889344) }, { argument := 311492015576564667940601856, coefficient := (-311492015576564667940601856) }, { argument := 322712358339862944968343552, coefficient := (-322712358339862944968343552) }, { argument := 322712358339862944968343552, coefficient := (-322712358339862944968343552) }, { argument := 365936178757568807609303040, coefficient := (-365936178757568807609303040) }, { argument := 299634153338078988809011200, coefficient := (-299634153338078988809011200) }] }

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
def constantNumerator : ℤ := (-114067990391520661103458511161917440)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    421335, 74655, 31725, 74655, 36855, 2927367,
    74817, 421335, 2927367, 68337, 36855, 74817,
    38745, 148099819240929, 537878613432349, 74051646731521, 445254288517099, 52689537864824853,
    31750888713, 320864331, 550015989279, 978908837367, 13171972851744345, 550015989279,
    15896415831, 16097742495, 31750888713, 31348235385, 978908837367, 31348235385,
    111312869583271, 320864331, 538693415797681, 50710040220309933, 237196998507, 2082911736528272855,
    18611375175, 16589847423, 472713638139, 120777868689, 18611375175, 7425168358509,
    475341047115, 202840504498445489, 472713638139, 16589847423, 475341047115, 16589847423,
    472713638139, 60559518783, 538693415797681, 35066694420104657, 31725, 1374206182947979821,
    344385, 15255, 1374206332604120883, 15255, 30105, 596511,
    30537, 344385, 596511, 35066921333029071
  ]
def negativeCoefficients : Array ℕ := #[
    3979396564119763932225208320, 352548269778633363428474880, 299634153338078988809011200, 352548269778633363428474880, 348085633452321548701532160, 13824099803858664700281618432,
    353313293148858245953093632, 3979396564119763932225208320, 13824099803858664700281618432, 322712358339862944968343552, 348085633452321548701532160, 353313293148858245953093632,
    365936178757568807609303040, 83372786343385707270371278848, 302798740378060752612006821888, 83374742156562395912527151104, 125327940490670148275031506944, 14830786443396802963243498733568,
    36606282387596515152796581888, 47351217570712239740622471168, 634125261917368095461609570304, 1128605049650100907703839752192, 14830323006712530423759796961280, 634125261917368095461609570304,
    36654639315465243400561754112, 37118866996217957667034890240, 36606282387596515152796581888, 36142054706843800886323445760, 1128605049650100907703839752192, 36142054706843800886323445760,
    125327149494189973492260143104, 47351217570712239740622471168, 303257433331671976855545577472, 57094429560032669786164734984192, 546939040813836951576498929664, 586287532529647648216812754042880,
    343319274713016319106403532800, 19126791852123182932948942848, 545001718931392482874610417664, 556989608368520290550578937856, 343319274713016319106403532800, 8560636275851348442188070518784,
    548030915241219937970411274240, 57094526279677657618430541430784, 545001718931392482874610417664, 19126791852123182932948942848, 548030915241219937970411274240, 19126791852123182932948942848,
    545001718931392482874610417664, 558562972108503763787830001664, 303257433331671976855545577472, 19740793990437298072754254249984, 299634153338078988809011200, 773609306681844197027077687345152,
    3252624362406125533837393920, 288158802784705750939729920, 773609390930761837093275876458496, 288158802784705750939729920, 284333685933581338316636160, 11267774212252219744268058624,
    288413810574780711781269504, 3252624362406125533837393920, 11267774212252219744268058624, 19740921731057527627744806961152
  ]
def negativeScales : Array ℕ := #[
    18, 16, 14, 16, 15, 21,
    16, 18, 21, 16, 15, 16,
    15, 47, 48, 46, 48, 55,
    34, 28, 39, 39, 53, 39,
    33, 33, 34, 34, 39, 34,
    46, 28, 48, 55, 37, 60,
    34, 33, 38, 36, 34, 42,
    38, 57, 38, 33, 38, 33,
    38, 35, 48, 54, 14, 60,
    18, 13, 60, 13, 14, 19,
    14, 18, 19, 54
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    18684608239020224, 16187951267285539, 14953332554642086, 16187951267285539, 15169572737970684, 21481172195115125,
    16191078497644886, 18684608239020224, 21481172195115125, 16060379294274153, 15169572737970684, 16191078497644886,
    15241722523726519, 47073563208210033, 48934273963530729, 46073597051493906, 48661622835326097, 55548366044218116,
    34886077926008927, 28257388179913497, 39000682602976870, 39832383557527114, 53548320961763775, 39000682602976870,
    33887982469739198, 33906139336520438, 34886077926008927, 34867665186249593, 39832383557527114, 34867665186249593,
    46661613729852115, 28257388179913497, 48936457768586749, 55493120936866388, 37787294798381585, 60853307416228542,
    34115465607433222, 33949581577097698, 38782175532326945, 36813565164358492, 34115465607433222, 42755560876900736,
    38790172032321715, 57493123380832202, 38782175532326945, 33949581577097698, 38790172032321715, 33949581577097698,
    38782175532326945, 35817634691246090, 48936457768586749, 54960950971338266, 14953332554642086, 60253304187237987,
    18393662780653309, 13896994563604115, 60253304344352810, 13896994563604115, 14877715499884064, 19186189216714610,
    14898270720387434, 18393662780653309, 19186189216714610, 54960960306839242
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
noncomputable def negativeCeiling : ℝ := 1684166435613 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3979396564119763932225208320, coefficient := (-3979396564119763932225208320) }, { argument := 352548269778633363428474880, coefficient := (-352548269778633363428474880) }, { argument := 299634153338078988809011200, coefficient := (-299634153338078988809011200) }, { argument := 352548269778633363428474880, coefficient := (-352548269778633363428474880) }, { argument := 348085633452321548701532160, coefficient := (-348085633452321548701532160) }, { argument := 13824099803858664700281618432, coefficient := (-13824099803858664700281618432) }, { argument := 353313293148858245953093632, coefficient := (-353313293148858245953093632) }, { argument := 3979396564119763932225208320, coefficient := (-3979396564119763932225208320) }, { argument := 13824099803858664700281618432, coefficient := (-13824099803858664700281618432) }, { argument := 322712358339862944968343552, coefficient := (-322712358339862944968343552) }, { argument := 348085633452321548701532160, coefficient := (-348085633452321548701532160) }, { argument := 353313293148858245953093632, coefficient := (-353313293148858245953093632) }, { argument := 365936178757568807609303040, coefficient := (-365936178757568807609303040) }, { argument := 83372786343385707270371278848, coefficient := (-83372786343385707270371278848) }, { argument := 302798740378060752612006821888, coefficient := (-302798740378060752612006821888) }, { argument := 83374742156562395912527151104, coefficient := (-83374742156562395912527151104) }, { argument := 125327940490670148275031506944, coefficient := (-125327940490670148275031506944) }, { argument := 14830786443396802963243498733568, coefficient := (-14830786443396802963243498733568) }, { argument := 36606282387596515152796581888, coefficient := (-36606282387596515152796581888) }, { argument := 47351217570712239740622471168, coefficient := (-47351217570712239740622471168) }, { argument := 634125261917368095461609570304, coefficient := (-634125261917368095461609570304) }, { argument := 1128605049650100907703839752192, coefficient := (-1128605049650100907703839752192) }, { argument := 14830323006712530423759796961280, coefficient := (-14830323006712530423759796961280) }, { argument := 634125261917368095461609570304, coefficient := (-634125261917368095461609570304) }, { argument := 36654639315465243400561754112, coefficient := (-36654639315465243400561754112) }, { argument := 37118866996217957667034890240, coefficient := (-37118866996217957667034890240) }, { argument := 36606282387596515152796581888, coefficient := (-36606282387596515152796581888) }, { argument := 36142054706843800886323445760, coefficient := (-36142054706843800886323445760) }, { argument := 1128605049650100907703839752192, coefficient := (-1128605049650100907703839752192) }, { argument := 36142054706843800886323445760, coefficient := (-36142054706843800886323445760) }, { argument := 125327149494189973492260143104, coefficient := (-125327149494189973492260143104) }, { argument := 47351217570712239740622471168, coefficient := (-47351217570712239740622471168) }, { argument := 303257433331671976855545577472, coefficient := (-303257433331671976855545577472) }, { argument := 57094429560032669786164734984192, coefficient := (-57094429560032669786164734984192) }, { argument := 546939040813836951576498929664, coefficient := (-546939040813836951576498929664) }, { argument := 586287532529647648216812754042880, coefficient := (-586287532529647648216812754042880) }, { argument := 343319274713016319106403532800, coefficient := (-343319274713016319106403532800) }, { argument := 19126791852123182932948942848, coefficient := (-19126791852123182932948942848) }, { argument := 545001718931392482874610417664, coefficient := (-545001718931392482874610417664) }, { argument := 556989608368520290550578937856, coefficient := (-556989608368520290550578937856) }, { argument := 343319274713016319106403532800, coefficient := (-343319274713016319106403532800) }, { argument := 8560636275851348442188070518784, coefficient := (-8560636275851348442188070518784) }, { argument := 548030915241219937970411274240, coefficient := (-548030915241219937970411274240) }, { argument := 57094526279677657618430541430784, coefficient := (-57094526279677657618430541430784) }, { argument := 545001718931392482874610417664, coefficient := (-545001718931392482874610417664) }, { argument := 19126791852123182932948942848, coefficient := (-19126791852123182932948942848) }, { argument := 548030915241219937970411274240, coefficient := (-548030915241219937970411274240) }, { argument := 19126791852123182932948942848, coefficient := (-19126791852123182932948942848) }, { argument := 545001718931392482874610417664, coefficient := (-545001718931392482874610417664) }, { argument := 558562972108503763787830001664, coefficient := (-558562972108503763787830001664) }, { argument := 303257433331671976855545577472, coefficient := (-303257433331671976855545577472) }, { argument := 19740793990437298072754254249984, coefficient := (-19740793990437298072754254249984) }, { argument := 299634153338078988809011200, coefficient := (-299634153338078988809011200) }, { argument := 773609306681844197027077687345152, coefficient := (-773609306681844197027077687345152) }, { argument := 3252624362406125533837393920, coefficient := (-3252624362406125533837393920) }, { argument := 288158802784705750939729920, coefficient := (-288158802784705750939729920) }, { argument := 773609390930761837093275876458496, coefficient := (-773609390930761837093275876458496) }, { argument := 288158802784705750939729920, coefficient := (-288158802784705750939729920) }, { argument := 284333685933581338316636160, coefficient := (-284333685933581338316636160) }, { argument := 11267774212252219744268058624, coefficient := (-11267774212252219744268058624) }, { argument := 288413810574780711781269504, coefficient := (-288413810574780711781269504) }, { argument := 3252624362406125533837393920, coefficient := (-3252624362406125533837393920) }, { argument := 11267774212252219744268058624, coefficient := (-11267774212252219744268058624) }, { argument := 19740921731057527627744806961152, coefficient := (-19740921731057527627744806961152) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
