import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk4Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 53; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk4.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left6.expected,
    Slot6.Left14.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left6.expected,
    Slot10.Left14.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left3.expected,
    Slot11.Left11.expected,
    Slot11.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 14998356610598159662448640 }, { target := 112, numerator := 574983133142519870568529920 }, { target := 115, numerator := 575046846184285854855331840 }, { target := 122, numerator := 14996600802063060912046080 }, { target := 206, numerator := 386362409749958052185899008 }, { target := 208, numerator := 14735937852599127481409077248 }, { target := 211, numerator := 14737397466835124908007096320 }, { target := 218, numerator := 386157621597639049884991488 }, { target := 257, numerator := 282372802894914378421764096 }, { target := 260, numerator := 1008285141039690282505863168 }, { target := 262, numerator := 282385943341688507980578816 }, { target := 302, numerator := 5278863813837649939399704576 }, { target := 304, numerator := 201031101375742618040308596736 }, { target := 307, numerator := 201050311316725546421510471680 }, { target := 314, numerator := 5275422179292777683485720576 }, { target := 353, numerator := 13937779068916229984514736128 }, { target := 356, numerator := 49781995419229071462969114624 }, { target := 358, numerator := 13938715908511511903834472448 }, { target := 679, numerator := 385074830579338130453692416 }, { target := 681, numerator := 14688828212556728126150803456 }, { target := 684, numerator := 14690287752224937672515256320 }, { target := 691, numerator := 384874931987949314067398656 }, { target := 695, numerator := 13935973140116145478431670272 }, { target := 698, numerator := 49775345225882790627656073216 }, { target := 700, numerator := 13936905605924118636536004608 }, { target := 966, numerator := 14709656985260973770145792 }, { target := 968, numerator := 564424008714101068201459712 }, { target := 971, numerator := 564487714018964367642460160 }, { target := 978, numerator := 14709005398837386272571392 }, { target := 982, numerator := 282981256707530609230086144 }, { target := 985, numerator := 1010588313781368315384430592 }, { target := 987, numerator := 282997202183614999623106560 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk0

namespace RouteChunk1

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left3.expected,
    Slot15.Left11.expected,
    Slot15.Left18.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot16.Left5.expected,
    Slot16.Left12.expected,
    Slot17.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 137278901372841820063531008 }, { target := 15, numerator := 6904319438659555799076962304 }, { target := 20, numerator := 6901531960325432465594253312 }, { target := 28, numerator := 138810713465517244214673408 }, { target := 56, numerator := 21382484391944658528239616 }, { target := 57, numerator := 570260415580133898804264960 }, { target := 59, numerator := 7402901038069798215553646592 }, { target := 67, numerator := 568975471975407134372265984 }, { target := 74, numerator := 21091169265095080201420800 }, { target := 110, numerator := 8701773358622518957572096 }, { target := 112, numerator := 303420603727613853809246208 }, { target := 115, numerator := 303562403018112852905951232 }, { target := 122, numerator := 8560122899706305480491008 }, { target := 152, numerator := 767238891402389155435511808 }, { target := 153, numerator := 20453565492968190107619164160 }, { target := 155, numerator := 265954042464786418355736150016 }, { target := 163, numerator := 20406564163218651143546601472 }, { target := 170, numerator := 756587936311694706134220800 }, { target := 206, numerator := 236944254667382712717803520 }, { target := 208, numerator := 8261967513751409979776040960 }, { target := 211, numerator := 8265828626402241836576931840 }, { target := 218, numerator := 233087194614452542463016960 }, { target := 283, numerator := 767381088294588631820009472 }, { target := 284, numerator := 20457437056694835238529925120 }, { target := 286, numerator := 266000171111069090723622027264 }, { target := 294, numerator := 20410435709139470722717974528 }, { target := 301, numerator := 756730082314907243092377600 }, { target := 302, numerator := 2821954509803596616294203392 }, { target := 304, numerator := 98398235137672167153274454016 }, { target := 307, numerator := 98444220149096774547605028864 }, { target := 314, numerator := 2776017763938080911697903616 }, { target := 660, numerator := 21192383325813141267283968 }, { target := 661, numerator := 565129817288814754875310080 }, { target := 663, numerator := 7339461358785793590575497216 }, { target := 671, numerator := 563849765990243624216952832 }, { target := 678, numerator := 20902213241420621702758400 }, { target := 679, numerator := 236945637061080607950372864 }, { target := 681, numerator := 8262015716193960266796367872 }, { target := 684, numerator := 8265876851371515984727769088 }, { target := 691, numerator := 233088554505070474608771072 }, { target := 966, numerator := 8699206056040713525657600 }, { target := 968, numerator := 303331084905734749342924800 }, { target := 971, numerator := 303472842360889434911539200 }, { target := 978, numerator := 8557597388558717209804800 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk1

namespace RouteChunk2

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot20.Left5.expected,
    Slot20.Left12.expected,
    Slot21.Left0.expected,
    Slot21.Left3.expected,
    Slot21.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 145093901522072558358233088 }, { target := 15, numerator := 7033459630256674185437773824 }, { target := 20, numerator := 7034441179790713012837416960 }, { target := 28, numerator := 144170543242013365015412736 }, { target := 56, numerator := 2317645577276020091781120 }, { target := 57, numerator := 53046248837206866099437568 }, { target := 59, numerator := 697917285571448340140261376 }, { target := 67, numerator := 53044995665011604031799296 }, { target := 74, numerator := 2317693776206607094382592 }, { target := 136, numerator := 1008285141039690282505863168 }, { target := 137, numerator := 49781995419229071462969114624 }, { target := 142, numerator := 49775345225882790627656073216 }, { target := 150, numerator := 1010588313781368315384430592 }, { target := 152, numerator := 111164845467744568942264320 }, { target := 153, numerator := 2544339873382347353565954048 }, { target := 155, numerator := 33475294048628366837846900736 }, { target := 163, numerator := 2544279765532037249400569856 }, { target := 170, numerator := 111167157308141111410163712 }, { target := 267, numerator := 282385943341688507980578816 }, { target := 268, numerator := 13938715908511511903834472448 }, { target := 273, numerator := 13936905605924118636536004608 }, { target := 281, numerator := 282997202183614999623106560 }, { target := 283, numerator := 111228160907810075941273600 }, { target := 284, numerator := 2545789036542531506054103040 }, { target := 286, numerator := 33494360354753230245493473280 }, { target := 294, numerator := 2545728894456982934525050880 }, { target := 301, numerator := 111230474064946559461621760 }, { target := 660, numerator := 2364340375956225125253120 }, { target := 661, numerator := 54114998923276837472698368 }, { target := 663, numerator := 711978584445065004608126976 }, { target := 671, numerator := 54113720502776164459216896 }, { target := 678, numerator := 2364389545975481779617792 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk4.Parent1
