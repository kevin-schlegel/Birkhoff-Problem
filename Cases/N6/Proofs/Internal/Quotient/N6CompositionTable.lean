import N6KindRows0
import N6KindRows1
import N6KindRows2
import N6KindRows3
import N6KindRows4
import N6KindRows5
import N6KindRows6
import N6KindRows7
import N6KindRows8
import N6KindRows9
import N6KindRows10
import N6KindRows11
import N6KindRows12
import N6KindRows13
import N6KindRows14
import N6KindRows15
import N6KindRows16
import N6KindRows17
import N6KindRows18
import N6KindRows19
import N6KindRows20
import N6KindRows21
import N6KindRows22
import N6KindRows23
import N6KindRows24
import N6KindRows25
import N6KindRows26
import N6KindRows27
import N6KindRows28
import N6KindRows29
import N6KindRows30
import N6KindRows31
import N6KindRows32
import N6KindRows33
import N6KindRows34
import N6KindRows35
import N6KindRows36
import N6KindRows37
import N6KindRows38
import N6KindRows39
import N6KindRows40
import N6KindRows41
import N6KindRows42
import N6KindRows43
import N6KindRows44
import N6KindRows45
import N6KindRows46
import N6Products0
import N6Products1
import N6Products2
import N6Products3
import N6Products4
import N6Products5
import N6Products6
import N6Products7
import N6Products8
import N6Products9
import N6Products10
import N6Products11
import N6Products12
import N6Products13
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
theorem allowed_products (a b c : Fin 14) (h : Allowed a b c) (p q : Fin 3) : Normal ℤ c (basisInt a p*basisInt b q) := by
  fin_cases a
  · exact products_row0 b c h p q
  · exact products_row1 b c h p q
  · exact products_row2 b c h p q
  · exact products_row3 b c h p q
  · exact products_row4 b c h p q
  · exact products_row5 b c h p q
  · exact products_row6 b c h p q
  · exact products_row7 b c h p q
  · exact products_row8 b c h p q
  · exact products_row9 b c h p q
  · exact products_row10 b c h p q
  · exact products_row11 b c h p q
  · exact products_row12 b c h p q
  · exact products_row13 b c h p q
theorem kind_allowed (i j l : Fin 47) : Allowed (homKind i j) (homKind j l) (homKind i l) := by
  fin_cases i
  · exact kind_allowed_0 j l
  · exact kind_allowed_1 j l
  · exact kind_allowed_2 j l
  · exact kind_allowed_3 j l
  · exact kind_allowed_4 j l
  · exact kind_allowed_5 j l
  · exact kind_allowed_6 j l
  · exact kind_allowed_7 j l
  · exact kind_allowed_8 j l
  · exact kind_allowed_9 j l
  · exact kind_allowed_10 j l
  · exact kind_allowed_11 j l
  · exact kind_allowed_12 j l
  · exact kind_allowed_13 j l
  · exact kind_allowed_14 j l
  · exact kind_allowed_15 j l
  · exact kind_allowed_16 j l
  · exact kind_allowed_17 j l
  · exact kind_allowed_18 j l
  · exact kind_allowed_19 j l
  · exact kind_allowed_20 j l
  · exact kind_allowed_21 j l
  · exact kind_allowed_22 j l
  · exact kind_allowed_23 j l
  · exact kind_allowed_24 j l
  · exact kind_allowed_25 j l
  · exact kind_allowed_26 j l
  · exact kind_allowed_27 j l
  · exact kind_allowed_28 j l
  · exact kind_allowed_29 j l
  · exact kind_allowed_30 j l
  · exact kind_allowed_31 j l
  · exact kind_allowed_32 j l
  · exact kind_allowed_33 j l
  · exact kind_allowed_34 j l
  · exact kind_allowed_35 j l
  · exact kind_allowed_36 j l
  · exact kind_allowed_37 j l
  · exact kind_allowed_38 j l
  · exact kind_allowed_39 j l
  · exact kind_allowed_40 j l
  · exact kind_allowed_41 j l
  · exact kind_allowed_42 j l
  · exact kind_allowed_43 j l
  · exact kind_allowed_44 j l
  · exact kind_allowed_45 j l
  · exact kind_allowed_46 j l
end UniserialComputations.N6
