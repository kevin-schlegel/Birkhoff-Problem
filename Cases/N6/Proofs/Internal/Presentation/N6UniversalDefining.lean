import N6Defining
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma defining_0 : word v [1, 33]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 0
lemma defining_1 : word v [1, 34, 64]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 1
lemma defining_2 : word v [3, 39]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 2
lemma defining_3 : word v [3, 40, 62, 52, 42]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 3
lemma defining_4 : word v [4, 55]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 4
lemma defining_5 : word v [4, 56, 43]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 5
lemma defining_6 : word v [5, 64]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 6
lemma defining_7 : word v [5, 65]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 7
lemma defining_8 : word v [8, 68, 39]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 8
lemma defining_9 : word v [8, 67]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 9
lemma defining_10 : word v [9, 41, 44, 58, 33]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 10
lemma defining_11 : word v [9, 42]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 11
lemma defining_12 : (-word v [15, 1]) + word v [16, 58]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 12
lemma defining_13 : word v [16, 59]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 13
lemma defining_14 : word v [17, 20]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 14
lemma defining_15 : word v [19, 53, 55]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 15
lemma defining_16 : (-word v [18, 9]) + word v [19, 52]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 16
lemma defining_17 : word v [20, 31]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 17
lemma defining_18 : word v [21, 71]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 18
lemma defining_19 : word v [23, 67]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 19
lemma defining_20 : word v [22, 3] + word v [23, 68]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 20
lemma defining_21 : word v [25, 61]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 21
lemma defining_22 : (-word v [24, 19]) + word v [25, 62]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 22
lemma defining_23 : word v [26, 30]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 23
lemma defining_24 : word v [27, 57]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 24
lemma defining_25 : (-word v [28, 14]) + word v [29, 18]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 25
lemma defining_26 : word v [31, 72]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 26
lemma defining_27 : word v [32, 60]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 27
lemma defining_28 : (-word v [33, 13]) + word v [34, 65]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 28
lemma defining_29 : word v [35, 54]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 29
lemma defining_30 : word v [36, 69]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 30
lemma defining_31 : (-word v [37, 24]) + word v [38, 29]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 31
lemma defining_32 : (-word v [39, 12]) + word v [40, 61]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 32
lemma defining_33 : (-word v [41, 43]) + word v [42, 46]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 33
lemma defining_34 : (-word v [43, 48]) + word v [44, 59]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 34
lemma defining_35 : (-word v [45, 6]) + word v [46, 47]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 35
lemma defining_36 : (-word v [47, 7]) + word v [48, 50]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 36
lemma defining_37 : word v [49, 70]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 37
lemma defining_38 : (-word v [50, 17]) + word v [51, 63]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 38
lemma defining_39 : (-word v [52, 41]) + word v [53, 56]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 39
lemma defining_40 : (-word v [54, 16]) + (-word v [55, 27]) + word v [56, 44]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 40
lemma defining_41 : word v [57, 5] + (-word v [58, 34]) + word v [59, 51]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 41
lemma defining_42 : (-word v [60, 4]) + (-word v [61, 35]) + word v [62, 53]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 42
lemma defining_43 : word v [63, 21] + (-word v [64, 36]) + word v [65, 49]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 43
lemma defining_44 : word v [66, 25] + (-word v [67, 32]) + word v [68, 40]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 44
lemma defining_45 : (-word v [69, 8]) + (-word v [70, 23]) + word v [71, 73]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 45
lemma defining_46 : (-word v [72, 37]) + word v [73, 66]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using H 46
end UniserialComputations.N6.Presentation.Universal
