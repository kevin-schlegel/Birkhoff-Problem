import N6PathPresentation
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma defining_0 : word (a k) [1, 33]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 0
lemma defining_1 : word (a k) [1, 34, 64]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 1
lemma defining_2 : word (a k) [3, 39]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 2
lemma defining_3 : word (a k) [3, 40, 62, 52, 42]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 3
lemma defining_4 : word (a k) [4, 55]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 4
lemma defining_5 : word (a k) [4, 56, 43]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 5
lemma defining_6 : word (a k) [5, 64]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 6
lemma defining_7 : word (a k) [5, 65]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 7
lemma defining_8 : word (a k) [8, 68, 39]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 8
lemma defining_9 : word (a k) [8, 67]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 9
lemma defining_10 : word (a k) [9, 41, 44, 58, 33]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 10
lemma defining_11 : word (a k) [9, 42]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 11
lemma defining_12 : (-word (a k) [15, 1]) + word (a k) [16, 58]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 12
lemma defining_13 : word (a k) [16, 59]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 13
lemma defining_14 : word (a k) [17, 20]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 14
lemma defining_15 : word (a k) [19, 53, 55]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 15
lemma defining_16 : (-word (a k) [18, 9]) + word (a k) [19, 52]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 16
lemma defining_17 : word (a k) [20, 31]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 17
lemma defining_18 : word (a k) [21, 71]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 18
lemma defining_19 : word (a k) [23, 67]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 19
lemma defining_20 : word (a k) [22, 3] + word (a k) [23, 68]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 20
lemma defining_21 : word (a k) [25, 61]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 21
lemma defining_22 : (-word (a k) [24, 19]) + word (a k) [25, 62]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 22
lemma defining_23 : word (a k) [26, 30]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 23
lemma defining_24 : word (a k) [27, 57]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 24
lemma defining_25 : (-word (a k) [28, 14]) + word (a k) [29, 18]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 25
lemma defining_26 : word (a k) [31, 72]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 26
lemma defining_27 : word (a k) [32, 60]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 27
lemma defining_28 : (-word (a k) [33, 13]) + word (a k) [34, 65]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 28
lemma defining_29 : word (a k) [35, 54]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 29
lemma defining_30 : word (a k) [36, 69]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 30
lemma defining_31 : (-word (a k) [37, 24]) + word (a k) [38, 29]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 31
lemma defining_32 : (-word (a k) [39, 12]) + word (a k) [40, 61]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 32
lemma defining_33 : (-word (a k) [41, 43]) + word (a k) [42, 46]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 33
lemma defining_34 : (-word (a k) [43, 48]) + word (a k) [44, 59]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 34
lemma defining_35 : (-word (a k) [45, 6]) + word (a k) [46, 47]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 35
lemma defining_36 : (-word (a k) [47, 7]) + word (a k) [48, 50]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 36
lemma defining_37 : word (a k) [49, 70]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 37
lemma defining_38 : (-word (a k) [50, 17]) + word (a k) [51, 63]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 38
lemma defining_39 : (-word (a k) [52, 41]) + word (a k) [53, 56]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 39
lemma defining_40 : (-word (a k) [54, 16]) + (-word (a k) [55, 27]) + word (a k) [56, 44]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 40
lemma defining_41 : word (a k) [57, 5] + (-word (a k) [58, 34]) + word (a k) [59, 51]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 41
lemma defining_42 : (-word (a k) [60, 4]) + (-word (a k) [61, 35]) + word (a k) [62, 53]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 42
lemma defining_43 : word (a k) [63, 21] + (-word (a k) [64, 36]) + word (a k) [65, 49]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 43
lemma defining_44 : word (a k) [66, 25] + (-word (a k) [67, 32]) + word (a k) [68, 40]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 44
lemma defining_45 : (-word (a k) [69, 8]) + (-word (a k) [70, 23]) + word (a k) [71, 73]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 45
lemma defining_46 : (-word (a k) [72, 37]) + word (a k) [73, 66]=0 := by
  simpa [polynomial,relationTerms,add_assoc,neg_one_zsmul] using relation_zero k 46
end UniserialComputations.N6.Presentation
