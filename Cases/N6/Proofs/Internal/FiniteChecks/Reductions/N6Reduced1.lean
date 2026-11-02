import N6Rules29
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma reduced_60 : word v [17, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_60 v H)
lemma mul_reduced_60 (x : A) : word v [17, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_60 v H)
lemma reduced_61 : word v [63, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_61 v H)
lemma mul_reduced_61 (x : A) : word v [63, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_61 v H)
lemma reduced_62 : word v [70, 23, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_62 v H)
lemma mul_reduced_62 (x : A) : word v [70, 23, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_62 v H)
lemma reduced_63 : word v [70, 23, 68]=(-word v [70, 22, 3]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_63 v H)
lemma mul_reduced_63 (x : A) : word v [70, 23, 68]*x=(-(word v [70, 22, 3]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_63 v H)
lemma reduced_64 : word v [37, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_64 v H)
lemma mul_reduced_64 (x : A) : word v [37, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_64 v H)
lemma reduced_65 : word v [66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_65 v H)
lemma mul_reduced_65 (x : A) : word v [66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_65 v H)
lemma reduced_66 : word v [37, 25, 62]=word v [37, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_66 v H)
lemma mul_reduced_66 (x : A) : word v [37, 25, 62]*x=(word v [37, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_66 v H)
lemma reduced_67 : word v [66, 25, 62]=word v [66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_67 v H)
lemma mul_reduced_67 (x : A) : word v [66, 25, 62]*x=(word v [66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_67 v H)
lemma reduced_68 : word v [11, 26, 30]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_68 v H)
lemma mul_reduced_68 (x : A) : word v [11, 26, 30]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_68 v H)
lemma reduced_69 : word v [55, 27, 57]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_69 v H)
lemma mul_reduced_69 (x : A) : word v [55, 27, 57]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_69 v H)
lemma reduced_70 : word v [38, 28, 14]=word v [37, 24, 18] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_70 v H)
lemma mul_reduced_70 (x : A) : word v [38, 28, 14]*x=(word v [37, 24, 18]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_70 v H)
lemma reduced_71 : word v [26, 31, 72]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_71 v H)
lemma mul_reduced_71 (x : A) : word v [26, 31, 72]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_71 v H)
lemma reduced_72 : word v [67, 32, 60]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_72 v H)
lemma mul_reduced_72 (x : A) : word v [67, 32, 60]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_72 v H)
lemma reduced_73 : word v [1, 34, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_73 v H)
lemma mul_reduced_73 (x : A) : word v [1, 34, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_73 v H)
lemma reduced_74 : word v [58, 34, 65]=word v [58, 33, 13] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_74 v H)
lemma mul_reduced_74 (x : A) : word v [58, 34, 65]*x=(word v [58, 33, 13]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_74 v H)
lemma reduced_75 : word v [12, 35, 54]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_75 v H)
lemma mul_reduced_75 (x : A) : word v [12, 35, 54]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_75 v H)
lemma reduced_76 : word v [61, 35, 54]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_76 v H)
lemma mul_reduced_76 (x : A) : word v [61, 35, 54]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_76 v H)
lemma reduced_77 : word v [64, 36, 69]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_77 v H)
lemma mul_reduced_77 (x : A) : word v [64, 36, 69]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_77 v H)
lemma reduced_78 : word v [72, 38, 29]=word v [72, 37, 24] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_78 v H)
lemma mul_reduced_78 (x : A) : word v [72, 38, 29]*x=(word v [72, 37, 24]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_78 v H)
lemma reduced_79 : word v [3, 40, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_79 v H)
lemma mul_reduced_79 (x : A) : word v [3, 40, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_79 v H)
lemma reduced_80 : word v [68, 39, 12]=word v [67, 32, 61] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_80 v H)
lemma mul_reduced_80 (x : A) : word v [68, 39, 12]*x=(word v [67, 32, 61]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_80 v H)
lemma reduced_81 : word v [9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_81 v H)
lemma mul_reduced_81 (x : A) : word v [9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_81 v H)
lemma reduced_82 : word v [52, 42, 46]=word v [52, 41, 43] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_82 v H)
lemma mul_reduced_82 (x : A) : word v [52, 42, 46]*x=(word v [52, 41, 43]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_82 v H)
lemma reduced_83 : word v [41, 44, 59]=word v [41, 43, 48] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_83 v H)
lemma mul_reduced_83 (x : A) : word v [41, 44, 59]*x=(word v [41, 43, 48]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_83 v H)
lemma reduced_84 : word v [56, 43, 48]=word v [55, 27, 59] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_84 v H)
lemma mul_reduced_84 (x : A) : word v [56, 43, 48]*x=(word v [55, 27, 59]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_84 v H)
lemma reduced_85 : word v [42, 45, 6]=word v [41, 43, 47] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_85 v H)
lemma mul_reduced_85 (x : A) : word v [42, 45, 6]*x=(word v [41, 43, 47]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_85 v H)
lemma reduced_86 : word v [43, 48, 50]=word v [43, 47, 7] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_86 v H)
lemma mul_reduced_86 (x : A) : word v [43, 48, 50]*x=(word v [43, 47, 7]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_86 v H)
lemma reduced_87 : word v [46, 48, 50]=word v [45, 6, 7] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_87 v H)
lemma mul_reduced_87 (x : A) : word v [46, 48, 50]*x=(word v [45, 6, 7]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_87 v H)
lemma reduced_88 : word v [13, 49, 70]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_88 v H)
lemma mul_reduced_88 (x : A) : word v [13, 49, 70]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_88 v H)
lemma reduced_89 : word v [64, 36, 70]=word v [63, 21, 70] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_89 v H)
lemma mul_reduced_89 (x : A) : word v [64, 36, 70]*x=(word v [63, 21, 70]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_89 v H)
lemma reduced_90 : word v [48, 51, 63]=word v [47, 7, 17] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_90 v H)
lemma mul_reduced_90 (x : A) : word v [48, 51, 63]*x=(word v [47, 7, 17]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_90 v H)
lemma reduced_91 : word v [59, 50, 17]=(-word v [57, 5, 63]) + word v [58, 34, 63] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_91 v H)
lemma mul_reduced_91 (x : A) : word v [59, 50, 17]*x=(-(word v [57, 5, 63]*x)) + (word v [58, 34, 63]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_91 v H)
lemma reduced_92 : word v [19, 53, 56]=word v [18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_92 v H)
lemma mul_reduced_92 (x : A) : word v [19, 53, 56]*x=(word v [18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_92 v H)
lemma reduced_93 : word v [62, 52, 41]=word v [60, 4, 56] + word v [61, 35, 56] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_93 v H)
lemma mul_reduced_93 (x : A) : word v [62, 52, 41]*x=(word v [60, 4, 56]*x) + (word v [61, 35, 56]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_93 v H)
lemma reduced_94 : word v [4, 56, 44]=word v [4, 54, 16] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_94 v H)
lemma mul_reduced_94 (x : A) : word v [4, 56, 44]*x=(word v [4, 54, 16]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_94 v H)
lemma reduced_95 : word v [35, 56, 44]=word v [35, 55, 27] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_95 v H)
lemma mul_reduced_95 (x : A) : word v [35, 56, 44]*x=(word v [35, 55, 27]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_95 v H)
lemma reduced_96 : word v [53, 55, 27]=(-word v [53, 54, 16]) + word v [52, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_96 v H)
lemma mul_reduced_96 (x : A) : word v [53, 55, 27]*x=(-(word v [53, 54, 16]*x)) + (word v [52, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_96 v H)
lemma reduced_97 : word v [16, 57, 5]=word v [15, 1, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_97 v H)
lemma mul_reduced_97 (x : A) : word v [16, 57, 5]*x=(word v [15, 1, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_97 v H)
lemma reduced_98 : word v [27, 59, 51]=word v [27, 58, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_98 v H)
lemma mul_reduced_98 (x : A) : word v [27, 59, 51]*x=(word v [27, 58, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_98 v H)
lemma reduced_99 : word v [44, 58, 34]=word v [44, 57, 5] + word v [43, 48, 51] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_99 v H)
lemma mul_reduced_99 (x : A) : word v [44, 58, 34]*x=(word v [44, 57, 5]*x) + (word v [43, 48, 51]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_99 v H)
lemma reduced_100 : word v [25, 60, 4]=word v [24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_100 v H)
lemma mul_reduced_100 (x : A) : word v [25, 60, 4]*x=(word v [24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_100 v H)
lemma reduced_101 : word v [32, 62, 53]=word v [32, 61, 35] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_101 v H)
lemma mul_reduced_101 (x : A) : word v [32, 62, 53]*x=(word v [32, 61, 35]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_101 v H)
lemma reduced_102 : word v [40, 62, 53]=word v [40, 60, 4] + word v [39, 12, 35] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_102 v H)
lemma mul_reduced_102 (x : A) : word v [40, 62, 53]*x=(word v [40, 60, 4]*x) + (word v [39, 12, 35]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_102 v H)
lemma reduced_103 : word v [5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_103 v H)
lemma mul_reduced_103 (x : A) : word v [5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_103 v H)
lemma reduced_104 : word v [34, 64, 36]=word v [34, 63, 21] + word v [33, 13, 49] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_104 v H)
lemma mul_reduced_104 (x : A) : word v [34, 64, 36]*x=(word v [34, 63, 21]*x) + (word v [33, 13, 49]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_104 v H)
lemma reduced_105 : word v [51, 65, 49]=(-word v [50, 17, 21]) + word v [51, 64, 36] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_105 v H)
lemma mul_reduced_105 (x : A) : word v [51, 65, 49]*x=(-(word v [50, 17, 21]*x)) + (word v [51, 64, 36]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_105 v H)
lemma reduced_106 : word v [8, 68, 40]=(-word v [8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_106 v H)
lemma mul_reduced_106 (x : A) : word v [8, 68, 40]*x=(-(word v [8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_106 v H)
lemma reduced_107 : word v [23, 66, 25]=word v [22, 3, 40] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_107 v H)
lemma mul_reduced_107 (x : A) : word v [23, 66, 25]*x=(word v [22, 3, 40]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_107 v H)
lemma reduced_108 : word v [73, 68, 40]=(-word v [72, 37, 25]) + word v [73, 67, 32] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_108 v H)
lemma mul_reduced_108 (x : A) : word v [73, 68, 40]*x=(-(word v [72, 37, 25]*x)) + (word v [73, 67, 32]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_108 v H)
lemma reduced_109 : word v [21, 70, 23]=(-word v [21, 69, 8]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_109 v H)
lemma mul_reduced_109 (x : A) : word v [21, 70, 23]*x=(-(word v [21, 69, 8]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_109 v H)
lemma reduced_110 : word v [36, 71, 73]=word v [36, 70, 23] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_110 v H)
lemma mul_reduced_110 (x : A) : word v [36, 71, 73]*x=(word v [36, 70, 23]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_110 v H)
lemma reduced_111 : word v [49, 71, 73]=word v [49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_111 v H)
lemma mul_reduced_111 (x : A) : word v [49, 71, 73]*x=(word v [49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_111 v H)
lemma reduced_112 : word v [31, 73, 66]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_112 v H)
lemma mul_reduced_112 (x : A) : word v [31, 73, 66]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_112 v H)
lemma reduced_113 : word v [71, 72, 37]=word v [69, 8, 66] + word v [70, 23, 66] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_113 v H)
lemma mul_reduced_113 (x : A) : word v [71, 72, 37]*x=(word v [69, 8, 66]*x) + (word v [70, 23, 66]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_113 v H)
lemma reduced_114 : word v [54, 15, 1, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_114 v H)
lemma mul_reduced_114 (x : A) : word v [54, 15, 1, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_114 v H)
lemma reduced_115 : word v [15, 1, 34, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_115 v H)
lemma mul_reduced_115 (x : A) : word v [15, 1, 34, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_115 v H)
lemma reduced_116 : word v [70, 22, 3, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_116 v H)
lemma mul_reduced_116 (x : A) : word v [70, 22, 3, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_116 v H)
lemma reduced_117 : word v [24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_117 v H)
lemma mul_reduced_117 (x : A) : word v [24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_117 v H)
lemma reduced_118 : word v [40, 60, 4, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_118 v H)
lemma mul_reduced_118 (x : A) : word v [40, 60, 4, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_118 v H)
lemma reduced_119 : word v [60, 4, 56, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_119 v H)
lemma mul_reduced_119 (x : A) : word v [60, 4, 56, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_119 v H)
end UniserialComputations.N6.Presentation.Universal
namespace UniserialComputations.N6.Presentation
variable (k : Type*) [Field k]
lemma reduced_60 : word (a k) [17, 21, 71]=0 := by
  exact Universal.reduced_60 (a k) (relation_zero k)
lemma reduced_61 : word (a k) [63, 21, 71]=0 := by
  exact Universal.reduced_61 (a k) (relation_zero k)
lemma reduced_62 : word (a k) [70, 23, 67]=0 := by
  exact Universal.reduced_62 (a k) (relation_zero k)
lemma reduced_63 : word (a k) [70, 23, 68]=(-word (a k) [70, 22, 3]) := by
  exact Universal.reduced_63 (a k) (relation_zero k)
lemma reduced_64 : word (a k) [37, 25, 61]=0 := by
  exact Universal.reduced_64 (a k) (relation_zero k)
lemma reduced_65 : word (a k) [66, 25, 61]=0 := by
  exact Universal.reduced_65 (a k) (relation_zero k)
lemma reduced_66 : word (a k) [37, 25, 62]=word (a k) [37, 24, 19] := by
  exact Universal.reduced_66 (a k) (relation_zero k)
lemma reduced_67 : word (a k) [66, 25, 62]=word (a k) [66, 24, 19] := by
  exact Universal.reduced_67 (a k) (relation_zero k)
lemma reduced_68 : word (a k) [11, 26, 30]=0 := by
  exact Universal.reduced_68 (a k) (relation_zero k)
lemma reduced_69 : word (a k) [55, 27, 57]=0 := by
  exact Universal.reduced_69 (a k) (relation_zero k)
lemma reduced_70 : word (a k) [38, 28, 14]=word (a k) [37, 24, 18] := by
  exact Universal.reduced_70 (a k) (relation_zero k)
lemma reduced_71 : word (a k) [26, 31, 72]=0 := by
  exact Universal.reduced_71 (a k) (relation_zero k)
lemma reduced_72 : word (a k) [67, 32, 60]=0 := by
  exact Universal.reduced_72 (a k) (relation_zero k)
lemma reduced_73 : word (a k) [1, 34, 65]=0 := by
  exact Universal.reduced_73 (a k) (relation_zero k)
lemma reduced_74 : word (a k) [58, 34, 65]=word (a k) [58, 33, 13] := by
  exact Universal.reduced_74 (a k) (relation_zero k)
lemma reduced_75 : word (a k) [12, 35, 54]=0 := by
  exact Universal.reduced_75 (a k) (relation_zero k)
lemma reduced_76 : word (a k) [61, 35, 54]=0 := by
  exact Universal.reduced_76 (a k) (relation_zero k)
lemma reduced_77 : word (a k) [64, 36, 69]=0 := by
  exact Universal.reduced_77 (a k) (relation_zero k)
lemma reduced_78 : word (a k) [72, 38, 29]=word (a k) [72, 37, 24] := by
  exact Universal.reduced_78 (a k) (relation_zero k)
lemma reduced_79 : word (a k) [3, 40, 61]=0 := by
  exact Universal.reduced_79 (a k) (relation_zero k)
lemma reduced_80 : word (a k) [68, 39, 12]=word (a k) [67, 32, 61] := by
  exact Universal.reduced_80 (a k) (relation_zero k)
lemma reduced_81 : word (a k) [9, 41, 43]=0 := by
  exact Universal.reduced_81 (a k) (relation_zero k)
lemma reduced_82 : word (a k) [52, 42, 46]=word (a k) [52, 41, 43] := by
  exact Universal.reduced_82 (a k) (relation_zero k)
lemma reduced_83 : word (a k) [41, 44, 59]=word (a k) [41, 43, 48] := by
  exact Universal.reduced_83 (a k) (relation_zero k)
lemma reduced_84 : word (a k) [56, 43, 48]=word (a k) [55, 27, 59] := by
  exact Universal.reduced_84 (a k) (relation_zero k)
lemma reduced_85 : word (a k) [42, 45, 6]=word (a k) [41, 43, 47] := by
  exact Universal.reduced_85 (a k) (relation_zero k)
lemma reduced_86 : word (a k) [43, 48, 50]=word (a k) [43, 47, 7] := by
  exact Universal.reduced_86 (a k) (relation_zero k)
lemma reduced_87 : word (a k) [46, 48, 50]=word (a k) [45, 6, 7] := by
  exact Universal.reduced_87 (a k) (relation_zero k)
lemma reduced_88 : word (a k) [13, 49, 70]=0 := by
  exact Universal.reduced_88 (a k) (relation_zero k)
lemma reduced_89 : word (a k) [64, 36, 70]=word (a k) [63, 21, 70] := by
  exact Universal.reduced_89 (a k) (relation_zero k)
lemma reduced_90 : word (a k) [48, 51, 63]=word (a k) [47, 7, 17] := by
  exact Universal.reduced_90 (a k) (relation_zero k)
lemma reduced_91 : word (a k) [59, 50, 17]=(-word (a k) [57, 5, 63]) + word (a k) [58, 34, 63] := by
  exact Universal.reduced_91 (a k) (relation_zero k)
lemma reduced_92 : word (a k) [19, 53, 56]=word (a k) [18, 9, 41] := by
  exact Universal.reduced_92 (a k) (relation_zero k)
lemma reduced_93 : word (a k) [62, 52, 41]=word (a k) [60, 4, 56] + word (a k) [61, 35, 56] := by
  exact Universal.reduced_93 (a k) (relation_zero k)
lemma reduced_94 : word (a k) [4, 56, 44]=word (a k) [4, 54, 16] := by
  exact Universal.reduced_94 (a k) (relation_zero k)
lemma reduced_95 : word (a k) [35, 56, 44]=word (a k) [35, 55, 27] := by
  exact Universal.reduced_95 (a k) (relation_zero k)
lemma reduced_96 : word (a k) [53, 55, 27]=(-word (a k) [53, 54, 16]) + word (a k) [52, 41, 44] := by
  exact Universal.reduced_96 (a k) (relation_zero k)
lemma reduced_97 : word (a k) [16, 57, 5]=word (a k) [15, 1, 34] := by
  exact Universal.reduced_97 (a k) (relation_zero k)
lemma reduced_98 : word (a k) [27, 59, 51]=word (a k) [27, 58, 34] := by
  exact Universal.reduced_98 (a k) (relation_zero k)
lemma reduced_99 : word (a k) [44, 58, 34]=word (a k) [44, 57, 5] + word (a k) [43, 48, 51] := by
  exact Universal.reduced_99 (a k) (relation_zero k)
lemma reduced_100 : word (a k) [25, 60, 4]=word (a k) [24, 19, 53] := by
  exact Universal.reduced_100 (a k) (relation_zero k)
lemma reduced_101 : word (a k) [32, 62, 53]=word (a k) [32, 61, 35] := by
  exact Universal.reduced_101 (a k) (relation_zero k)
lemma reduced_102 : word (a k) [40, 62, 53]=word (a k) [40, 60, 4] + word (a k) [39, 12, 35] := by
  exact Universal.reduced_102 (a k) (relation_zero k)
lemma reduced_103 : word (a k) [5, 63, 21]=0 := by
  exact Universal.reduced_103 (a k) (relation_zero k)
lemma reduced_104 : word (a k) [34, 64, 36]=word (a k) [34, 63, 21] + word (a k) [33, 13, 49] := by
  exact Universal.reduced_104 (a k) (relation_zero k)
lemma reduced_105 : word (a k) [51, 65, 49]=(-word (a k) [50, 17, 21]) + word (a k) [51, 64, 36] := by
  exact Universal.reduced_105 (a k) (relation_zero k)
lemma reduced_106 : word (a k) [8, 68, 40]=(-word (a k) [8, 66, 25]) := by
  exact Universal.reduced_106 (a k) (relation_zero k)
lemma reduced_107 : word (a k) [23, 66, 25]=word (a k) [22, 3, 40] := by
  exact Universal.reduced_107 (a k) (relation_zero k)
lemma reduced_108 : word (a k) [73, 68, 40]=(-word (a k) [72, 37, 25]) + word (a k) [73, 67, 32] := by
  exact Universal.reduced_108 (a k) (relation_zero k)
lemma reduced_109 : word (a k) [21, 70, 23]=(-word (a k) [21, 69, 8]) := by
  exact Universal.reduced_109 (a k) (relation_zero k)
lemma reduced_110 : word (a k) [36, 71, 73]=word (a k) [36, 70, 23] := by
  exact Universal.reduced_110 (a k) (relation_zero k)
lemma reduced_111 : word (a k) [49, 71, 73]=word (a k) [49, 69, 8] := by
  exact Universal.reduced_111 (a k) (relation_zero k)
lemma reduced_112 : word (a k) [31, 73, 66]=0 := by
  exact Universal.reduced_112 (a k) (relation_zero k)
lemma reduced_113 : word (a k) [71, 72, 37]=word (a k) [69, 8, 66] + word (a k) [70, 23, 66] := by
  exact Universal.reduced_113 (a k) (relation_zero k)
lemma reduced_114 : word (a k) [54, 15, 1, 33]=0 := by
  exact Universal.reduced_114 (a k) (relation_zero k)
lemma reduced_115 : word (a k) [15, 1, 34, 64]=0 := by
  exact Universal.reduced_115 (a k) (relation_zero k)
lemma reduced_116 : word (a k) [70, 22, 3, 39]=0 := by
  exact Universal.reduced_116 (a k) (relation_zero k)
lemma reduced_117 : word (a k) [24, 19, 53, 55]=0 := by
  exact Universal.reduced_117 (a k) (relation_zero k)
lemma reduced_118 : word (a k) [40, 60, 4, 55]=0 := by
  exact Universal.reduced_118 (a k) (relation_zero k)
lemma reduced_119 : word (a k) [60, 4, 56, 43]=0 := by
  exact Universal.reduced_119 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
