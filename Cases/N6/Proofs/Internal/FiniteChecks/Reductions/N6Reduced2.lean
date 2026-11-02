import N6Rules29
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma reduced_120 : word v [44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_120 v H)
lemma mul_reduced_120 (x : A) : word v [44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_120 v H)
lemma reduced_121 : word v [15, 1, 34, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_121 v H)
lemma mul_reduced_121 (x : A) : word v [15, 1, 34, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_121 v H)
lemma reduced_122 : word v [44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_122 v H)
lemma mul_reduced_122 (x : A) : word v [44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_122 v H)
lemma reduced_123 : word v [69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_123 v H)
lemma mul_reduced_123 (x : A) : word v [69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_123 v H)
lemma reduced_124 : word v [21, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_124 v H)
lemma mul_reduced_124 (x : A) : word v [21, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_124 v H)
lemma reduced_125 : word v [49, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_125 v H)
lemma mul_reduced_125 (x : A) : word v [49, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_125 v H)
lemma reduced_126 : word v [24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_126 v H)
lemma mul_reduced_126 (x : A) : word v [24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_126 v H)
lemma reduced_127 : word v [28, 14, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_127 v H)
lemma mul_reduced_127 (x : A) : word v [28, 14, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_127 v H)
lemma reduced_128 : word v [4, 54, 16, 58]=word v [4, 54, 15, 1] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_128 v H)
lemma mul_reduced_128 (x : A) : word v [4, 54, 16, 58]*x=(word v [4, 54, 15, 1]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_128 v H)
lemma reduced_129 : word v [53, 54, 16, 58]=word v [53, 54, 15, 1] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_129 v H)
lemma mul_reduced_129 (x : A) : word v [53, 54, 16, 58]*x=(word v [53, 54, 15, 1]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_129 v H)
lemma reduced_130 : word v [4, 54, 16, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_130 v H)
lemma mul_reduced_130 (x : A) : word v [4, 54, 16, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_130 v H)
lemma reduced_131 : word v [53, 54, 16, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_131 v H)
lemma mul_reduced_131 (x : A) : word v [53, 54, 16, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_131 v H)
lemma reduced_132 : word v [6, 7, 17, 20]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_132 v H)
lemma mul_reduced_132 (x : A) : word v [6, 7, 17, 20]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_132 v H)
lemma reduced_133 : word v [47, 7, 17, 20]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_133 v H)
lemma mul_reduced_133 (x : A) : word v [47, 7, 17, 20]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_133 v H)
lemma reduced_134 : word v [58, 34, 63, 20]=word v [57, 5, 63, 20] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_134 v H)
lemma mul_reduced_134 (x : A) : word v [58, 34, 63, 20]*x=(word v [57, 5, 63, 20]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_134 v H)
lemma reduced_135 : word v [29, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_135 v H)
lemma mul_reduced_135 (x : A) : word v [29, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_135 v H)
lemma reduced_136 : word v [37, 24, 19, 52]=word v [37, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_136 v H)
lemma mul_reduced_136 (x : A) : word v [37, 24, 19, 52]*x=(word v [37, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_136 v H)
lemma reduced_137 : word v [66, 24, 19, 52]=word v [66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_137 v H)
lemma mul_reduced_137 (x : A) : word v [66, 24, 19, 52]*x=(word v [66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_137 v H)
lemma reduced_138 : word v [5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_138 v H)
lemma mul_reduced_138 (x : A) : word v [5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_138 v H)
lemma reduced_139 : word v [34, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_139 v H)
lemma mul_reduced_139 (x : A) : word v [34, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_139 v H)
lemma reduced_140 : word v [7, 17, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_140 v H)
lemma mul_reduced_140 (x : A) : word v [7, 17, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_140 v H)
lemma reduced_141 : word v [34, 63, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_141 v H)
lemma mul_reduced_141 (x : A) : word v [34, 63, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_141 v H)
lemma reduced_142 : word v [50, 17, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_142 v H)
lemma mul_reduced_142 (x : A) : word v [50, 17, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_142 v H)
lemma reduced_143 : word v [36, 70, 23, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_143 v H)
lemma mul_reduced_143 (x : A) : word v [36, 70, 23, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_143 v H)
lemma reduced_144 : word v [21, 70, 22, 3]=word v [21, 69, 8, 68] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_144 v H)
lemma mul_reduced_144 (x : A) : word v [21, 70, 22, 3]*x=(word v [21, 69, 8, 68]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_144 v H)
lemma reduced_145 : word v [36, 70, 23, 68]=(-word v [36, 70, 22, 3]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_145 v H)
lemma mul_reduced_145 (x : A) : word v [36, 70, 23, 68]*x=(-(word v [36, 70, 22, 3]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_145 v H)
lemma reduced_146 : word v [8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_146 v H)
lemma mul_reduced_146 (x : A) : word v [8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_146 v H)
lemma reduced_147 : word v [22, 3, 40, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_147 v H)
lemma mul_reduced_147 (x : A) : word v [22, 3, 40, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_147 v H)
lemma reduced_148 : word v [72, 37, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_148 v H)
lemma mul_reduced_148 (x : A) : word v [72, 37, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_148 v H)
lemma reduced_149 : word v [8, 66, 25, 62]=word v [8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_149 v H)
lemma mul_reduced_149 (x : A) : word v [8, 66, 25, 62]*x=(word v [8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_149 v H)
lemma reduced_150 : word v [23, 66, 24, 19]=word v [22, 3, 40, 62] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_150 v H)
lemma mul_reduced_150 (x : A) : word v [23, 66, 24, 19]*x=(word v [22, 3, 40, 62]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_150 v H)
lemma reduced_151 : word v [72, 37, 25, 62]=word v [72, 37, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_151 v H)
lemma mul_reduced_151 (x : A) : word v [72, 37, 25, 62]*x=(word v [72, 37, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_151 v H)
lemma reduced_152 : word v [10, 11, 26, 30]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_152 v H)
lemma mul_reduced_152 (x : A) : word v [10, 11, 26, 30]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_152 v H)
lemma reduced_153 : word v [35, 55, 27, 57]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_153 v H)
lemma mul_reduced_153 (x : A) : word v [35, 55, 27, 57]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_153 v H)
lemma reduced_154 : word v [53, 54, 16, 57]=word v [52, 41, 44, 57] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_154 v H)
lemma mul_reduced_154 (x : A) : word v [53, 54, 16, 57]*x=(word v [52, 41, 44, 57]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_154 v H)
lemma reduced_155 : word v [72, 38, 28, 14]=word v [72, 37, 24, 18] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_155 v H)
lemma mul_reduced_155 (x : A) : word v [72, 38, 28, 14]*x=(word v [72, 37, 24, 18]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_155 v H)
lemma reduced_156 : word v [11, 26, 31, 72]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_156 v H)
lemma mul_reduced_156 (x : A) : word v [11, 26, 31, 72]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_156 v H)
lemma reduced_157 : word v [73, 67, 32, 60]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_157 v H)
lemma mul_reduced_157 (x : A) : word v [73, 67, 32, 60]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_157 v H)
lemma reduced_158 : word v [27, 58, 34, 65]=word v [27, 58, 33, 13] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_158 v H)
lemma mul_reduced_158 (x : A) : word v [27, 58, 34, 65]*x=(word v [27, 58, 33, 13]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_158 v H)
lemma reduced_159 : word v [44, 58, 33, 13]=word v [43, 48, 51, 65] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_159 v H)
lemma mul_reduced_159 (x : A) : word v [44, 58, 33, 13]*x=(word v [43, 48, 51, 65]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_159 v H)
lemma reduced_160 : word v [32, 61, 35, 54]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_160 v H)
lemma mul_reduced_160 (x : A) : word v [32, 61, 35, 54]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_160 v H)
lemma reduced_161 : word v [39, 12, 35, 54]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_161 v H)
lemma mul_reduced_161 (x : A) : word v [39, 12, 35, 54]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_161 v H)
lemma reduced_162 : word v [34, 63, 21, 69]=(-word v [33, 13, 49, 69]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_162 v H)
lemma mul_reduced_162 (x : A) : word v [34, 63, 21, 69]*x=(-(word v [33, 13, 49, 69]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_162 v H)
lemma reduced_163 : word v [51, 64, 36, 69]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_163 v H)
lemma mul_reduced_163 (x : A) : word v [51, 64, 36, 69]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_163 v H)
lemma reduced_164 : word v [71, 72, 38, 29]=word v [69, 8, 66, 24] + word v [70, 23, 66, 24] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_164 v H)
lemma mul_reduced_164 (x : A) : word v [71, 72, 38, 29]*x=(word v [69, 8, 66, 24]*x) + (word v [70, 23, 66, 24]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_164 v H)
lemma reduced_165 : word v [73, 68, 39, 12]=word v [73, 67, 32, 61] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_165 v H)
lemma mul_reduced_165 (x : A) : word v [73, 68, 39, 12]*x=(word v [73, 67, 32, 61]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_165 v H)
lemma reduced_166 : word v [14, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_166 v H)
lemma mul_reduced_166 (x : A) : word v [14, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_166 v H)
lemma reduced_167 : word v [18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_167 v H)
lemma mul_reduced_167 (x : A) : word v [18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_167 v H)
lemma reduced_168 : word v [62, 52, 42, 46]=word v [61, 35, 56, 43] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_168 v H)
lemma mul_reduced_168 (x : A) : word v [62, 52, 42, 46]*x=(word v [61, 35, 56, 43]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_168 v H)
lemma reduced_169 : word v [9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_169 v H)
lemma mul_reduced_169 (x : A) : word v [9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_169 v H)
lemma reduced_170 : word v [35, 56, 43, 48]=word v [35, 55, 27, 59] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_170 v H)
lemma mul_reduced_170 (x : A) : word v [35, 56, 43, 48]*x=(word v [35, 55, 27, 59]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_170 v H)
lemma reduced_171 : word v [52, 41, 44, 59]=word v [52, 41, 43, 48] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_171 v H)
lemma mul_reduced_171 (x : A) : word v [52, 41, 44, 59]*x=(word v [52, 41, 43, 48]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_171 v H)
lemma reduced_172 : word v [52, 42, 45, 6]=word v [52, 41, 43, 47] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_172 v H)
lemma mul_reduced_172 (x : A) : word v [52, 42, 45, 6]*x=(word v [52, 41, 43, 47]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_172 v H)
lemma reduced_173 : word v [41, 43, 48, 50]=word v [41, 43, 47, 7] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_173 v H)
lemma mul_reduced_173 (x : A) : word v [41, 43, 48, 50]*x=(word v [41, 43, 47, 7]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_173 v H)
lemma reduced_174 : word v [56, 43, 47, 7]=word v [55, 27, 59, 50] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_174 v H)
lemma mul_reduced_174 (x : A) : word v [56, 43, 47, 7]*x=(word v [55, 27, 59, 50]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_174 v H)
lemma reduced_175 : word v [33, 13, 49, 70]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_175 v H)
lemma mul_reduced_175 (x : A) : word v [33, 13, 49, 70]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_175 v H)
lemma reduced_176 : word v [51, 64, 36, 70]=word v [50, 17, 21, 70] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_176 v H)
lemma mul_reduced_176 (x : A) : word v [51, 64, 36, 70]*x=(word v [50, 17, 21, 70]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_176 v H)
lemma reduced_177 : word v [27, 59, 50, 17]=word v [27, 58, 34, 63] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_177 v H)
lemma mul_reduced_177 (x : A) : word v [27, 59, 50, 17]*x=(word v [27, 58, 34, 63]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_177 v H)
lemma reduced_178 : word v [43, 48, 51, 63]=word v [43, 47, 7, 17] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_178 v H)
lemma mul_reduced_178 (x : A) : word v [43, 48, 51, 63]*x=(word v [43, 47, 7, 17]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_178 v H)
lemma reduced_179 : word v [46, 48, 51, 63]=word v [45, 6, 7, 17] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_179 v H)
lemma mul_reduced_179 (x : A) : word v [46, 48, 51, 63]*x=(word v [45, 6, 7, 17]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_179 v H)
end UniserialComputations.N6.Presentation.Universal
namespace UniserialComputations.N6.Presentation
variable (k : Type*) [Field k]
lemma reduced_120 : word (a k) [44, 57, 5, 64]=0 := by
  exact Universal.reduced_120 (a k) (relation_zero k)
lemma reduced_121 : word (a k) [15, 1, 34, 65]=0 := by
  exact Universal.reduced_121 (a k) (relation_zero k)
lemma reduced_122 : word (a k) [44, 57, 5, 65]=0 := by
  exact Universal.reduced_122 (a k) (relation_zero k)
lemma reduced_123 : word (a k) [69, 8, 68, 39]=0 := by
  exact Universal.reduced_123 (a k) (relation_zero k)
lemma reduced_124 : word (a k) [21, 69, 8, 67]=0 := by
  exact Universal.reduced_124 (a k) (relation_zero k)
lemma reduced_125 : word (a k) [49, 69, 8, 67]=0 := by
  exact Universal.reduced_125 (a k) (relation_zero k)
lemma reduced_126 : word (a k) [24, 18, 9, 42]=0 := by
  exact Universal.reduced_126 (a k) (relation_zero k)
lemma reduced_127 : word (a k) [28, 14, 9, 42]=0 := by
  exact Universal.reduced_127 (a k) (relation_zero k)
lemma reduced_128 : word (a k) [4, 54, 16, 58]=word (a k) [4, 54, 15, 1] := by
  exact Universal.reduced_128 (a k) (relation_zero k)
lemma reduced_129 : word (a k) [53, 54, 16, 58]=word (a k) [53, 54, 15, 1] := by
  exact Universal.reduced_129 (a k) (relation_zero k)
lemma reduced_130 : word (a k) [4, 54, 16, 59]=0 := by
  exact Universal.reduced_130 (a k) (relation_zero k)
lemma reduced_131 : word (a k) [53, 54, 16, 59]=0 := by
  exact Universal.reduced_131 (a k) (relation_zero k)
lemma reduced_132 : word (a k) [6, 7, 17, 20]=0 := by
  exact Universal.reduced_132 (a k) (relation_zero k)
lemma reduced_133 : word (a k) [47, 7, 17, 20]=0 := by
  exact Universal.reduced_133 (a k) (relation_zero k)
lemma reduced_134 : word (a k) [58, 34, 63, 20]=word (a k) [57, 5, 63, 20] := by
  exact Universal.reduced_134 (a k) (relation_zero k)
lemma reduced_135 : word (a k) [29, 19, 53, 55]=0 := by
  exact Universal.reduced_135 (a k) (relation_zero k)
lemma reduced_136 : word (a k) [37, 24, 19, 52]=word (a k) [37, 24, 18, 9] := by
  exact Universal.reduced_136 (a k) (relation_zero k)
lemma reduced_137 : word (a k) [66, 24, 19, 52]=word (a k) [66, 24, 18, 9] := by
  exact Universal.reduced_137 (a k) (relation_zero k)
lemma reduced_138 : word (a k) [5, 63, 20, 31]=0 := by
  exact Universal.reduced_138 (a k) (relation_zero k)
lemma reduced_139 : word (a k) [34, 63, 20, 31]=0 := by
  exact Universal.reduced_139 (a k) (relation_zero k)
lemma reduced_140 : word (a k) [7, 17, 21, 71]=0 := by
  exact Universal.reduced_140 (a k) (relation_zero k)
lemma reduced_141 : word (a k) [34, 63, 21, 71]=0 := by
  exact Universal.reduced_141 (a k) (relation_zero k)
lemma reduced_142 : word (a k) [50, 17, 21, 71]=0 := by
  exact Universal.reduced_142 (a k) (relation_zero k)
lemma reduced_143 : word (a k) [36, 70, 23, 67]=0 := by
  exact Universal.reduced_143 (a k) (relation_zero k)
lemma reduced_144 : word (a k) [21, 70, 22, 3]=word (a k) [21, 69, 8, 68] := by
  exact Universal.reduced_144 (a k) (relation_zero k)
lemma reduced_145 : word (a k) [36, 70, 23, 68]=(-word (a k) [36, 70, 22, 3]) := by
  exact Universal.reduced_145 (a k) (relation_zero k)
lemma reduced_146 : word (a k) [8, 66, 25, 61]=0 := by
  exact Universal.reduced_146 (a k) (relation_zero k)
lemma reduced_147 : word (a k) [22, 3, 40, 61]=0 := by
  exact Universal.reduced_147 (a k) (relation_zero k)
lemma reduced_148 : word (a k) [72, 37, 25, 61]=0 := by
  exact Universal.reduced_148 (a k) (relation_zero k)
lemma reduced_149 : word (a k) [8, 66, 25, 62]=word (a k) [8, 66, 24, 19] := by
  exact Universal.reduced_149 (a k) (relation_zero k)
lemma reduced_150 : word (a k) [23, 66, 24, 19]=word (a k) [22, 3, 40, 62] := by
  exact Universal.reduced_150 (a k) (relation_zero k)
lemma reduced_151 : word (a k) [72, 37, 25, 62]=word (a k) [72, 37, 24, 19] := by
  exact Universal.reduced_151 (a k) (relation_zero k)
lemma reduced_152 : word (a k) [10, 11, 26, 30]=0 := by
  exact Universal.reduced_152 (a k) (relation_zero k)
lemma reduced_153 : word (a k) [35, 55, 27, 57]=0 := by
  exact Universal.reduced_153 (a k) (relation_zero k)
lemma reduced_154 : word (a k) [53, 54, 16, 57]=word (a k) [52, 41, 44, 57] := by
  exact Universal.reduced_154 (a k) (relation_zero k)
lemma reduced_155 : word (a k) [72, 38, 28, 14]=word (a k) [72, 37, 24, 18] := by
  exact Universal.reduced_155 (a k) (relation_zero k)
lemma reduced_156 : word (a k) [11, 26, 31, 72]=0 := by
  exact Universal.reduced_156 (a k) (relation_zero k)
lemma reduced_157 : word (a k) [73, 67, 32, 60]=0 := by
  exact Universal.reduced_157 (a k) (relation_zero k)
lemma reduced_158 : word (a k) [27, 58, 34, 65]=word (a k) [27, 58, 33, 13] := by
  exact Universal.reduced_158 (a k) (relation_zero k)
lemma reduced_159 : word (a k) [44, 58, 33, 13]=word (a k) [43, 48, 51, 65] := by
  exact Universal.reduced_159 (a k) (relation_zero k)
lemma reduced_160 : word (a k) [32, 61, 35, 54]=0 := by
  exact Universal.reduced_160 (a k) (relation_zero k)
lemma reduced_161 : word (a k) [39, 12, 35, 54]=0 := by
  exact Universal.reduced_161 (a k) (relation_zero k)
lemma reduced_162 : word (a k) [34, 63, 21, 69]=(-word (a k) [33, 13, 49, 69]) := by
  exact Universal.reduced_162 (a k) (relation_zero k)
lemma reduced_163 : word (a k) [51, 64, 36, 69]=0 := by
  exact Universal.reduced_163 (a k) (relation_zero k)
lemma reduced_164 : word (a k) [71, 72, 38, 29]=word (a k) [69, 8, 66, 24] + word (a k) [70, 23, 66, 24] := by
  exact Universal.reduced_164 (a k) (relation_zero k)
lemma reduced_165 : word (a k) [73, 68, 39, 12]=word (a k) [73, 67, 32, 61] := by
  exact Universal.reduced_165 (a k) (relation_zero k)
lemma reduced_166 : word (a k) [14, 9, 41, 43]=0 := by
  exact Universal.reduced_166 (a k) (relation_zero k)
lemma reduced_167 : word (a k) [18, 9, 41, 43]=0 := by
  exact Universal.reduced_167 (a k) (relation_zero k)
lemma reduced_168 : word (a k) [62, 52, 42, 46]=word (a k) [61, 35, 56, 43] := by
  exact Universal.reduced_168 (a k) (relation_zero k)
lemma reduced_169 : word (a k) [9, 41, 44, 59]=0 := by
  exact Universal.reduced_169 (a k) (relation_zero k)
lemma reduced_170 : word (a k) [35, 56, 43, 48]=word (a k) [35, 55, 27, 59] := by
  exact Universal.reduced_170 (a k) (relation_zero k)
lemma reduced_171 : word (a k) [52, 41, 44, 59]=word (a k) [52, 41, 43, 48] := by
  exact Universal.reduced_171 (a k) (relation_zero k)
lemma reduced_172 : word (a k) [52, 42, 45, 6]=word (a k) [52, 41, 43, 47] := by
  exact Universal.reduced_172 (a k) (relation_zero k)
lemma reduced_173 : word (a k) [41, 43, 48, 50]=word (a k) [41, 43, 47, 7] := by
  exact Universal.reduced_173 (a k) (relation_zero k)
lemma reduced_174 : word (a k) [56, 43, 47, 7]=word (a k) [55, 27, 59, 50] := by
  exact Universal.reduced_174 (a k) (relation_zero k)
lemma reduced_175 : word (a k) [33, 13, 49, 70]=0 := by
  exact Universal.reduced_175 (a k) (relation_zero k)
lemma reduced_176 : word (a k) [51, 64, 36, 70]=word (a k) [50, 17, 21, 70] := by
  exact Universal.reduced_176 (a k) (relation_zero k)
lemma reduced_177 : word (a k) [27, 59, 50, 17]=word (a k) [27, 58, 34, 63] := by
  exact Universal.reduced_177 (a k) (relation_zero k)
lemma reduced_178 : word (a k) [43, 48, 51, 63]=word (a k) [43, 47, 7, 17] := by
  exact Universal.reduced_178 (a k) (relation_zero k)
lemma reduced_179 : word (a k) [46, 48, 51, 63]=word (a k) [45, 6, 7, 17] := by
  exact Universal.reduced_179 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
