import N6Rules29
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma reduced_180 : word v [24, 19, 53, 56]=word v [24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_180 v H)
lemma mul_reduced_180 (x : A) : word v [24, 19, 53, 56]*x=(word v [24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_180 v H)
lemma reduced_181 : word v [29, 19, 53, 56]=word v [28, 14, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_181 v H)
lemma mul_reduced_181 (x : A) : word v [29, 19, 53, 56]*x=(word v [28, 14, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_181 v H)
lemma reduced_182 : word v [32, 62, 52, 41]=word v [32, 61, 35, 56] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_182 v H)
lemma mul_reduced_182 (x : A) : word v [32, 62, 52, 41]*x=(word v [32, 61, 35, 56]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_182 v H)
lemma reduced_183 : word v [40, 62, 52, 41]=word v [40, 60, 4, 56] + word v [39, 12, 35, 56] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_183 v H)
lemma mul_reduced_183 (x : A) : word v [40, 62, 52, 41]*x=(word v [40, 60, 4, 56]*x) + (word v [39, 12, 35, 56]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_183 v H)
lemma reduced_184 : word v [12, 35, 56, 44]=word v [12, 35, 55, 27] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_184 v H)
lemma mul_reduced_184 (x : A) : word v [12, 35, 56, 44]*x=(word v [12, 35, 55, 27]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_184 v H)
lemma reduced_185 : word v [19, 53, 54, 16]=word v [18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_185 v H)
lemma mul_reduced_185 (x : A) : word v [19, 53, 54, 16]*x=(word v [18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_185 v H)
lemma reduced_186 : word v [60, 4, 56, 44]=word v [60, 4, 54, 16] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_186 v H)
lemma mul_reduced_186 (x : A) : word v [60, 4, 56, 44]*x=(word v [60, 4, 54, 16]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_186 v H)
lemma reduced_187 : word v [61, 35, 56, 44]=word v [61, 35, 55, 27] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_187 v H)
lemma mul_reduced_187 (x : A) : word v [61, 35, 56, 44]*x=(word v [61, 35, 55, 27]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_187 v H)
lemma reduced_188 : word v [41, 44, 58, 34]=word v [41, 44, 57, 5] + word v [41, 43, 48, 51] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_188 v H)
lemma mul_reduced_188 (x : A) : word v [41, 44, 58, 34]*x=(word v [41, 44, 57, 5]*x) + (word v [41, 43, 48, 51]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_188 v H)
lemma reduced_189 : word v [54, 16, 57, 5]=word v [54, 15, 1, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_189 v H)
lemma mul_reduced_189 (x : A) : word v [54, 16, 57, 5]*x=(word v [54, 15, 1, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_189 v H)
lemma reduced_190 : word v [55, 27, 59, 51]=word v [55, 27, 58, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_190 v H)
lemma mul_reduced_190 (x : A) : word v [55, 27, 59, 51]*x=(word v [55, 27, 58, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_190 v H)
lemma reduced_191 : word v [3, 40, 62, 53]=word v [3, 40, 60, 4] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_191 v H)
lemma mul_reduced_191 (x : A) : word v [3, 40, 62, 53]*x=(word v [3, 40, 60, 4]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_191 v H)
lemma reduced_192 : word v [37, 25, 60, 4]=word v [37, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_192 v H)
lemma mul_reduced_192 (x : A) : word v [37, 25, 60, 4]*x=(word v [37, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_192 v H)
lemma reduced_193 : word v [66, 25, 60, 4]=word v [66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_193 v H)
lemma mul_reduced_193 (x : A) : word v [66, 25, 60, 4]*x=(word v [66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_193 v H)
lemma reduced_194 : word v [67, 32, 62, 53]=word v [67, 32, 61, 35] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_194 v H)
lemma mul_reduced_194 (x : A) : word v [67, 32, 62, 53]*x=(word v [67, 32, 61, 35]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_194 v H)
lemma reduced_195 : word v [1, 34, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_195 v H)
lemma mul_reduced_195 (x : A) : word v [1, 34, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_195 v H)
lemma reduced_196 : word v [48, 51, 65, 49]=(-word v [47, 7, 17, 21]) + word v [48, 51, 64, 36] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_196 v H)
lemma mul_reduced_196 (x : A) : word v [48, 51, 65, 49]*x=(-(word v [47, 7, 17, 21]*x)) + (word v [48, 51, 64, 36]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_196 v H)
lemma reduced_197 : word v [57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_197 v H)
lemma mul_reduced_197 (x : A) : word v [57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_197 v H)
lemma reduced_198 : word v [58, 34, 64, 36]=word v [58, 34, 63, 21] + word v [58, 33, 13, 49] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_198 v H)
lemma mul_reduced_198 (x : A) : word v [58, 34, 64, 36]*x=(word v [58, 34, 63, 21]*x) + (word v [58, 33, 13, 49]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_198 v H)
lemma reduced_199 : word v [31, 73, 68, 40]=word v [31, 73, 67, 32] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_199 v H)
lemma mul_reduced_199 (x : A) : word v [31, 73, 68, 40]*x=(word v [31, 73, 67, 32]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_199 v H)
lemma reduced_200 : word v [69, 8, 68, 40]=(-word v [69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_200 v H)
lemma mul_reduced_200 (x : A) : word v [69, 8, 68, 40]*x=(-(word v [69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_200 v H)
lemma reduced_201 : word v [70, 23, 66, 25]=word v [70, 22, 3, 40] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_201 v H)
lemma mul_reduced_201 (x : A) : word v [70, 23, 66, 25]*x=(word v [70, 22, 3, 40]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_201 v H)
lemma reduced_202 : word v [13, 49, 71, 73]=word v [13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_202 v H)
lemma mul_reduced_202 (x : A) : word v [13, 49, 71, 73]*x=(word v [13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_202 v H)
lemma reduced_203 : word v [17, 21, 70, 23]=(-word v [17, 21, 69, 8]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_203 v H)
lemma mul_reduced_203 (x : A) : word v [17, 21, 70, 23]*x=(-(word v [17, 21, 69, 8]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_203 v H)
lemma reduced_204 : word v [63, 21, 70, 23]=(-word v [63, 21, 69, 8]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_204 v H)
lemma mul_reduced_204 (x : A) : word v [63, 21, 70, 23]*x=(-(word v [63, 21, 69, 8]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_204 v H)
lemma reduced_205 : word v [64, 36, 71, 73]=(-word v [63, 21, 69, 8]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_205 v H)
lemma mul_reduced_205 (x : A) : word v [64, 36, 71, 73]*x=(-(word v [63, 21, 69, 8]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_205 v H)
lemma reduced_206 : word v [26, 31, 73, 66]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_206 v H)
lemma mul_reduced_206 (x : A) : word v [26, 31, 73, 66]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_206 v H)
lemma reduced_207 : word v [36, 71, 72, 37]=word v [36, 70, 23, 66] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_207 v H)
lemma mul_reduced_207 (x : A) : word v [36, 71, 72, 37]*x=(word v [36, 70, 23, 66]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_207 v H)
lemma reduced_208 : word v [49, 71, 72, 37]=word v [49, 69, 8, 66] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_208 v H)
lemma mul_reduced_208 (x : A) : word v [49, 71, 72, 37]*x=(word v [49, 69, 8, 66]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_208 v H)
lemma reduced_209 : word v [4, 54, 15, 1, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_209 v H)
lemma mul_reduced_209 (x : A) : word v [4, 54, 15, 1, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_209 v H)
lemma reduced_210 : word v [53, 54, 15, 1, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_210 v H)
lemma mul_reduced_210 (x : A) : word v [53, 54, 15, 1, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_210 v H)
lemma reduced_211 : word v [54, 15, 1, 34, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_211 v H)
lemma mul_reduced_211 (x : A) : word v [54, 15, 1, 34, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_211 v H)
lemma reduced_212 : word v [21, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_212 v H)
lemma mul_reduced_212 (x : A) : word v [21, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_212 v H)
lemma reduced_213 : word v [36, 70, 22, 3, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_213 v H)
lemma mul_reduced_213 (x : A) : word v [36, 70, 22, 3, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_213 v H)
lemma reduced_214 : word v [3, 40, 62, 52, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_214 v H)
lemma mul_reduced_214 (x : A) : word v [3, 40, 62, 52, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_214 v H)
lemma reduced_215 : word v [3, 40, 60, 4, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_215 v H)
lemma mul_reduced_215 (x : A) : word v [3, 40, 60, 4, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_215 v H)
lemma reduced_216 : word v [37, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_216 v H)
lemma mul_reduced_216 (x : A) : word v [37, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_216 v H)
lemma reduced_217 : word v [66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_217 v H)
lemma mul_reduced_217 (x : A) : word v [66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_217 v H)
lemma reduced_218 : word v [24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_218 v H)
lemma mul_reduced_218 (x : A) : word v [24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_218 v H)
lemma reduced_219 : word v [40, 60, 4, 56, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_219 v H)
lemma mul_reduced_219 (x : A) : word v [40, 60, 4, 56, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_219 v H)
lemma reduced_220 : word v [41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_220 v H)
lemma mul_reduced_220 (x : A) : word v [41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_220 v H)
lemma reduced_221 : word v [41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_221 v H)
lemma mul_reduced_221 (x : A) : word v [41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_221 v H)
lemma reduced_222 : word v [54, 15, 1, 34, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_222 v H)
lemma mul_reduced_222 (x : A) : word v [54, 15, 1, 34, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_222 v H)
lemma reduced_223 : word v [49, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_223 v H)
lemma mul_reduced_223 (x : A) : word v [49, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_223 v H)
lemma reduced_224 : word v [13, 49, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_224 v H)
lemma mul_reduced_224 (x : A) : word v [13, 49, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_224 v H)
lemma reduced_225 : word v [17, 21, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_225 v H)
lemma mul_reduced_225 (x : A) : word v [17, 21, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_225 v H)
lemma reduced_226 : word v [63, 21, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_226 v H)
lemma mul_reduced_226 (x : A) : word v [63, 21, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_226 v H)
lemma reduced_227 : word v [9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_227 v H)
lemma mul_reduced_227 (x : A) : word v [9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_227 v H)
lemma reduced_228 : word v [37, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_228 v H)
lemma mul_reduced_228 (x : A) : word v [37, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_228 v H)
lemma reduced_229 : word v [66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_229 v H)
lemma mul_reduced_229 (x : A) : word v [66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_229 v H)
lemma reduced_230 : word v [19, 53, 54, 15, 1]=word v [18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_230 v H)
lemma mul_reduced_230 (x : A) : word v [19, 53, 54, 15, 1]*x=(word v [18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_230 v H)
lemma reduced_231 : word v [60, 4, 54, 16, 58]=word v [60, 4, 54, 15, 1] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_231 v H)
lemma mul_reduced_231 (x : A) : word v [60, 4, 54, 16, 58]*x=(word v [60, 4, 54, 15, 1]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_231 v H)
lemma reduced_232 : word v [18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_232 v H)
lemma mul_reduced_232 (x : A) : word v [18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_232 v H)
lemma reduced_233 : word v [60, 4, 54, 16, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_233 v H)
lemma mul_reduced_233 (x : A) : word v [60, 4, 54, 16, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_233 v H)
lemma reduced_234 : word v [27, 58, 34, 63, 20]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_234 v H)
lemma mul_reduced_234 (x : A) : word v [27, 58, 34, 63, 20]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_234 v H)
lemma reduced_235 : word v [43, 47, 7, 17, 20]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_235 v H)
lemma mul_reduced_235 (x : A) : word v [43, 47, 7, 17, 20]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_235 v H)
lemma reduced_236 : word v [45, 6, 7, 17, 20]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_236 v H)
lemma mul_reduced_236 (x : A) : word v [45, 6, 7, 17, 20]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_236 v H)
lemma reduced_237 : word v [8, 66, 24, 19, 52]=word v [8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_237 v H)
lemma mul_reduced_237 (x : A) : word v [8, 66, 24, 19, 52]*x=(word v [8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_237 v H)
lemma reduced_238 : word v [23, 66, 24, 18, 9]=word v [22, 3, 40, 62, 52] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_238 v H)
lemma mul_reduced_238 (x : A) : word v [23, 66, 24, 18, 9]*x=(word v [22, 3, 40, 62, 52]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_238 v H)
lemma reduced_239 : word v [72, 37, 24, 19, 52]=word v [72, 37, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_239 v H)
lemma mul_reduced_239 (x : A) : word v [72, 37, 24, 19, 52]*x=(word v [72, 37, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_239 v H)
end UniserialComputations.N6.Presentation.Universal
namespace UniserialComputations.N6.Presentation
variable (k : Type*) [Field k]
lemma reduced_180 : word (a k) [24, 19, 53, 56]=word (a k) [24, 18, 9, 41] := by
  exact Universal.reduced_180 (a k) (relation_zero k)
lemma reduced_181 : word (a k) [29, 19, 53, 56]=word (a k) [28, 14, 9, 41] := by
  exact Universal.reduced_181 (a k) (relation_zero k)
lemma reduced_182 : word (a k) [32, 62, 52, 41]=word (a k) [32, 61, 35, 56] := by
  exact Universal.reduced_182 (a k) (relation_zero k)
lemma reduced_183 : word (a k) [40, 62, 52, 41]=word (a k) [40, 60, 4, 56] + word (a k) [39, 12, 35, 56] := by
  exact Universal.reduced_183 (a k) (relation_zero k)
lemma reduced_184 : word (a k) [12, 35, 56, 44]=word (a k) [12, 35, 55, 27] := by
  exact Universal.reduced_184 (a k) (relation_zero k)
lemma reduced_185 : word (a k) [19, 53, 54, 16]=word (a k) [18, 9, 41, 44] := by
  exact Universal.reduced_185 (a k) (relation_zero k)
lemma reduced_186 : word (a k) [60, 4, 56, 44]=word (a k) [60, 4, 54, 16] := by
  exact Universal.reduced_186 (a k) (relation_zero k)
lemma reduced_187 : word (a k) [61, 35, 56, 44]=word (a k) [61, 35, 55, 27] := by
  exact Universal.reduced_187 (a k) (relation_zero k)
lemma reduced_188 : word (a k) [41, 44, 58, 34]=word (a k) [41, 44, 57, 5] + word (a k) [41, 43, 48, 51] := by
  exact Universal.reduced_188 (a k) (relation_zero k)
lemma reduced_189 : word (a k) [54, 16, 57, 5]=word (a k) [54, 15, 1, 34] := by
  exact Universal.reduced_189 (a k) (relation_zero k)
lemma reduced_190 : word (a k) [55, 27, 59, 51]=word (a k) [55, 27, 58, 34] := by
  exact Universal.reduced_190 (a k) (relation_zero k)
lemma reduced_191 : word (a k) [3, 40, 62, 53]=word (a k) [3, 40, 60, 4] := by
  exact Universal.reduced_191 (a k) (relation_zero k)
lemma reduced_192 : word (a k) [37, 25, 60, 4]=word (a k) [37, 24, 19, 53] := by
  exact Universal.reduced_192 (a k) (relation_zero k)
lemma reduced_193 : word (a k) [66, 25, 60, 4]=word (a k) [66, 24, 19, 53] := by
  exact Universal.reduced_193 (a k) (relation_zero k)
lemma reduced_194 : word (a k) [67, 32, 62, 53]=word (a k) [67, 32, 61, 35] := by
  exact Universal.reduced_194 (a k) (relation_zero k)
lemma reduced_195 : word (a k) [1, 34, 63, 21]=0 := by
  exact Universal.reduced_195 (a k) (relation_zero k)
lemma reduced_196 : word (a k) [48, 51, 65, 49]=(-word (a k) [47, 7, 17, 21]) + word (a k) [48, 51, 64, 36] := by
  exact Universal.reduced_196 (a k) (relation_zero k)
lemma reduced_197 : word (a k) [57, 5, 63, 21]=0 := by
  exact Universal.reduced_197 (a k) (relation_zero k)
lemma reduced_198 : word (a k) [58, 34, 64, 36]=word (a k) [58, 34, 63, 21] + word (a k) [58, 33, 13, 49] := by
  exact Universal.reduced_198 (a k) (relation_zero k)
lemma reduced_199 : word (a k) [31, 73, 68, 40]=word (a k) [31, 73, 67, 32] := by
  exact Universal.reduced_199 (a k) (relation_zero k)
lemma reduced_200 : word (a k) [69, 8, 68, 40]=(-word (a k) [69, 8, 66, 25]) := by
  exact Universal.reduced_200 (a k) (relation_zero k)
lemma reduced_201 : word (a k) [70, 23, 66, 25]=word (a k) [70, 22, 3, 40] := by
  exact Universal.reduced_201 (a k) (relation_zero k)
lemma reduced_202 : word (a k) [13, 49, 71, 73]=word (a k) [13, 49, 69, 8] := by
  exact Universal.reduced_202 (a k) (relation_zero k)
lemma reduced_203 : word (a k) [17, 21, 70, 23]=(-word (a k) [17, 21, 69, 8]) := by
  exact Universal.reduced_203 (a k) (relation_zero k)
lemma reduced_204 : word (a k) [63, 21, 70, 23]=(-word (a k) [63, 21, 69, 8]) := by
  exact Universal.reduced_204 (a k) (relation_zero k)
lemma reduced_205 : word (a k) [64, 36, 71, 73]=(-word (a k) [63, 21, 69, 8]) := by
  exact Universal.reduced_205 (a k) (relation_zero k)
lemma reduced_206 : word (a k) [26, 31, 73, 66]=0 := by
  exact Universal.reduced_206 (a k) (relation_zero k)
lemma reduced_207 : word (a k) [36, 71, 72, 37]=word (a k) [36, 70, 23, 66] := by
  exact Universal.reduced_207 (a k) (relation_zero k)
lemma reduced_208 : word (a k) [49, 71, 72, 37]=word (a k) [49, 69, 8, 66] := by
  exact Universal.reduced_208 (a k) (relation_zero k)
lemma reduced_209 : word (a k) [4, 54, 15, 1, 33]=0 := by
  exact Universal.reduced_209 (a k) (relation_zero k)
lemma reduced_210 : word (a k) [53, 54, 15, 1, 33]=0 := by
  exact Universal.reduced_210 (a k) (relation_zero k)
lemma reduced_211 : word (a k) [54, 15, 1, 34, 64]=0 := by
  exact Universal.reduced_211 (a k) (relation_zero k)
lemma reduced_212 : word (a k) [21, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_212 (a k) (relation_zero k)
lemma reduced_213 : word (a k) [36, 70, 22, 3, 39]=0 := by
  exact Universal.reduced_213 (a k) (relation_zero k)
lemma reduced_214 : word (a k) [3, 40, 62, 52, 42]=0 := by
  exact Universal.reduced_214 (a k) (relation_zero k)
lemma reduced_215 : word (a k) [3, 40, 60, 4, 55]=0 := by
  exact Universal.reduced_215 (a k) (relation_zero k)
lemma reduced_216 : word (a k) [37, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_216 (a k) (relation_zero k)
lemma reduced_217 : word (a k) [66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_217 (a k) (relation_zero k)
lemma reduced_218 : word (a k) [24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_218 (a k) (relation_zero k)
lemma reduced_219 : word (a k) [40, 60, 4, 56, 43]=0 := by
  exact Universal.reduced_219 (a k) (relation_zero k)
lemma reduced_220 : word (a k) [41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_220 (a k) (relation_zero k)
lemma reduced_221 : word (a k) [41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_221 (a k) (relation_zero k)
lemma reduced_222 : word (a k) [54, 15, 1, 34, 65]=0 := by
  exact Universal.reduced_222 (a k) (relation_zero k)
lemma reduced_223 : word (a k) [49, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_223 (a k) (relation_zero k)
lemma reduced_224 : word (a k) [13, 49, 69, 8, 67]=0 := by
  exact Universal.reduced_224 (a k) (relation_zero k)
lemma reduced_225 : word (a k) [17, 21, 69, 8, 67]=0 := by
  exact Universal.reduced_225 (a k) (relation_zero k)
lemma reduced_226 : word (a k) [63, 21, 69, 8, 67]=0 := by
  exact Universal.reduced_226 (a k) (relation_zero k)
lemma reduced_227 : word (a k) [9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_227 (a k) (relation_zero k)
lemma reduced_228 : word (a k) [37, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_228 (a k) (relation_zero k)
lemma reduced_229 : word (a k) [66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_229 (a k) (relation_zero k)
lemma reduced_230 : word (a k) [19, 53, 54, 15, 1]=word (a k) [18, 9, 41, 44, 58] := by
  exact Universal.reduced_230 (a k) (relation_zero k)
lemma reduced_231 : word (a k) [60, 4, 54, 16, 58]=word (a k) [60, 4, 54, 15, 1] := by
  exact Universal.reduced_231 (a k) (relation_zero k)
lemma reduced_232 : word (a k) [18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_232 (a k) (relation_zero k)
lemma reduced_233 : word (a k) [60, 4, 54, 16, 59]=0 := by
  exact Universal.reduced_233 (a k) (relation_zero k)
lemma reduced_234 : word (a k) [27, 58, 34, 63, 20]=0 := by
  exact Universal.reduced_234 (a k) (relation_zero k)
lemma reduced_235 : word (a k) [43, 47, 7, 17, 20]=0 := by
  exact Universal.reduced_235 (a k) (relation_zero k)
lemma reduced_236 : word (a k) [45, 6, 7, 17, 20]=0 := by
  exact Universal.reduced_236 (a k) (relation_zero k)
lemma reduced_237 : word (a k) [8, 66, 24, 19, 52]=word (a k) [8, 66, 24, 18, 9] := by
  exact Universal.reduced_237 (a k) (relation_zero k)
lemma reduced_238 : word (a k) [23, 66, 24, 18, 9]=word (a k) [22, 3, 40, 62, 52] := by
  exact Universal.reduced_238 (a k) (relation_zero k)
lemma reduced_239 : word (a k) [72, 37, 24, 19, 52]=word (a k) [72, 37, 24, 18, 9] := by
  exact Universal.reduced_239 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
