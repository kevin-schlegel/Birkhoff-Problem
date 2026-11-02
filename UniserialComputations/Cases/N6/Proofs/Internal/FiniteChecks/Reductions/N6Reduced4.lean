import N6Rules29
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma reduced_240 : word v [1, 34, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_240 v H)
lemma mul_reduced_240 (x : A) : word v [1, 34, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_240 v H)
lemma reduced_241 : word v [57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_241 v H)
lemma mul_reduced_241 (x : A) : word v [57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_241 v H)
lemma reduced_242 : word v [6, 7, 17, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_242 v H)
lemma mul_reduced_242 (x : A) : word v [6, 7, 17, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_242 v H)
lemma reduced_243 : word v [47, 7, 17, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_243 v H)
lemma mul_reduced_243 (x : A) : word v [47, 7, 17, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_243 v H)
lemma reduced_244 : word v [58, 34, 63, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_244 v H)
lemma mul_reduced_244 (x : A) : word v [58, 34, 63, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_244 v H)
lemma reduced_245 : word v [17, 21, 70, 22, 3]=word v [17, 21, 69, 8, 68] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_245 v H)
lemma mul_reduced_245 (x : A) : word v [17, 21, 70, 22, 3]*x=(word v [17, 21, 69, 8, 68]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_245 v H)
lemma reduced_246 : word v [63, 21, 70, 22, 3]=word v [63, 21, 69, 8, 68] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_246 v H)
lemma mul_reduced_246 (x : A) : word v [63, 21, 70, 22, 3]*x=(word v [63, 21, 69, 8, 68]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_246 v H)
lemma reduced_247 : word v [69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_247 v H)
lemma mul_reduced_247 (x : A) : word v [69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_247 v H)
lemma reduced_248 : word v [70, 22, 3, 40, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_248 v H)
lemma mul_reduced_248 (x : A) : word v [70, 22, 3, 40, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_248 v H)
lemma reduced_249 : word v [69, 8, 66, 25, 62]=word v [69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_249 v H)
lemma mul_reduced_249 (x : A) : word v [69, 8, 66, 25, 62]*x=(word v [69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_249 v H)
lemma reduced_250 : word v [70, 23, 66, 24, 19]=word v [70, 22, 3, 40, 62] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_250 v H)
lemma mul_reduced_250 (x : A) : word v [70, 23, 66, 24, 19]*x=(word v [70, 22, 3, 40, 62]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_250 v H)
lemma reduced_251 : word v [74, 10, 11, 26, 30]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_251 v H)
lemma mul_reduced_251 (x : A) : word v [74, 10, 11, 26, 30]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_251 v H)
lemma reduced_252 : word v [12, 35, 55, 27, 57]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_252 v H)
lemma mul_reduced_252 (x : A) : word v [12, 35, 55, 27, 57]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_252 v H)
lemma reduced_253 : word v [61, 35, 55, 27, 57]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_253 v H)
lemma mul_reduced_253 (x : A) : word v [61, 35, 55, 27, 57]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_253 v H)
lemma reduced_254 : word v [71, 72, 38, 28, 14]=word v [69, 8, 66, 24, 18] + word v [70, 23, 66, 24, 18] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_254 v H)
lemma mul_reduced_254 (x : A) : word v [71, 72, 38, 28, 14]*x=(word v [69, 8, 66, 24, 18]*x) + (word v [70, 23, 66, 24, 18]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_254 v H)
lemma reduced_255 : word v [10, 11, 26, 31, 72]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_255 v H)
lemma mul_reduced_255 (x : A) : word v [10, 11, 26, 31, 72]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_255 v H)
lemma reduced_256 : word v [31, 73, 67, 32, 60]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_256 v H)
lemma mul_reduced_256 (x : A) : word v [31, 73, 67, 32, 60]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_256 v H)
lemma reduced_257 : word v [41, 44, 58, 33, 13]=word v [41, 43, 48, 51, 65] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_257 v H)
lemma mul_reduced_257 (x : A) : word v [41, 44, 58, 33, 13]*x=(word v [41, 43, 48, 51, 65]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_257 v H)
lemma reduced_258 : word v [55, 27, 58, 34, 65]=word v [55, 27, 58, 33, 13] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_258 v H)
lemma mul_reduced_258 (x : A) : word v [55, 27, 58, 34, 65]*x=(word v [55, 27, 58, 33, 13]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_258 v H)
lemma reduced_259 : word v [67, 32, 61, 35, 54]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_259 v H)
lemma mul_reduced_259 (x : A) : word v [67, 32, 61, 35, 54]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_259 v H)
lemma reduced_260 : word v [48, 51, 64, 36, 69]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_260 v H)
lemma mul_reduced_260 (x : A) : word v [48, 51, 64, 36, 69]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_260 v H)
lemma reduced_261 : word v [58, 34, 63, 21, 69]=(-word v [58, 33, 13, 49, 69]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_261 v H)
lemma mul_reduced_261 (x : A) : word v [58, 34, 63, 21, 69]*x=(-(word v [58, 33, 13, 49, 69]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_261 v H)
lemma reduced_262 : word v [36, 71, 72, 38, 29]=word v [36, 70, 23, 66, 24] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_262 v H)
lemma mul_reduced_262 (x : A) : word v [36, 71, 72, 38, 29]*x=(word v [36, 70, 23, 66, 24]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_262 v H)
lemma reduced_263 : word v [49, 71, 72, 38, 29]=word v [49, 69, 8, 66, 24] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_263 v H)
lemma mul_reduced_263 (x : A) : word v [49, 71, 72, 38, 29]*x=(word v [49, 69, 8, 66, 24]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_263 v H)
lemma reduced_264 : word v [31, 73, 68, 39, 12]=word v [31, 73, 67, 32, 61] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_264 v H)
lemma mul_reduced_264 (x : A) : word v [31, 73, 68, 39, 12]*x=(word v [31, 73, 67, 32, 61]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_264 v H)
lemma reduced_265 : word v [28, 14, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_265 v H)
lemma mul_reduced_265 (x : A) : word v [28, 14, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_265 v H)
lemma reduced_266 : word v [32, 62, 52, 42, 46]=word v [32, 61, 35, 56, 43] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_266 v H)
lemma mul_reduced_266 (x : A) : word v [32, 62, 52, 42, 46]*x=(word v [32, 61, 35, 56, 43]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_266 v H)
lemma reduced_267 : word v [40, 62, 52, 42, 46]=word v [39, 12, 35, 56, 43] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_267 v H)
lemma mul_reduced_267 (x : A) : word v [40, 62, 52, 42, 46]*x=(word v [39, 12, 35, 56, 43]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_267 v H)
lemma reduced_268 : word v [12, 35, 56, 43, 48]=word v [12, 35, 55, 27, 59] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_268 v H)
lemma mul_reduced_268 (x : A) : word v [12, 35, 56, 43, 48]*x=(word v [12, 35, 55, 27, 59]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_268 v H)
lemma reduced_269 : word v [14, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_269 v H)
lemma mul_reduced_269 (x : A) : word v [14, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_269 v H)
lemma reduced_270 : word v [61, 35, 56, 43, 48]=word v [61, 35, 55, 27, 59] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_270 v H)
lemma mul_reduced_270 (x : A) : word v [61, 35, 56, 43, 48]*x=(word v [61, 35, 55, 27, 59]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_270 v H)
lemma reduced_271 : word v [62, 52, 42, 45, 6]=word v [61, 35, 56, 43, 47] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_271 v H)
lemma mul_reduced_271 (x : A) : word v [62, 52, 42, 45, 6]*x=(word v [61, 35, 56, 43, 47]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_271 v H)
lemma reduced_272 : word v [35, 56, 43, 47, 7]=word v [35, 55, 27, 59, 50] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_272 v H)
lemma mul_reduced_272 (x : A) : word v [35, 56, 43, 47, 7]*x=(word v [35, 55, 27, 59, 50]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_272 v H)
lemma reduced_273 : word v [52, 41, 43, 48, 50]=word v [52, 41, 43, 47, 7] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_273 v H)
lemma mul_reduced_273 (x : A) : word v [52, 41, 43, 48, 50]*x=(word v [52, 41, 43, 47, 7]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_273 v H)
lemma reduced_274 : word v [48, 51, 64, 36, 70]=word v [47, 7, 17, 21, 70] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_274 v H)
lemma mul_reduced_274 (x : A) : word v [48, 51, 64, 36, 70]*x=(word v [47, 7, 17, 21, 70]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_274 v H)
lemma reduced_275 : word v [58, 33, 13, 49, 70]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_275 v H)
lemma mul_reduced_275 (x : A) : word v [58, 33, 13, 49, 70]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_275 v H)
lemma reduced_276 : word v [41, 43, 48, 51, 63]=word v [41, 43, 47, 7, 17] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_276 v H)
lemma mul_reduced_276 (x : A) : word v [41, 43, 48, 51, 63]*x=(word v [41, 43, 47, 7, 17]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_276 v H)
lemma reduced_277 : word v [55, 27, 59, 50, 17]=word v [55, 27, 58, 34, 63] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_277 v H)
lemma mul_reduced_277 (x : A) : word v [55, 27, 59, 50, 17]*x=(word v [55, 27, 58, 34, 63]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_277 v H)
lemma reduced_278 : word v [3, 40, 62, 52, 41]=word v [3, 40, 60, 4, 56] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_278 v H)
lemma mul_reduced_278 (x : A) : word v [3, 40, 62, 52, 41]*x=(word v [3, 40, 60, 4, 56]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_278 v H)
lemma reduced_279 : word v [37, 24, 19, 53, 56]=word v [37, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_279 v H)
lemma mul_reduced_279 (x : A) : word v [37, 24, 19, 53, 56]*x=(word v [37, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_279 v H)
lemma reduced_280 : word v [66, 24, 19, 53, 56]=word v [66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_280 v H)
lemma mul_reduced_280 (x : A) : word v [66, 24, 19, 53, 56]*x=(word v [66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_280 v H)
lemma reduced_281 : word v [67, 32, 62, 52, 41]=word v [67, 32, 61, 35, 56] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_281 v H)
lemma mul_reduced_281 (x : A) : word v [67, 32, 62, 52, 41]*x=(word v [67, 32, 61, 35, 56]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_281 v H)
lemma reduced_282 : word v [24, 19, 53, 54, 16]=word v [24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_282 v H)
lemma mul_reduced_282 (x : A) : word v [24, 19, 53, 54, 16]*x=(word v [24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_282 v H)
lemma reduced_283 : word v [29, 19, 53, 54, 16]=word v [28, 14, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_283 v H)
lemma mul_reduced_283 (x : A) : word v [29, 19, 53, 54, 16]*x=(word v [28, 14, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_283 v H)
lemma reduced_284 : word v [32, 61, 35, 56, 44]=word v [32, 61, 35, 55, 27] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_284 v H)
lemma mul_reduced_284 (x : A) : word v [32, 61, 35, 56, 44]*x=(word v [32, 61, 35, 55, 27]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_284 v H)
lemma reduced_285 : word v [39, 12, 35, 56, 44]=word v [39, 12, 35, 55, 27] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_285 v H)
lemma mul_reduced_285 (x : A) : word v [39, 12, 35, 56, 44]*x=(word v [39, 12, 35, 55, 27]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_285 v H)
lemma reduced_286 : word v [40, 60, 4, 56, 44]=word v [40, 60, 4, 54, 16] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_286 v H)
lemma mul_reduced_286 (x : A) : word v [40, 60, 4, 56, 44]*x=(word v [40, 60, 4, 54, 16]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_286 v H)
lemma reduced_287 : word v [4, 54, 16, 57, 5]=word v [4, 54, 15, 1, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_287 v H)
lemma mul_reduced_287 (x : A) : word v [4, 54, 16, 57, 5]*x=(word v [4, 54, 15, 1, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_287 v H)
lemma reduced_288 : word v [9, 41, 44, 58, 34]=word v [9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_288 v H)
lemma mul_reduced_288 (x : A) : word v [9, 41, 44, 58, 34]*x=(word v [9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_288 v H)
lemma reduced_289 : word v [35, 55, 27, 59, 51]=word v [35, 55, 27, 58, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_289 v H)
lemma mul_reduced_289 (x : A) : word v [35, 55, 27, 59, 51]*x=(word v [35, 55, 27, 58, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_289 v H)
lemma reduced_290 : word v [52, 41, 44, 58, 34]=word v [52, 41, 44, 57, 5] + word v [52, 41, 43, 48, 51] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_290 v H)
lemma mul_reduced_290 (x : A) : word v [52, 41, 44, 58, 34]*x=(word v [52, 41, 44, 57, 5]*x) + (word v [52, 41, 43, 48, 51]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_290 v H)
lemma reduced_291 : word v [53, 54, 15, 1, 34]=word v [52, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_291 v H)
lemma mul_reduced_291 (x : A) : word v [53, 54, 15, 1, 34]*x=(word v [52, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_291 v H)
lemma reduced_292 : word v [8, 66, 25, 60, 4]=word v [8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_292 v H)
lemma mul_reduced_292 (x : A) : word v [8, 66, 25, 60, 4]*x=(word v [8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_292 v H)
lemma reduced_293 : word v [22, 3, 40, 62, 53]=word v [22, 3, 40, 60, 4] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_293 v H)
lemma mul_reduced_293 (x : A) : word v [22, 3, 40, 62, 53]*x=(word v [22, 3, 40, 60, 4]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_293 v H)
lemma reduced_294 : word v [72, 37, 25, 60, 4]=word v [72, 37, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_294 v H)
lemma mul_reduced_294 (x : A) : word v [72, 37, 25, 60, 4]*x=(word v [72, 37, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_294 v H)
lemma reduced_295 : word v [73, 67, 32, 62, 53]=word v [73, 67, 32, 61, 35] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_295 v H)
lemma mul_reduced_295 (x : A) : word v [73, 67, 32, 62, 53]*x=(word v [73, 67, 32, 61, 35]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_295 v H)
lemma reduced_296 : word v [15, 1, 34, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_296 v H)
lemma mul_reduced_296 (x : A) : word v [15, 1, 34, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_296 v H)
lemma reduced_297 : word v [27, 58, 34, 64, 36]=word v [27, 58, 34, 63, 21] + word v [27, 58, 33, 13, 49] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_297 v H)
lemma mul_reduced_297 (x : A) : word v [27, 58, 34, 64, 36]*x=(word v [27, 58, 34, 63, 21]*x) + (word v [27, 58, 33, 13, 49]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_297 v H)
lemma reduced_298 : word v [43, 48, 51, 65, 49]=(-word v [43, 47, 7, 17, 21]) + word v [43, 48, 51, 64, 36] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_298 v H)
lemma mul_reduced_298 (x : A) : word v [43, 48, 51, 65, 49]*x=(-(word v [43, 47, 7, 17, 21]*x)) + (word v [43, 48, 51, 64, 36]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_298 v H)
lemma reduced_299 : word v [44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_299 v H)
lemma mul_reduced_299 (x : A) : word v [44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_299 v H)
end UniserialComputations.N6.Presentation.Universal
namespace UniserialComputations.N6.Presentation
variable (k : Type*) [Field k]
lemma reduced_240 : word (a k) [1, 34, 63, 20, 31]=0 := by
  exact Universal.reduced_240 (a k) (relation_zero k)
lemma reduced_241 : word (a k) [57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_241 (a k) (relation_zero k)
lemma reduced_242 : word (a k) [6, 7, 17, 21, 71]=0 := by
  exact Universal.reduced_242 (a k) (relation_zero k)
lemma reduced_243 : word (a k) [47, 7, 17, 21, 71]=0 := by
  exact Universal.reduced_243 (a k) (relation_zero k)
lemma reduced_244 : word (a k) [58, 34, 63, 21, 71]=0 := by
  exact Universal.reduced_244 (a k) (relation_zero k)
lemma reduced_245 : word (a k) [17, 21, 70, 22, 3]=word (a k) [17, 21, 69, 8, 68] := by
  exact Universal.reduced_245 (a k) (relation_zero k)
lemma reduced_246 : word (a k) [63, 21, 70, 22, 3]=word (a k) [63, 21, 69, 8, 68] := by
  exact Universal.reduced_246 (a k) (relation_zero k)
lemma reduced_247 : word (a k) [69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_247 (a k) (relation_zero k)
lemma reduced_248 : word (a k) [70, 22, 3, 40, 61]=0 := by
  exact Universal.reduced_248 (a k) (relation_zero k)
lemma reduced_249 : word (a k) [69, 8, 66, 25, 62]=word (a k) [69, 8, 66, 24, 19] := by
  exact Universal.reduced_249 (a k) (relation_zero k)
lemma reduced_250 : word (a k) [70, 23, 66, 24, 19]=word (a k) [70, 22, 3, 40, 62] := by
  exact Universal.reduced_250 (a k) (relation_zero k)
lemma reduced_251 : word (a k) [74, 10, 11, 26, 30]=0 := by
  exact Universal.reduced_251 (a k) (relation_zero k)
lemma reduced_252 : word (a k) [12, 35, 55, 27, 57]=0 := by
  exact Universal.reduced_252 (a k) (relation_zero k)
lemma reduced_253 : word (a k) [61, 35, 55, 27, 57]=0 := by
  exact Universal.reduced_253 (a k) (relation_zero k)
lemma reduced_254 : word (a k) [71, 72, 38, 28, 14]=word (a k) [69, 8, 66, 24, 18] + word (a k) [70, 23, 66, 24, 18] := by
  exact Universal.reduced_254 (a k) (relation_zero k)
lemma reduced_255 : word (a k) [10, 11, 26, 31, 72]=0 := by
  exact Universal.reduced_255 (a k) (relation_zero k)
lemma reduced_256 : word (a k) [31, 73, 67, 32, 60]=0 := by
  exact Universal.reduced_256 (a k) (relation_zero k)
lemma reduced_257 : word (a k) [41, 44, 58, 33, 13]=word (a k) [41, 43, 48, 51, 65] := by
  exact Universal.reduced_257 (a k) (relation_zero k)
lemma reduced_258 : word (a k) [55, 27, 58, 34, 65]=word (a k) [55, 27, 58, 33, 13] := by
  exact Universal.reduced_258 (a k) (relation_zero k)
lemma reduced_259 : word (a k) [67, 32, 61, 35, 54]=0 := by
  exact Universal.reduced_259 (a k) (relation_zero k)
lemma reduced_260 : word (a k) [48, 51, 64, 36, 69]=0 := by
  exact Universal.reduced_260 (a k) (relation_zero k)
lemma reduced_261 : word (a k) [58, 34, 63, 21, 69]=(-word (a k) [58, 33, 13, 49, 69]) := by
  exact Universal.reduced_261 (a k) (relation_zero k)
lemma reduced_262 : word (a k) [36, 71, 72, 38, 29]=word (a k) [36, 70, 23, 66, 24] := by
  exact Universal.reduced_262 (a k) (relation_zero k)
lemma reduced_263 : word (a k) [49, 71, 72, 38, 29]=word (a k) [49, 69, 8, 66, 24] := by
  exact Universal.reduced_263 (a k) (relation_zero k)
lemma reduced_264 : word (a k) [31, 73, 68, 39, 12]=word (a k) [31, 73, 67, 32, 61] := by
  exact Universal.reduced_264 (a k) (relation_zero k)
lemma reduced_265 : word (a k) [28, 14, 9, 41, 43]=0 := by
  exact Universal.reduced_265 (a k) (relation_zero k)
lemma reduced_266 : word (a k) [32, 62, 52, 42, 46]=word (a k) [32, 61, 35, 56, 43] := by
  exact Universal.reduced_266 (a k) (relation_zero k)
lemma reduced_267 : word (a k) [40, 62, 52, 42, 46]=word (a k) [39, 12, 35, 56, 43] := by
  exact Universal.reduced_267 (a k) (relation_zero k)
lemma reduced_268 : word (a k) [12, 35, 56, 43, 48]=word (a k) [12, 35, 55, 27, 59] := by
  exact Universal.reduced_268 (a k) (relation_zero k)
lemma reduced_269 : word (a k) [14, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_269 (a k) (relation_zero k)
lemma reduced_270 : word (a k) [61, 35, 56, 43, 48]=word (a k) [61, 35, 55, 27, 59] := by
  exact Universal.reduced_270 (a k) (relation_zero k)
lemma reduced_271 : word (a k) [62, 52, 42, 45, 6]=word (a k) [61, 35, 56, 43, 47] := by
  exact Universal.reduced_271 (a k) (relation_zero k)
lemma reduced_272 : word (a k) [35, 56, 43, 47, 7]=word (a k) [35, 55, 27, 59, 50] := by
  exact Universal.reduced_272 (a k) (relation_zero k)
lemma reduced_273 : word (a k) [52, 41, 43, 48, 50]=word (a k) [52, 41, 43, 47, 7] := by
  exact Universal.reduced_273 (a k) (relation_zero k)
lemma reduced_274 : word (a k) [48, 51, 64, 36, 70]=word (a k) [47, 7, 17, 21, 70] := by
  exact Universal.reduced_274 (a k) (relation_zero k)
lemma reduced_275 : word (a k) [58, 33, 13, 49, 70]=0 := by
  exact Universal.reduced_275 (a k) (relation_zero k)
lemma reduced_276 : word (a k) [41, 43, 48, 51, 63]=word (a k) [41, 43, 47, 7, 17] := by
  exact Universal.reduced_276 (a k) (relation_zero k)
lemma reduced_277 : word (a k) [55, 27, 59, 50, 17]=word (a k) [55, 27, 58, 34, 63] := by
  exact Universal.reduced_277 (a k) (relation_zero k)
lemma reduced_278 : word (a k) [3, 40, 62, 52, 41]=word (a k) [3, 40, 60, 4, 56] := by
  exact Universal.reduced_278 (a k) (relation_zero k)
lemma reduced_279 : word (a k) [37, 24, 19, 53, 56]=word (a k) [37, 24, 18, 9, 41] := by
  exact Universal.reduced_279 (a k) (relation_zero k)
lemma reduced_280 : word (a k) [66, 24, 19, 53, 56]=word (a k) [66, 24, 18, 9, 41] := by
  exact Universal.reduced_280 (a k) (relation_zero k)
lemma reduced_281 : word (a k) [67, 32, 62, 52, 41]=word (a k) [67, 32, 61, 35, 56] := by
  exact Universal.reduced_281 (a k) (relation_zero k)
lemma reduced_282 : word (a k) [24, 19, 53, 54, 16]=word (a k) [24, 18, 9, 41, 44] := by
  exact Universal.reduced_282 (a k) (relation_zero k)
lemma reduced_283 : word (a k) [29, 19, 53, 54, 16]=word (a k) [28, 14, 9, 41, 44] := by
  exact Universal.reduced_283 (a k) (relation_zero k)
lemma reduced_284 : word (a k) [32, 61, 35, 56, 44]=word (a k) [32, 61, 35, 55, 27] := by
  exact Universal.reduced_284 (a k) (relation_zero k)
lemma reduced_285 : word (a k) [39, 12, 35, 56, 44]=word (a k) [39, 12, 35, 55, 27] := by
  exact Universal.reduced_285 (a k) (relation_zero k)
lemma reduced_286 : word (a k) [40, 60, 4, 56, 44]=word (a k) [40, 60, 4, 54, 16] := by
  exact Universal.reduced_286 (a k) (relation_zero k)
lemma reduced_287 : word (a k) [4, 54, 16, 57, 5]=word (a k) [4, 54, 15, 1, 34] := by
  exact Universal.reduced_287 (a k) (relation_zero k)
lemma reduced_288 : word (a k) [9, 41, 44, 58, 34]=word (a k) [9, 41, 44, 57, 5] := by
  exact Universal.reduced_288 (a k) (relation_zero k)
lemma reduced_289 : word (a k) [35, 55, 27, 59, 51]=word (a k) [35, 55, 27, 58, 34] := by
  exact Universal.reduced_289 (a k) (relation_zero k)
lemma reduced_290 : word (a k) [52, 41, 44, 58, 34]=word (a k) [52, 41, 44, 57, 5] + word (a k) [52, 41, 43, 48, 51] := by
  exact Universal.reduced_290 (a k) (relation_zero k)
lemma reduced_291 : word (a k) [53, 54, 15, 1, 34]=word (a k) [52, 41, 44, 57, 5] := by
  exact Universal.reduced_291 (a k) (relation_zero k)
lemma reduced_292 : word (a k) [8, 66, 25, 60, 4]=word (a k) [8, 66, 24, 19, 53] := by
  exact Universal.reduced_292 (a k) (relation_zero k)
lemma reduced_293 : word (a k) [22, 3, 40, 62, 53]=word (a k) [22, 3, 40, 60, 4] := by
  exact Universal.reduced_293 (a k) (relation_zero k)
lemma reduced_294 : word (a k) [72, 37, 25, 60, 4]=word (a k) [72, 37, 24, 19, 53] := by
  exact Universal.reduced_294 (a k) (relation_zero k)
lemma reduced_295 : word (a k) [73, 67, 32, 62, 53]=word (a k) [73, 67, 32, 61, 35] := by
  exact Universal.reduced_295 (a k) (relation_zero k)
lemma reduced_296 : word (a k) [15, 1, 34, 63, 21]=0 := by
  exact Universal.reduced_296 (a k) (relation_zero k)
lemma reduced_297 : word (a k) [27, 58, 34, 64, 36]=word (a k) [27, 58, 34, 63, 21] + word (a k) [27, 58, 33, 13, 49] := by
  exact Universal.reduced_297 (a k) (relation_zero k)
lemma reduced_298 : word (a k) [43, 48, 51, 65, 49]=(-word (a k) [43, 47, 7, 17, 21]) + word (a k) [43, 48, 51, 64, 36] := by
  exact Universal.reduced_298 (a k) (relation_zero k)
lemma reduced_299 : word (a k) [44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_299 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
