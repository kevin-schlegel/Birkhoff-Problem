import N6Rules4
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma rule_209 : word v [4, 54, 15, 1, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [4, 54, 15]) (defining_0 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_210 : word v [53, 54, 15, 1, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [53, 54, 15]) (defining_0 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_211 : word v [54, 15, 1, 34, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [54, 15]) (defining_1 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_212 : word v [21, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [21, 70, 22]) (defining_2 v H)
  have h1 := congrArg (fun x : A => word v [39] * x) (rule_144 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_213 : word v [36, 70, 22, 3, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 70, 22]) (defining_2 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_214 : word v [3, 40, 62, 52, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_3 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_215 : word v [3, 40, 60, 4, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [3, 40, 60]) (defining_4 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_216 : word v [37, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [37, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_192 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_217 : word v [66, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [66, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_193 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_218 : word v [24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_100 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_180 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_219 : word v [40, 60, 4, 56, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [40, 60]) (defining_5 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_220 : word v [41, 44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 44, 57]) (defining_6 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_221 : word v [41, 44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_222 : word v [54, 15, 1, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [54, 16, 57]) (defining_7 v H)
  have h1 := congrArg (fun x : A => word v [65] * x) (rule_189 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_223 : word v [49, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [49, 69]) (defining_8 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_224 : word v [13, 49, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [13, 49, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_225 : word v [17, 21, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [17, 21, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_226 : word v [63, 21, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [63, 21, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_227 : word v [9, 41, 44, 58, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_10 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_228 : word v [37, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [37, 24, 18]) (defining_11 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_229 : word v [66, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [66, 24, 18]) (defining_11 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_230 : word v [19, 53, 54, 15, 1] + (-word v [18, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_185 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_231 : (-word v [60, 4, 54, 15, 1]) + word v [60, 4, 54, 16, 58]=0 := by
  have h0 := congrArg (fun x : A => x * word v [60, 4, 54]) (defining_12 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_232 : word v [18, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_185 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_233 : word v [60, 4, 54, 16, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [60, 4, 54]) (defining_13 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_234 : word v [27, 58, 34, 63, 20]=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 59, 50]) (defining_14 v H)
  have h1 := congrArg (fun x : A => word v [20] * x) (rule_177 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_235 : word v [43, 47, 7, 17, 20]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 47, 7]) (defining_14 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_236 : word v [45, 6, 7, 17, 20]=0 := by
  have h0 := congrArg (fun x : A => x * word v [45, 6, 7]) (defining_14 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_237 : (-word v [8, 66, 24, 18, 9]) + word v [8, 66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [8, 66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_238 : word v [23, 66, 24, 18, 9] + (-word v [22, 3, 40, 62, 52])=0 := by
  have h0 := congrArg (fun x : A => x * word v [23, 66, 24]) (defining_16 v H)
  have h1 := congrArg (fun x : A => word v [52] * x) (rule_150 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_239 : (-word v [72, 37, 24, 18, 9]) + word v [72, 37, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [72, 37, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_240 : word v [1, 34, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [1, 34, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_241 : word v [57, 5, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [57, 5, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_242 : word v [6, 7, 17, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [6, 7, 17]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_243 : word v [47, 7, 17, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [47, 7, 17]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_244 : word v [58, 34, 63, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 34, 63]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_245 : word v [17, 21, 70, 22, 3] + (-word v [17, 21, 69, 8, 68])=0 := by
  have h0 := congrArg (fun x : A => x * word v [17, 21, 70]) (defining_20 v H)
  have h1 := congrArg (fun x : A => word v [68] * x) (rule_203 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_246 : word v [63, 21, 70, 22, 3] + (-word v [63, 21, 69, 8, 68])=0 := by
  have h0 := congrArg (fun x : A => x * word v [63, 21, 70]) (defining_20 v H)
  have h1 := congrArg (fun x : A => word v [68] * x) (rule_204 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_247 : word v [69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_248 : word v [70, 22, 3, 40, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [70, 23, 66]) (defining_21 v H)
  have h1 := congrArg (fun x : A => word v [61] * x) (rule_201 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_249 : (-word v [69, 8, 66, 24, 19]) + word v [69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_250 : word v [70, 23, 66, 24, 19] + (-word v [70, 22, 3, 40, 62])=0 := by
  have h0 := congrArg (fun x : A => x * word v [70, 23, 66]) (defining_22 v H)
  have h1 := congrArg (fun x : A => word v [62] * x) (rule_201 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_251 : word v [74, 10, 11, 26, 30]=0 := by
  have h0 := congrArg (fun x : A => x * word v [74, 10, 11]) (defining_23 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_252 : word v [12, 35, 55, 27, 57]=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55]) (defining_24 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_253 : word v [61, 35, 55, 27, 57]=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55]) (defining_24 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_254 : word v [71, 72, 38, 28, 14] + (-word v [69, 8, 66, 24, 18]) + (-word v [70, 23, 66, 24, 18])=0 := by
  have h0 := congrArg (fun x : A => x * word v [71, 72, 38]) (defining_25 v H)
  have h1 := congrArg (fun x : A => word v [18] * x) (rule_164 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_255 : word v [10, 11, 26, 31, 72]=0 := by
  have h0 := congrArg (fun x : A => x * word v [10, 11, 26]) (defining_26 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_256 : word v [31, 73, 67, 32, 60]=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 67]) (defining_27 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_257 : word v [41, 44, 58, 33, 13] + (-word v [41, 43, 48, 51, 65])=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 44, 58]) (defining_28 v H)
  have h1 := congrArg (fun x : A => word v [65] * x) (rule_188 v H)
  have h2 := congrArg (fun x : A => word v [] * x) (rule_221 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1 + (1) * h2
lemma rule_258 : (-word v [55, 27, 58, 33, 13]) + word v [55, 27, 58, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58]) (defining_28 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_259 : word v [67, 32, 61, 35, 54]=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 61]) (defining_29 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_260 : word v [48, 51, 64, 36, 69]=0 := by
  have h0 := congrArg (fun x : A => x * word v [48, 51, 64]) (defining_30 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_261 : word v [58, 34, 63, 21, 69] + word v [58, 33, 13, 49, 69]=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 34, 64]) (defining_30 v H)
  have h1 := congrArg (fun x : A => word v [69] * x) (rule_198 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_262 : (-word v [36, 70, 23, 66, 24]) + word v [36, 71, 72, 38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 71, 72]) (defining_31 v H)
  have h1 := congrArg (fun x : A => word v [24] * x) (rule_207 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_263 : (-word v [49, 69, 8, 66, 24]) + word v [49, 71, 72, 38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v [49, 71, 72]) (defining_31 v H)
  have h1 := congrArg (fun x : A => word v [24] * x) (rule_208 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_264 : word v [31, 73, 68, 39, 12] + (-word v [31, 73, 67, 32, 61])=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 68]) (defining_32 v H)
  have h1 := congrArg (fun x : A => word v [61] * x) (rule_199 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_265 : word v [28, 14, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [28, 14, 9]) (defining_33 v H)
  have h1 := congrArg (fun x : A => word v [46] * x) (rule_127 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_266 : (-word v [32, 61, 35, 56, 43]) + word v [32, 62, 52, 42, 46]=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 62, 52]) (defining_33 v H)
  have h1 := congrArg (fun x : A => word v [43] * x) (rule_182 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_267 : (-word v [39, 12, 35, 56, 43]) + word v [40, 62, 52, 42, 46]=0 := by
  have h0 := congrArg (fun x : A => x * word v [40, 62, 52]) (defining_33 v H)
  have h1 := congrArg (fun x : A => word v [43] * x) (rule_183 v H)
  have h2 := congrArg (fun x : A => word v [] * x) (rule_219 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (1) * h2
lemma rule_268 : word v [12, 35, 56, 43, 48] + (-word v [12, 35, 55, 27, 59])=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 56]) (defining_34 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_184 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_269 : word v [14, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [14, 9, 41]) (defining_34 v H)
  have h1 := congrArg (fun x : A => word v [48] * x) (rule_166 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_270 : word v [61, 35, 56, 43, 48] + (-word v [61, 35, 55, 27, 59])=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 56]) (defining_34 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_187 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_271 : word v [62, 52, 42, 45, 6] + (-word v [61, 35, 56, 43, 47])=0 := by
  have h0 := congrArg (fun x : A => x * word v [62, 52, 42]) (defining_35 v H)
  have h1 := congrArg (fun x : A => word v [47] * x) (rule_168 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_272 : word v [35, 56, 43, 47, 7] + (-word v [35, 55, 27, 59, 50])=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 56, 43]) (defining_36 v H)
  have h1 := congrArg (fun x : A => word v [50] * x) (rule_170 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_273 : (-word v [52, 41, 43, 47, 7]) + word v [52, 41, 43, 48, 50]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43]) (defining_36 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_274 : (-word v [47, 7, 17, 21, 70]) + word v [48, 51, 64, 36, 70]=0 := by
  have h0 := congrArg (fun x : A => x * word v [48, 51, 65]) (defining_37 v H)
  have h1 := congrArg (fun x : A => word v [70] * x) (rule_196 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_275 : word v [58, 33, 13, 49, 70]=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 33, 13]) (defining_37 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_276 : (-word v [41, 43, 47, 7, 17]) + word v [41, 43, 48, 51, 63]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 48]) (defining_38 v H)
  have h1 := congrArg (fun x : A => word v [17] * x) (rule_173 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_277 : word v [55, 27, 59, 50, 17] + (-word v [55, 27, 58, 34, 63])=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 59]) (defining_38 v H)
  have h1 := congrArg (fun x : A => word v [63] * x) (rule_190 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_278 : word v [3, 40, 62, 52, 41] + (-word v [3, 40, 60, 4, 56])=0 := by
  have h0 := congrArg (fun x : A => x * word v [3, 40, 62]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [56] * x) (rule_191 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_279 : (-word v [37, 24, 18, 9, 41]) + word v [37, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [37, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_136 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_280 : (-word v [66, 24, 18, 9, 41]) + word v [66, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [66, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_137 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_281 : word v [67, 32, 62, 52, 41] + (-word v [67, 32, 61, 35, 56])=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 62]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [56] * x) (rule_194 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_282 : word v [24, 19, 53, 54, 16] + (-word v [24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_117 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_180 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_283 : word v [29, 19, 53, 54, 16] + (-word v [28, 14, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [29, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_135 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_181 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_284 : (-word v [32, 61, 35, 55, 27]) + word v [32, 61, 35, 56, 44]=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [16] * x) (rule_160 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_285 : (-word v [39, 12, 35, 55, 27]) + word v [39, 12, 35, 56, 44]=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [16] * x) (rule_161 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_286 : (-word v [40, 60, 4, 54, 16]) + word v [40, 60, 4, 56, 44]=0 := by
  have h0 := congrArg (fun x : A => x * word v [40, 60, 4]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_118 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_287 : word v [4, 54, 16, 57, 5] + (-word v [4, 54, 15, 1, 34])=0 := by
  have h0 := congrArg (fun x : A => x * word v [4, 54, 16]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [34] * x) (rule_128 v H)
  have h2 := congrArg (fun x : A => word v [51] * x) (rule_130 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_288 : (-word v [9, 41, 44, 57, 5]) + word v [9, 41, 44, 58, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [9, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_169 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_289 : (-word v [35, 55, 27, 58, 34]) + word v [35, 55, 27, 59, 51]=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [5] * x) (rule_153 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_290 : (-word v [52, 41, 44, 57, 5]) + word v [52, 41, 44, 58, 34] + (-word v [52, 41, 43, 48, 51])=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_171 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_291 : (-word v [52, 41, 44, 57, 5]) + word v [53, 54, 15, 1, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [53, 54, 16]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [5] * x) (rule_154 v H)
  have h2 := congrArg (fun x : A => word v [34] * x) (rule_129 v H)
  have h3 := congrArg (fun x : A => word v [51] * x) (rule_131 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1 + (-1) * h2 + (1) * h3
lemma rule_292 : word v [8, 66, 25, 60, 4] + (-word v [8, 66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [8, 66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_146 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_149 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_293 : (-word v [22, 3, 40, 60, 4]) + word v [22, 3, 40, 62, 53]=0 := by
  have h0 := congrArg (fun x : A => x * word v [22, 3, 40]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_147 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_294 : word v [72, 37, 25, 60, 4] + (-word v [72, 37, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [72, 37, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_148 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_151 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_295 : (-word v [73, 67, 32, 61, 35]) + word v [73, 67, 32, 62, 53]=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [4] * x) (rule_157 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_296 : word v [15, 1, 34, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [15, 1, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_115 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_121 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_297 : (-word v [27, 58, 34, 63, 21]) + word v [27, 58, 34, 64, 36] + (-word v [27, 58, 33, 13, 49])=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [49] * x) (rule_158 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_298 : word v [43, 47, 7, 17, 21] + (-word v [43, 48, 51, 64, 36]) + word v [43, 48, 51, 65, 49]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 48, 51]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [21] * x) (rule_178 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_299 : word v [44, 57, 5, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [44, 57, 5]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_120 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_122 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_300 : word v [45, 6, 7, 17, 21] + (-word v [46, 48, 51, 64, 36]) + word v [46, 48, 51, 65, 49]=0 := by
  have h0 := congrArg (fun x : A => x * word v [46, 48, 51]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [21] * x) (rule_179 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_301 : word v [21, 69, 8, 66, 25] + word v [21, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [21, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_124 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_302 : (-word v [26, 31, 73, 67, 32]) + word v [26, 31, 73, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31, 73]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [25] * x) (rule_206 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_303 : word v [36, 70, 23, 66, 25] + (-word v [36, 70, 22, 3, 40])=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 70, 23]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_143 v H)
  have h2 := congrArg (fun x : A => word v [40] * x) (rule_145 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_304 : word v [49, 69, 8, 66, 25] + word v [49, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [49, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_125 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_305 : word v [7, 17, 21, 69, 8] + word v [7, 17, 21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [7, 17, 21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [73] * x) (rule_140 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_306 : (-word v [33, 13, 49, 69, 8]) + word v [33, 13, 49, 71, 73]=0 := by
  have h0 := congrArg (fun x : A => x * word v [33, 13, 49]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [23] * x) (rule_175 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_307 : (-word v [33, 13, 49, 69, 8]) + word v [34, 63, 21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [34, 63, 21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [8] * x) (rule_162 v H)
  have h2 := congrArg (fun x : A => word v [73] * x) (rule_141 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_308 : word v [50, 17, 21, 69, 8] + word v [50, 17, 21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [50, 17, 21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [73] * x) (rule_142 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_309 : word v [51, 64, 36, 71, 73] + word v [50, 17, 21, 69, 8]=0 := by
  have h0 := congrArg (fun x : A => x * word v [51, 64, 36]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [8] * x) (rule_163 v H)
  have h2 := congrArg (fun x : A => word v [23] * x) (rule_176 v H)
  have h3 := congrArg (fun x : A => word v [] * x) (rule_308 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (1) * h2 + (1) * h3
lemma rule_310 : word v [11, 26, 31, 73, 66]=0 := by
  have h0 := congrArg (fun x : A => x * word v [11, 26, 31]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [37] * x) (rule_156 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_311 : word v [13, 49, 71, 72, 37] + (-word v [13, 49, 69, 8, 66])=0 := by
  have h0 := congrArg (fun x : A => x * word v [13, 49, 71]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [66] * x) (rule_202 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_312 : word v [64, 36, 71, 72, 37] + word v [63, 21, 69, 8, 66]=0 := by
  have h0 := congrArg (fun x : A => x * word v [64, 36, 71]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [66] * x) (rule_205 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
end UniserialComputations.N6.Presentation.Universal
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma rule_209 : word (a k) [4, 54, 15, 1, 33]=0 := by
  exact Universal.rule_209 (a k) (relation_zero k)
lemma rule_210 : word (a k) [53, 54, 15, 1, 33]=0 := by
  exact Universal.rule_210 (a k) (relation_zero k)
lemma rule_211 : word (a k) [54, 15, 1, 34, 64]=0 := by
  exact Universal.rule_211 (a k) (relation_zero k)
lemma rule_212 : word (a k) [21, 69, 8, 68, 39]=0 := by
  exact Universal.rule_212 (a k) (relation_zero k)
lemma rule_213 : word (a k) [36, 70, 22, 3, 39]=0 := by
  exact Universal.rule_213 (a k) (relation_zero k)
lemma rule_214 : word (a k) [3, 40, 62, 52, 42]=0 := by
  exact Universal.rule_214 (a k) (relation_zero k)
lemma rule_215 : word (a k) [3, 40, 60, 4, 55]=0 := by
  exact Universal.rule_215 (a k) (relation_zero k)
lemma rule_216 : word (a k) [37, 24, 19, 53, 55]=0 := by
  exact Universal.rule_216 (a k) (relation_zero k)
lemma rule_217 : word (a k) [66, 24, 19, 53, 55]=0 := by
  exact Universal.rule_217 (a k) (relation_zero k)
lemma rule_218 : word (a k) [24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_218 (a k) (relation_zero k)
lemma rule_219 : word (a k) [40, 60, 4, 56, 43]=0 := by
  exact Universal.rule_219 (a k) (relation_zero k)
lemma rule_220 : word (a k) [41, 44, 57, 5, 64]=0 := by
  exact Universal.rule_220 (a k) (relation_zero k)
lemma rule_221 : word (a k) [41, 44, 57, 5, 65]=0 := by
  exact Universal.rule_221 (a k) (relation_zero k)
lemma rule_222 : word (a k) [54, 15, 1, 34, 65]=0 := by
  exact Universal.rule_222 (a k) (relation_zero k)
lemma rule_223 : word (a k) [49, 69, 8, 68, 39]=0 := by
  exact Universal.rule_223 (a k) (relation_zero k)
lemma rule_224 : word (a k) [13, 49, 69, 8, 67]=0 := by
  exact Universal.rule_224 (a k) (relation_zero k)
lemma rule_225 : word (a k) [17, 21, 69, 8, 67]=0 := by
  exact Universal.rule_225 (a k) (relation_zero k)
lemma rule_226 : word (a k) [63, 21, 69, 8, 67]=0 := by
  exact Universal.rule_226 (a k) (relation_zero k)
lemma rule_227 : word (a k) [9, 41, 44, 58, 33]=0 := by
  exact Universal.rule_227 (a k) (relation_zero k)
lemma rule_228 : word (a k) [37, 24, 18, 9, 42]=0 := by
  exact Universal.rule_228 (a k) (relation_zero k)
lemma rule_229 : word (a k) [66, 24, 18, 9, 42]=0 := by
  exact Universal.rule_229 (a k) (relation_zero k)
lemma rule_230 : word (a k) [19, 53, 54, 15, 1] + (-word (a k) [18, 9, 41, 44, 58])=0 := by
  exact Universal.rule_230 (a k) (relation_zero k)
lemma rule_231 : (-word (a k) [60, 4, 54, 15, 1]) + word (a k) [60, 4, 54, 16, 58]=0 := by
  exact Universal.rule_231 (a k) (relation_zero k)
lemma rule_232 : word (a k) [18, 9, 41, 44, 59]=0 := by
  exact Universal.rule_232 (a k) (relation_zero k)
lemma rule_233 : word (a k) [60, 4, 54, 16, 59]=0 := by
  exact Universal.rule_233 (a k) (relation_zero k)
lemma rule_234 : word (a k) [27, 58, 34, 63, 20]=0 := by
  exact Universal.rule_234 (a k) (relation_zero k)
lemma rule_235 : word (a k) [43, 47, 7, 17, 20]=0 := by
  exact Universal.rule_235 (a k) (relation_zero k)
lemma rule_236 : word (a k) [45, 6, 7, 17, 20]=0 := by
  exact Universal.rule_236 (a k) (relation_zero k)
lemma rule_237 : (-word (a k) [8, 66, 24, 18, 9]) + word (a k) [8, 66, 24, 19, 52]=0 := by
  exact Universal.rule_237 (a k) (relation_zero k)
lemma rule_238 : word (a k) [23, 66, 24, 18, 9] + (-word (a k) [22, 3, 40, 62, 52])=0 := by
  exact Universal.rule_238 (a k) (relation_zero k)
lemma rule_239 : (-word (a k) [72, 37, 24, 18, 9]) + word (a k) [72, 37, 24, 19, 52]=0 := by
  exact Universal.rule_239 (a k) (relation_zero k)
lemma rule_240 : word (a k) [1, 34, 63, 20, 31]=0 := by
  exact Universal.rule_240 (a k) (relation_zero k)
lemma rule_241 : word (a k) [57, 5, 63, 20, 31]=0 := by
  exact Universal.rule_241 (a k) (relation_zero k)
lemma rule_242 : word (a k) [6, 7, 17, 21, 71]=0 := by
  exact Universal.rule_242 (a k) (relation_zero k)
lemma rule_243 : word (a k) [47, 7, 17, 21, 71]=0 := by
  exact Universal.rule_243 (a k) (relation_zero k)
lemma rule_244 : word (a k) [58, 34, 63, 21, 71]=0 := by
  exact Universal.rule_244 (a k) (relation_zero k)
lemma rule_245 : word (a k) [17, 21, 70, 22, 3] + (-word (a k) [17, 21, 69, 8, 68])=0 := by
  exact Universal.rule_245 (a k) (relation_zero k)
lemma rule_246 : word (a k) [63, 21, 70, 22, 3] + (-word (a k) [63, 21, 69, 8, 68])=0 := by
  exact Universal.rule_246 (a k) (relation_zero k)
lemma rule_247 : word (a k) [69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_247 (a k) (relation_zero k)
lemma rule_248 : word (a k) [70, 22, 3, 40, 61]=0 := by
  exact Universal.rule_248 (a k) (relation_zero k)
lemma rule_249 : (-word (a k) [69, 8, 66, 24, 19]) + word (a k) [69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_249 (a k) (relation_zero k)
lemma rule_250 : word (a k) [70, 23, 66, 24, 19] + (-word (a k) [70, 22, 3, 40, 62])=0 := by
  exact Universal.rule_250 (a k) (relation_zero k)
lemma rule_251 : word (a k) [74, 10, 11, 26, 30]=0 := by
  exact Universal.rule_251 (a k) (relation_zero k)
lemma rule_252 : word (a k) [12, 35, 55, 27, 57]=0 := by
  exact Universal.rule_252 (a k) (relation_zero k)
lemma rule_253 : word (a k) [61, 35, 55, 27, 57]=0 := by
  exact Universal.rule_253 (a k) (relation_zero k)
lemma rule_254 : word (a k) [71, 72, 38, 28, 14] + (-word (a k) [69, 8, 66, 24, 18]) + (-word (a k) [70, 23, 66, 24, 18])=0 := by
  exact Universal.rule_254 (a k) (relation_zero k)
lemma rule_255 : word (a k) [10, 11, 26, 31, 72]=0 := by
  exact Universal.rule_255 (a k) (relation_zero k)
lemma rule_256 : word (a k) [31, 73, 67, 32, 60]=0 := by
  exact Universal.rule_256 (a k) (relation_zero k)
lemma rule_257 : word (a k) [41, 44, 58, 33, 13] + (-word (a k) [41, 43, 48, 51, 65])=0 := by
  exact Universal.rule_257 (a k) (relation_zero k)
lemma rule_258 : (-word (a k) [55, 27, 58, 33, 13]) + word (a k) [55, 27, 58, 34, 65]=0 := by
  exact Universal.rule_258 (a k) (relation_zero k)
lemma rule_259 : word (a k) [67, 32, 61, 35, 54]=0 := by
  exact Universal.rule_259 (a k) (relation_zero k)
lemma rule_260 : word (a k) [48, 51, 64, 36, 69]=0 := by
  exact Universal.rule_260 (a k) (relation_zero k)
lemma rule_261 : word (a k) [58, 34, 63, 21, 69] + word (a k) [58, 33, 13, 49, 69]=0 := by
  exact Universal.rule_261 (a k) (relation_zero k)
lemma rule_262 : (-word (a k) [36, 70, 23, 66, 24]) + word (a k) [36, 71, 72, 38, 29]=0 := by
  exact Universal.rule_262 (a k) (relation_zero k)
lemma rule_263 : (-word (a k) [49, 69, 8, 66, 24]) + word (a k) [49, 71, 72, 38, 29]=0 := by
  exact Universal.rule_263 (a k) (relation_zero k)
lemma rule_264 : word (a k) [31, 73, 68, 39, 12] + (-word (a k) [31, 73, 67, 32, 61])=0 := by
  exact Universal.rule_264 (a k) (relation_zero k)
lemma rule_265 : word (a k) [28, 14, 9, 41, 43]=0 := by
  exact Universal.rule_265 (a k) (relation_zero k)
lemma rule_266 : (-word (a k) [32, 61, 35, 56, 43]) + word (a k) [32, 62, 52, 42, 46]=0 := by
  exact Universal.rule_266 (a k) (relation_zero k)
lemma rule_267 : (-word (a k) [39, 12, 35, 56, 43]) + word (a k) [40, 62, 52, 42, 46]=0 := by
  exact Universal.rule_267 (a k) (relation_zero k)
lemma rule_268 : word (a k) [12, 35, 56, 43, 48] + (-word (a k) [12, 35, 55, 27, 59])=0 := by
  exact Universal.rule_268 (a k) (relation_zero k)
lemma rule_269 : word (a k) [14, 9, 41, 44, 59]=0 := by
  exact Universal.rule_269 (a k) (relation_zero k)
lemma rule_270 : word (a k) [61, 35, 56, 43, 48] + (-word (a k) [61, 35, 55, 27, 59])=0 := by
  exact Universal.rule_270 (a k) (relation_zero k)
lemma rule_271 : word (a k) [62, 52, 42, 45, 6] + (-word (a k) [61, 35, 56, 43, 47])=0 := by
  exact Universal.rule_271 (a k) (relation_zero k)
lemma rule_272 : word (a k) [35, 56, 43, 47, 7] + (-word (a k) [35, 55, 27, 59, 50])=0 := by
  exact Universal.rule_272 (a k) (relation_zero k)
lemma rule_273 : (-word (a k) [52, 41, 43, 47, 7]) + word (a k) [52, 41, 43, 48, 50]=0 := by
  exact Universal.rule_273 (a k) (relation_zero k)
lemma rule_274 : (-word (a k) [47, 7, 17, 21, 70]) + word (a k) [48, 51, 64, 36, 70]=0 := by
  exact Universal.rule_274 (a k) (relation_zero k)
lemma rule_275 : word (a k) [58, 33, 13, 49, 70]=0 := by
  exact Universal.rule_275 (a k) (relation_zero k)
lemma rule_276 : (-word (a k) [41, 43, 47, 7, 17]) + word (a k) [41, 43, 48, 51, 63]=0 := by
  exact Universal.rule_276 (a k) (relation_zero k)
lemma rule_277 : word (a k) [55, 27, 59, 50, 17] + (-word (a k) [55, 27, 58, 34, 63])=0 := by
  exact Universal.rule_277 (a k) (relation_zero k)
lemma rule_278 : word (a k) [3, 40, 62, 52, 41] + (-word (a k) [3, 40, 60, 4, 56])=0 := by
  exact Universal.rule_278 (a k) (relation_zero k)
lemma rule_279 : (-word (a k) [37, 24, 18, 9, 41]) + word (a k) [37, 24, 19, 53, 56]=0 := by
  exact Universal.rule_279 (a k) (relation_zero k)
lemma rule_280 : (-word (a k) [66, 24, 18, 9, 41]) + word (a k) [66, 24, 19, 53, 56]=0 := by
  exact Universal.rule_280 (a k) (relation_zero k)
lemma rule_281 : word (a k) [67, 32, 62, 52, 41] + (-word (a k) [67, 32, 61, 35, 56])=0 := by
  exact Universal.rule_281 (a k) (relation_zero k)
lemma rule_282 : word (a k) [24, 19, 53, 54, 16] + (-word (a k) [24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_282 (a k) (relation_zero k)
lemma rule_283 : word (a k) [29, 19, 53, 54, 16] + (-word (a k) [28, 14, 9, 41, 44])=0 := by
  exact Universal.rule_283 (a k) (relation_zero k)
lemma rule_284 : (-word (a k) [32, 61, 35, 55, 27]) + word (a k) [32, 61, 35, 56, 44]=0 := by
  exact Universal.rule_284 (a k) (relation_zero k)
lemma rule_285 : (-word (a k) [39, 12, 35, 55, 27]) + word (a k) [39, 12, 35, 56, 44]=0 := by
  exact Universal.rule_285 (a k) (relation_zero k)
lemma rule_286 : (-word (a k) [40, 60, 4, 54, 16]) + word (a k) [40, 60, 4, 56, 44]=0 := by
  exact Universal.rule_286 (a k) (relation_zero k)
lemma rule_287 : word (a k) [4, 54, 16, 57, 5] + (-word (a k) [4, 54, 15, 1, 34])=0 := by
  exact Universal.rule_287 (a k) (relation_zero k)
lemma rule_288 : (-word (a k) [9, 41, 44, 57, 5]) + word (a k) [9, 41, 44, 58, 34]=0 := by
  exact Universal.rule_288 (a k) (relation_zero k)
lemma rule_289 : (-word (a k) [35, 55, 27, 58, 34]) + word (a k) [35, 55, 27, 59, 51]=0 := by
  exact Universal.rule_289 (a k) (relation_zero k)
lemma rule_290 : (-word (a k) [52, 41, 44, 57, 5]) + word (a k) [52, 41, 44, 58, 34] + (-word (a k) [52, 41, 43, 48, 51])=0 := by
  exact Universal.rule_290 (a k) (relation_zero k)
lemma rule_291 : (-word (a k) [52, 41, 44, 57, 5]) + word (a k) [53, 54, 15, 1, 34]=0 := by
  exact Universal.rule_291 (a k) (relation_zero k)
lemma rule_292 : word (a k) [8, 66, 25, 60, 4] + (-word (a k) [8, 66, 24, 19, 53])=0 := by
  exact Universal.rule_292 (a k) (relation_zero k)
lemma rule_293 : (-word (a k) [22, 3, 40, 60, 4]) + word (a k) [22, 3, 40, 62, 53]=0 := by
  exact Universal.rule_293 (a k) (relation_zero k)
lemma rule_294 : word (a k) [72, 37, 25, 60, 4] + (-word (a k) [72, 37, 24, 19, 53])=0 := by
  exact Universal.rule_294 (a k) (relation_zero k)
lemma rule_295 : (-word (a k) [73, 67, 32, 61, 35]) + word (a k) [73, 67, 32, 62, 53]=0 := by
  exact Universal.rule_295 (a k) (relation_zero k)
lemma rule_296 : word (a k) [15, 1, 34, 63, 21]=0 := by
  exact Universal.rule_296 (a k) (relation_zero k)
lemma rule_297 : (-word (a k) [27, 58, 34, 63, 21]) + word (a k) [27, 58, 34, 64, 36] + (-word (a k) [27, 58, 33, 13, 49])=0 := by
  exact Universal.rule_297 (a k) (relation_zero k)
lemma rule_298 : word (a k) [43, 47, 7, 17, 21] + (-word (a k) [43, 48, 51, 64, 36]) + word (a k) [43, 48, 51, 65, 49]=0 := by
  exact Universal.rule_298 (a k) (relation_zero k)
lemma rule_299 : word (a k) [44, 57, 5, 63, 21]=0 := by
  exact Universal.rule_299 (a k) (relation_zero k)
lemma rule_300 : word (a k) [45, 6, 7, 17, 21] + (-word (a k) [46, 48, 51, 64, 36]) + word (a k) [46, 48, 51, 65, 49]=0 := by
  exact Universal.rule_300 (a k) (relation_zero k)
lemma rule_301 : word (a k) [21, 69, 8, 66, 25] + word (a k) [21, 69, 8, 68, 40]=0 := by
  exact Universal.rule_301 (a k) (relation_zero k)
lemma rule_302 : (-word (a k) [26, 31, 73, 67, 32]) + word (a k) [26, 31, 73, 68, 40]=0 := by
  exact Universal.rule_302 (a k) (relation_zero k)
lemma rule_303 : word (a k) [36, 70, 23, 66, 25] + (-word (a k) [36, 70, 22, 3, 40])=0 := by
  exact Universal.rule_303 (a k) (relation_zero k)
lemma rule_304 : word (a k) [49, 69, 8, 66, 25] + word (a k) [49, 69, 8, 68, 40]=0 := by
  exact Universal.rule_304 (a k) (relation_zero k)
lemma rule_305 : word (a k) [7, 17, 21, 69, 8] + word (a k) [7, 17, 21, 70, 23]=0 := by
  exact Universal.rule_305 (a k) (relation_zero k)
lemma rule_306 : (-word (a k) [33, 13, 49, 69, 8]) + word (a k) [33, 13, 49, 71, 73]=0 := by
  exact Universal.rule_306 (a k) (relation_zero k)
lemma rule_307 : (-word (a k) [33, 13, 49, 69, 8]) + word (a k) [34, 63, 21, 70, 23]=0 := by
  exact Universal.rule_307 (a k) (relation_zero k)
lemma rule_308 : word (a k) [50, 17, 21, 69, 8] + word (a k) [50, 17, 21, 70, 23]=0 := by
  exact Universal.rule_308 (a k) (relation_zero k)
lemma rule_309 : word (a k) [51, 64, 36, 71, 73] + word (a k) [50, 17, 21, 69, 8]=0 := by
  exact Universal.rule_309 (a k) (relation_zero k)
lemma rule_310 : word (a k) [11, 26, 31, 73, 66]=0 := by
  exact Universal.rule_310 (a k) (relation_zero k)
lemma rule_311 : word (a k) [13, 49, 71, 72, 37] + (-word (a k) [13, 49, 69, 8, 66])=0 := by
  exact Universal.rule_311 (a k) (relation_zero k)
lemma rule_312 : word (a k) [64, 36, 71, 72, 37] + word (a k) [63, 21, 69, 8, 66]=0 := by
  exact Universal.rule_312 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
