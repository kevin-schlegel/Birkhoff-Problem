import N6NormalData
import N6Reduced0
import N6Reduced1
import N6Reduced2
import N6Reduced3
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_200_17 : a k 17*normalRep k 200=(-normalRep k 302) + normalRep k 304 := by
  change a k 17*walk k 39 [59, 50]=(-walk k 39 [57, 5, 63]) + walk k 39 [58, 34, 63]
  rw [← walk_snoc]
  exact Universal.mul_reduced_91 (a k) (relation_zero k) (e k 39)
lemma arrow_span_200 (b : Fin 75) : a k b*normalRep k 200 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_200_17 k]
      exact (normalSpan k).add_mem ((normalSpan k).smul_mem (-1:k) (normal_mem k 302)) (normal_mem k 304)
  · rw [show a k b*normalRep k 200=0 from arrow_incompatible k b 39 16 [59, 50] (normal_endpoints 200) h]
    exact Submodule.zero_mem _
lemma extension_201_54 : a k 54*normalRep k 201=normalRep k 306 := by
  exact (walk_snoc k 40 [60, 4] 54).symm
lemma extension_201_55 : a k 55*normalRep k 201=0 := by
  change a k 55*walk k 40 [60, 4]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_44 (a k) (relation_zero k) (e k 40)
lemma extension_201_56 : a k 56*normalRep k 201=normalRep k 307 := by
  exact (walk_snoc k 40 [60, 4] 56).symm
lemma arrow_span_201 (b : Fin 75) : a k b*normalRep k 201 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_201_54 k]
      exact normal_mem k 306
    · rw [extension_201_55 k]
      exact Submodule.zero_mem _
    · rw [extension_201_56 k]
      exact normal_mem k 307
  · rw [show a k b*normalRep k 201=0 from arrow_incompatible k b 40 38 [60, 4] (normal_endpoints 201) h]
    exact Submodule.zero_mem _
lemma extension_202_54 : a k 54*normalRep k 202=0 := by
  change a k 54*walk k 40 [61, 35]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_76 (a k) (relation_zero k) (e k 40)
lemma extension_202_55 : a k 55*normalRep k 202=normalRep k 308 := by
  exact (walk_snoc k 40 [61, 35] 55).symm
lemma extension_202_56 : a k 56*normalRep k 202=normalRep k 309 := by
  exact (walk_snoc k 40 [61, 35] 56).symm
lemma arrow_span_202 (b : Fin 75) : a k b*normalRep k 202 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_202_54 k]
      exact Submodule.zero_mem _
    · rw [extension_202_55 k]
      exact normal_mem k 308
    · rw [extension_202_56 k]
      exact normal_mem k 309
  · rw [show a k b*normalRep k 202=0 from arrow_incompatible k b 40 38 [61, 35] (normal_endpoints 202) h]
    exact Submodule.zero_mem _
lemma extension_203_41 : a k 41*normalRep k 203=normalRep k 307 + normalRep k 309 := by
  change a k 41*walk k 40 [62, 52]=walk k 40 [60, 4, 56] + walk k 40 [61, 35, 56]
  rw [← walk_snoc]
  exact Universal.mul_reduced_93 (a k) (relation_zero k) (e k 40)
lemma extension_203_42 : a k 42*normalRep k 203=normalRep k 310 := by
  exact (walk_snoc k 40 [62, 52] 42).symm
lemma arrow_span_203 (b : Fin 75) : a k b*normalRep k 203 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_203_41 k]
      exact (normalSpan k).add_mem (normal_mem k 307) (normal_mem k 309)
    · rw [extension_203_42 k]
      exact normal_mem k 310
  · rw [show a k b*normalRep k 203=0 from arrow_incompatible k b 40 31 [62, 52] (normal_endpoints 203) h]
    exact Submodule.zero_mem _
lemma extension_204_30 : a k 30*normalRep k 204=normalRep k 311 := by
  exact (walk_snoc k 41 [63, 20] 30).symm
lemma extension_204_31 : a k 31*normalRep k 204=0 := by
  change a k 31*walk k 41 [63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_59 (a k) (relation_zero k) (e k 41)
lemma arrow_span_204 (b : Fin 75) : a k b*normalRep k 204 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_204_30 k]
      exact normal_mem k 311
    · rw [extension_204_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 204=0 from arrow_incompatible k b 41 24 [63, 20] (normal_endpoints 204) h]
    exact Submodule.zero_mem _
lemma extension_205_69 : a k 69*normalRep k 205=normalRep k 312 := by
  exact (walk_snoc k 41 [63, 21] 69).symm
lemma extension_205_70 : a k 70*normalRep k 205=normalRep k 313 := by
  exact (walk_snoc k 41 [63, 21] 70).symm
lemma extension_205_71 : a k 71*normalRep k 205=0 := by
  change a k 71*walk k 41 [63, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_61 (a k) (relation_zero k) (e k 41)
lemma arrow_span_205 (b : Fin 75) : a k b*normalRep k 205 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_205_69 k]
      exact normal_mem k 312
    · rw [extension_205_70 k]
      exact normal_mem k 313
    · rw [extension_205_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 205=0 from arrow_incompatible k b 41 43 [63, 21] (normal_endpoints 205) h]
    exact Submodule.zero_mem _
lemma extension_206_69 : a k 69*normalRep k 206=0 := by
  change a k 69*walk k 41 [64, 36]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_77 (a k) (relation_zero k) (e k 41)
lemma extension_206_70 : a k 70*normalRep k 206=normalRep k 313 := by
  change a k 70*walk k 41 [64, 36]=walk k 41 [63, 21, 70]
  rw [← walk_snoc]
  exact Universal.mul_reduced_89 (a k) (relation_zero k) (e k 41)
lemma extension_206_71 : a k 71*normalRep k 206=normalRep k 314 := by
  exact (walk_snoc k 41 [64, 36] 71).symm
lemma arrow_span_206 (b : Fin 75) : a k b*normalRep k 206 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_206_69 k]
      exact Submodule.zero_mem _
    · rw [extension_206_70 k]
      exact normal_mem k 313
    · rw [extension_206_71 k]
      exact normal_mem k 314
  · rw [show a k b*normalRep k 206=0 from arrow_incompatible k b 41 43 [64, 36] (normal_endpoints 206) h]
    exact Submodule.zero_mem _
lemma extension_207_18 : a k 18*normalRep k 207=normalRep k 315 := by
  exact (walk_snoc k 42 [66, 24] 18).symm
lemma extension_207_19 : a k 19*normalRep k 207=normalRep k 316 := by
  exact (walk_snoc k 42 [66, 24] 19).symm
lemma arrow_span_207 (b : Fin 75) : a k b*normalRep k 207 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_207_18 k]
      exact normal_mem k 315
    · rw [extension_207_19 k]
      exact normal_mem k 316
  · rw [show a k b*normalRep k 207=0 from arrow_incompatible k b 42 17 [66, 24] (normal_endpoints 207) h]
    exact Submodule.zero_mem _
lemma extension_208_60 : a k 60*normalRep k 208=normalRep k 317 := by
  exact (walk_snoc k 42 [66, 25] 60).symm
lemma extension_208_61 : a k 61*normalRep k 208=0 := by
  change a k 61*walk k 42 [66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_65 (a k) (relation_zero k) (e k 42)
lemma extension_208_62 : a k 62*normalRep k 208=normalRep k 316 := by
  change a k 62*walk k 42 [66, 25]=walk k 42 [66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_67 (a k) (relation_zero k) (e k 42)
lemma arrow_span_208 (b : Fin 75) : a k b*normalRep k 208 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_208_60 k]
      exact normal_mem k 317
    · rw [extension_208_61 k]
      exact Submodule.zero_mem _
    · rw [extension_208_62 k]
      exact normal_mem k 316
  · rw [show a k b*normalRep k 208=0 from arrow_incompatible k b 42 40 [66, 25] (normal_endpoints 208) h]
    exact Submodule.zero_mem _
lemma extension_209_60 : a k 60*normalRep k 209=0 := by
  change a k 60*walk k 42 [67, 32]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_72 (a k) (relation_zero k) (e k 42)
lemma extension_209_61 : a k 61*normalRep k 209=normalRep k 318 := by
  exact (walk_snoc k 42 [67, 32] 61).symm
lemma extension_209_62 : a k 62*normalRep k 209=normalRep k 319 := by
  exact (walk_snoc k 42 [67, 32] 62).symm
lemma arrow_span_209 (b : Fin 75) : a k b*normalRep k 209 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_209_60 k]
      exact Submodule.zero_mem _
    · rw [extension_209_61 k]
      exact normal_mem k 318
    · rw [extension_209_62 k]
      exact normal_mem k 319
  · rw [show a k b*normalRep k 209=0 from arrow_incompatible k b 42 40 [67, 32] (normal_endpoints 209) h]
    exact Submodule.zero_mem _
lemma extension_210_12 : a k 12*normalRep k 210=normalRep k 318 := by
  change a k 12*walk k 42 [68, 39]=walk k 42 [67, 32, 61]
  rw [← walk_snoc]
  exact Universal.mul_reduced_80 (a k) (relation_zero k) (e k 42)
lemma arrow_span_210 (b : Fin 75) : a k b*normalRep k 210 ∈ normalSpan k := by
  by_cases h : arrowSource b=12
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [12] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_210_12 k]
      exact normal_mem k 318
  · rw [show a k b*normalRep k 210=0 from arrow_incompatible k b 42 12 [68, 39] (normal_endpoints 210) h]
    exact Submodule.zero_mem _
lemma extension_211_66 : a k 66*normalRep k 211=normalRep k 320 := by
  exact (walk_snoc k 43 [69, 8] 66).symm
lemma extension_211_67 : a k 67*normalRep k 211=0 := by
  change a k 67*walk k 43 [69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_49 (a k) (relation_zero k) (e k 43)
lemma extension_211_68 : a k 68*normalRep k 211=normalRep k 321 := by
  exact (walk_snoc k 43 [69, 8] 68).symm
lemma arrow_span_211 (b : Fin 75) : a k b*normalRep k 211 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_211_66 k]
      exact normal_mem k 320
    · rw [extension_211_67 k]
      exact Submodule.zero_mem _
    · rw [extension_211_68 k]
      exact normal_mem k 321
  · rw [show a k b*normalRep k 211=0 from arrow_incompatible k b 43 42 [69, 8] (normal_endpoints 211) h]
    exact Submodule.zero_mem _
lemma extension_212_3 : a k 3*normalRep k 212=normalRep k 322 := by
  exact (walk_snoc k 43 [70, 22] 3).symm
lemma arrow_span_212 (b : Fin 75) : a k b*normalRep k 212 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_212_3 k]
      exact normal_mem k 322
  · rw [show a k b*normalRep k 212=0 from arrow_incompatible k b 43 3 [70, 22] (normal_endpoints 212) h]
    exact Submodule.zero_mem _
lemma extension_213_66 : a k 66*normalRep k 213=normalRep k 323 := by
  exact (walk_snoc k 43 [70, 23] 66).symm
lemma extension_213_67 : a k 67*normalRep k 213=0 := by
  change a k 67*walk k 43 [70, 23]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_62 (a k) (relation_zero k) (e k 43)
lemma extension_213_68 : a k 68*normalRep k 213=(-normalRep k 322) := by
  change a k 68*walk k 43 [70, 23]=(-walk k 43 [70, 22, 3])
  rw [← walk_snoc]
  exact Universal.mul_reduced_63 (a k) (relation_zero k) (e k 43)
lemma arrow_span_213 (b : Fin 75) : a k b*normalRep k 213 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_213_66 k]
      exact normal_mem k 323
    · rw [extension_213_67 k]
      exact Submodule.zero_mem _
    · rw [extension_213_68 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 322)
  · rw [show a k b*normalRep k 213=0 from arrow_incompatible k b 43 42 [70, 23] (normal_endpoints 213) h]
    exact Submodule.zero_mem _
lemma extension_214_37 : a k 37*normalRep k 214=normalRep k 320 + normalRep k 323 := by
  change a k 37*walk k 43 [71, 72]=walk k 43 [69, 8, 66] + walk k 43 [70, 23, 66]
  rw [← walk_snoc]
  exact Universal.mul_reduced_113 (a k) (relation_zero k) (e k 43)
lemma extension_214_38 : a k 38*normalRep k 214=normalRep k 324 := by
  exact (walk_snoc k 43 [71, 72] 38).symm
lemma arrow_span_214 (b : Fin 75) : a k b*normalRep k 214 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_214_37 k]
      exact (normalSpan k).add_mem (normal_mem k 320) (normal_mem k 323)
    · rw [extension_214_38 k]
      exact normal_mem k 324
  · rw [show a k b*normalRep k 214=0 from arrow_incompatible k b 43 29 [71, 72] (normal_endpoints 214) h]
    exact Submodule.zero_mem _
lemma extension_215_24 : a k 24*normalRep k 215=normalRep k 325 := by
  exact (walk_snoc k 44 [72, 37] 24).symm
lemma extension_215_25 : a k 25*normalRep k 215=normalRep k 326 := by
  exact (walk_snoc k 44 [72, 37] 25).symm
lemma arrow_span_215 (b : Fin 75) : a k b*normalRep k 215 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_215_24 k]
      exact normal_mem k 325
    · rw [extension_215_25 k]
      exact normal_mem k 326
  · rw [show a k b*normalRep k 215=0 from arrow_incompatible k b 44 20 [72, 37] (normal_endpoints 215) h]
    exact Submodule.zero_mem _
lemma extension_216_28 : a k 28*normalRep k 216=normalRep k 327 := by
  exact (walk_snoc k 44 [72, 38] 28).symm
lemma extension_216_29 : a k 29*normalRep k 216=normalRep k 325 := by
  change a k 29*walk k 44 [72, 38]=walk k 44 [72, 37, 24]
  rw [← walk_snoc]
  exact Universal.mul_reduced_78 (a k) (relation_zero k) (e k 44)
lemma arrow_span_216 (b : Fin 75) : a k b*normalRep k 216 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_216_28 k]
      exact normal_mem k 327
    · rw [extension_216_29 k]
      exact normal_mem k 325
  · rw [show a k b*normalRep k 216=0 from arrow_incompatible k b 44 23 [72, 38] (normal_endpoints 216) h]
    exact Submodule.zero_mem _
lemma extension_217_32 : a k 32*normalRep k 217=normalRep k 328 := by
  exact (walk_snoc k 44 [73, 67] 32).symm
lemma arrow_span_217 (b : Fin 75) : a k b*normalRep k 217 ∈ normalSpan k := by
  by_cases h : arrowSource b=25
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [32] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_217_32 k]
      exact normal_mem k 328
  · rw [show a k b*normalRep k 217=0 from arrow_incompatible k b 44 25 [73, 67] (normal_endpoints 217) h]
    exact Submodule.zero_mem _
lemma extension_218_39 : a k 39*normalRep k 218=normalRep k 329 := by
  exact (walk_snoc k 44 [73, 68] 39).symm
lemma extension_218_40 : a k 40*normalRep k 218=(-normalRep k 326) + normalRep k 328 := by
  change a k 40*walk k 44 [73, 68]=(-walk k 44 [72, 37, 25]) + walk k 44 [73, 67, 32]
  rw [← walk_snoc]
  exact Universal.mul_reduced_108 (a k) (relation_zero k) (e k 44)
lemma arrow_span_218 (b : Fin 75) : a k b*normalRep k 218 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_218_39 k]
      exact normal_mem k 329
    · rw [extension_218_40 k]
      exact (normalSpan k).add_mem ((normalSpan k).smul_mem (-1:k) (normal_mem k 326)) (normal_mem k 328)
  · rw [show a k b*normalRep k 218=0 from arrow_incompatible k b 44 30 [73, 68] (normal_endpoints 218) h]
    exact Submodule.zero_mem _
lemma extension_219_11 : a k 11*normalRep k 219=normalRep k 330 := by
  exact (walk_snoc k 45 [74, 10] 11).symm
lemma arrow_span_219 (b : Fin 75) : a k b*normalRep k 219 ∈ normalSpan k := by
  by_cases h : arrowSource b=11
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [11] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_219_11 k]
      exact normal_mem k 330
  · rw [show a k b*normalRep k 219=0 from arrow_incompatible k b 45 11 [74, 10] (normal_endpoints 219) h]
    exact Submodule.zero_mem _
lemma extension_220_20 : a k 20*normalRep k 220=normalRep k 331 := by
  exact (walk_snoc k 1 [1, 34, 63] 20).symm
lemma extension_220_21 : a k 21*normalRep k 220=0 := by
  change a k 21*walk k 1 [1, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_195 (a k) (relation_zero k) (e k 1)
lemma arrow_span_220 (b : Fin 75) : a k b*normalRep k 220 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_220_20 k]
      exact normal_mem k 331
    · rw [extension_220_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 220=0 from arrow_incompatible k b 1 18 [1, 34, 63] (normal_endpoints 220) h]
    exact Submodule.zero_mem _
lemma extension_221_4 : a k 4*normalRep k 221=normalRep k 332 := by
  exact (walk_snoc k 3 [3, 40, 60] 4).symm
lemma arrow_span_221 (b : Fin 75) : a k b*normalRep k 221 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_221_4 k]
      exact normal_mem k 332
  · rw [show a k b*normalRep k 221=0 from arrow_incompatible k b 3 4 [3, 40, 60] (normal_endpoints 221) h]
    exact Submodule.zero_mem _
lemma extension_222_52 : a k 52*normalRep k 222=normalRep k 333 := by
  exact (walk_snoc k 3 [3, 40, 62] 52).symm
lemma extension_222_53 : a k 53*normalRep k 222=normalRep k 332 := by
  change a k 53*walk k 3 [3, 40, 62]=walk k 3 [3, 40, 60, 4]
  rw [← walk_snoc]
  exact Universal.mul_reduced_191 (a k) (relation_zero k) (e k 3)
lemma arrow_span_222 (b : Fin 75) : a k b*normalRep k 222 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_222_52 k]
      exact normal_mem k 333
    · rw [extension_222_53 k]
      exact normal_mem k 332
  · rw [show a k b*normalRep k 222=0 from arrow_incompatible k b 3 37 [3, 40, 62] (normal_endpoints 222) h]
    exact Submodule.zero_mem _
lemma extension_223_1 : a k 1*normalRep k 223=normalRep k 334 := by
  exact (walk_snoc k 4 [4, 54, 15] 1).symm
lemma arrow_span_223 (b : Fin 75) : a k b*normalRep k 223 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_223_1 k]
      exact normal_mem k 334
  · rw [show a k b*normalRep k 223=0 from arrow_incompatible k b 4 1 [4, 54, 15] (normal_endpoints 223) h]
    exact Submodule.zero_mem _
lemma extension_224_57 : a k 57*normalRep k 224=normalRep k 335 := by
  exact (walk_snoc k 4 [4, 54, 16] 57).symm
lemma extension_224_58 : a k 58*normalRep k 224=normalRep k 334 := by
  change a k 58*walk k 4 [4, 54, 16]=walk k 4 [4, 54, 15, 1]
  rw [← walk_snoc]
  exact Universal.mul_reduced_128 (a k) (relation_zero k) (e k 4)
lemma extension_224_59 : a k 59*normalRep k 224=0 := by
  change a k 59*walk k 4 [4, 54, 16]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_130 (a k) (relation_zero k) (e k 4)
lemma arrow_span_224 (b : Fin 75) : a k b*normalRep k 224 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_224_57 k]
      exact normal_mem k 335
    · rw [extension_224_58 k]
      exact normal_mem k 334
    · rw [extension_224_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 224=0 from arrow_incompatible k b 4 39 [4, 54, 16] (normal_endpoints 224) h]
    exact Submodule.zero_mem _
lemma extension_225_30 : a k 30*normalRep k 225=normalRep k 336 := by
  exact (walk_snoc k 5 [5, 63, 20] 30).symm
lemma extension_225_31 : a k 31*normalRep k 225=0 := by
  change a k 31*walk k 5 [5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_138 (a k) (relation_zero k) (e k 5)
lemma arrow_span_225 (b : Fin 75) : a k b*normalRep k 225 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_225_30 k]
      exact normal_mem k 336
    · rw [extension_225_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 225=0 from arrow_incompatible k b 5 24 [5, 63, 20] (normal_endpoints 225) h]
    exact Submodule.zero_mem _
lemma extension_226_20 : a k 20*normalRep k 226=0 := by
  change a k 20*walk k 6 [6, 7, 17]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_132 (a k) (relation_zero k) (e k 6)
lemma extension_226_21 : a k 21*normalRep k 226=normalRep k 337 := by
  exact (walk_snoc k 6 [6, 7, 17] 21).symm
lemma arrow_span_226 (b : Fin 75) : a k b*normalRep k 226 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_226_20 k]
      exact Submodule.zero_mem _
    · rw [extension_226_21 k]
      exact normal_mem k 337
  · rw [show a k b*normalRep k 226=0 from arrow_incompatible k b 6 18 [6, 7, 17] (normal_endpoints 226) h]
    exact Submodule.zero_mem _
lemma extension_227_69 : a k 69*normalRep k 227=normalRep k 338 := by
  exact (walk_snoc k 7 [7, 17, 21] 69).symm
lemma extension_227_70 : a k 70*normalRep k 227=normalRep k 339 := by
  exact (walk_snoc k 7 [7, 17, 21] 70).symm
lemma extension_227_71 : a k 71*normalRep k 227=0 := by
  change a k 71*walk k 7 [7, 17, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_140 (a k) (relation_zero k) (e k 7)
lemma arrow_span_227 (b : Fin 75) : a k b*normalRep k 227 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_227_69 k]
      exact normal_mem k 338
    · rw [extension_227_70 k]
      exact normal_mem k 339
    · rw [extension_227_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 227=0 from arrow_incompatible k b 7 43 [7, 17, 21] (normal_endpoints 227) h]
    exact Submodule.zero_mem _
lemma extension_228_18 : a k 18*normalRep k 228=normalRep k 340 := by
  exact (walk_snoc k 8 [8, 66, 24] 18).symm
lemma extension_228_19 : a k 19*normalRep k 228=normalRep k 341 := by
  exact (walk_snoc k 8 [8, 66, 24] 19).symm
lemma arrow_span_228 (b : Fin 75) : a k b*normalRep k 228 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_228_18 k]
      exact normal_mem k 340
    · rw [extension_228_19 k]
      exact normal_mem k 341
  · rw [show a k b*normalRep k 228=0 from arrow_incompatible k b 8 17 [8, 66, 24] (normal_endpoints 228) h]
    exact Submodule.zero_mem _
lemma extension_229_60 : a k 60*normalRep k 229=normalRep k 342 := by
  exact (walk_snoc k 8 [8, 66, 25] 60).symm
lemma extension_229_61 : a k 61*normalRep k 229=0 := by
  change a k 61*walk k 8 [8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_146 (a k) (relation_zero k) (e k 8)
lemma extension_229_62 : a k 62*normalRep k 229=normalRep k 341 := by
  change a k 62*walk k 8 [8, 66, 25]=walk k 8 [8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_149 (a k) (relation_zero k) (e k 8)
lemma arrow_span_229 (b : Fin 75) : a k b*normalRep k 229 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_229_60 k]
      exact normal_mem k 342
    · rw [extension_229_61 k]
      exact Submodule.zero_mem _
    · rw [extension_229_62 k]
      exact normal_mem k 341
  · rw [show a k b*normalRep k 229=0 from arrow_incompatible k b 8 40 [8, 66, 25] (normal_endpoints 229) h]
    exact Submodule.zero_mem _
lemma extension_230_57 : a k 57*normalRep k 230=normalRep k 343 := by
  exact (walk_snoc k 9 [9, 41, 44] 57).symm
lemma extension_230_58 : a k 58*normalRep k 230=normalRep k 344 := by
  exact (walk_snoc k 9 [9, 41, 44] 58).symm
lemma extension_230_59 : a k 59*normalRep k 230=0 := by
  change a k 59*walk k 9 [9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_169 (a k) (relation_zero k) (e k 9)
lemma arrow_span_230 (b : Fin 75) : a k b*normalRep k 230 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_230_57 k]
      exact normal_mem k 343
    · rw [extension_230_58 k]
      exact normal_mem k 344
    · rw [extension_230_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 230=0 from arrow_incompatible k b 9 39 [9, 41, 44] (normal_endpoints 230) h]
    exact Submodule.zero_mem _
lemma extension_231_30 : a k 30*normalRep k 231=0 := by
  change a k 30*walk k 10 [10, 11, 26]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_152 (a k) (relation_zero k) (e k 10)
lemma extension_231_31 : a k 31*normalRep k 231=normalRep k 345 := by
  exact (walk_snoc k 10 [10, 11, 26] 31).symm
lemma arrow_span_231 (b : Fin 75) : a k b*normalRep k 231 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_231_30 k]
      exact Submodule.zero_mem _
    · rw [extension_231_31 k]
      exact normal_mem k 345
  · rw [show a k b*normalRep k 231=0 from arrow_incompatible k b 10 24 [10, 11, 26] (normal_endpoints 231) h]
    exact Submodule.zero_mem _
lemma extension_232_72 : a k 72*normalRep k 232=0 := by
  change a k 72*walk k 11 [11, 26, 31]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_156 (a k) (relation_zero k) (e k 11)
lemma extension_232_73 : a k 73*normalRep k 232=normalRep k 346 := by
  exact (walk_snoc k 11 [11, 26, 31] 73).symm
lemma arrow_span_232 (b : Fin 75) : a k b*normalRep k 232 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_232_72 k]
      exact Submodule.zero_mem _
    · rw [extension_232_73 k]
      exact normal_mem k 346
  · rw [show a k b*normalRep k 232=0 from arrow_incompatible k b 11 44 [11, 26, 31] (normal_endpoints 232) h]
    exact Submodule.zero_mem _
lemma extension_233_27 : a k 27*normalRep k 233=normalRep k 347 := by
  exact (walk_snoc k 12 [12, 35, 55] 27).symm
lemma arrow_span_233 (b : Fin 75) : a k b*normalRep k 233 ∈ normalSpan k := by
  by_cases h : arrowSource b=22
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [27] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_233_27 k]
      exact normal_mem k 347
  · rw [show a k b*normalRep k 233=0 from arrow_incompatible k b 12 22 [12, 35, 55] (normal_endpoints 233) h]
    exact Submodule.zero_mem _
lemma extension_234_43 : a k 43*normalRep k 234=normalRep k 348 := by
  exact (walk_snoc k 12 [12, 35, 56] 43).symm
lemma extension_234_44 : a k 44*normalRep k 234=normalRep k 347 := by
  change a k 44*walk k 12 [12, 35, 56]=walk k 12 [12, 35, 55, 27]
  rw [← walk_snoc]
  exact Universal.mul_reduced_184 (a k) (relation_zero k) (e k 12)
lemma arrow_span_234 (b : Fin 75) : a k b*normalRep k 234 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_234_43 k]
      exact normal_mem k 348
    · rw [extension_234_44 k]
      exact normal_mem k 347
  · rw [show a k b*normalRep k 234=0 from arrow_incompatible k b 12 32 [12, 35, 56] (normal_endpoints 234) h]
    exact Submodule.zero_mem _
lemma extension_235_8 : a k 8*normalRep k 235=normalRep k 349 := by
  exact (walk_snoc k 13 [13, 49, 69] 8).symm
lemma arrow_span_235 (b : Fin 75) : a k b*normalRep k 235 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_235_8 k]
      exact normal_mem k 349
  · rw [show a k b*normalRep k 235=0 from arrow_incompatible k b 13 8 [13, 49, 69] (normal_endpoints 235) h]
    exact Submodule.zero_mem _
lemma extension_236_72 : a k 72*normalRep k 236=normalRep k 350 := by
  exact (walk_snoc k 13 [13, 49, 71] 72).symm
lemma extension_236_73 : a k 73*normalRep k 236=normalRep k 349 := by
  change a k 73*walk k 13 [13, 49, 71]=walk k 13 [13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_202 (a k) (relation_zero k) (e k 13)
lemma arrow_span_236 (b : Fin 75) : a k b*normalRep k 236 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_236_72 k]
      exact normal_mem k 350
    · rw [extension_236_73 k]
      exact normal_mem k 349
  · rw [show a k b*normalRep k 236=0 from arrow_incompatible k b 13 44 [13, 49, 71] (normal_endpoints 236) h]
    exact Submodule.zero_mem _
lemma extension_237_43 : a k 43*normalRep k 237=0 := by
  change a k 43*walk k 14 [14, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_166 (a k) (relation_zero k) (e k 14)
lemma extension_237_44 : a k 44*normalRep k 237=normalRep k 351 := by
  exact (walk_snoc k 14 [14, 9, 41] 44).symm
lemma arrow_span_237 (b : Fin 75) : a k b*normalRep k 237 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_237_43 k]
      exact Submodule.zero_mem _
    · rw [extension_237_44 k]
      exact normal_mem k 351
  · rw [show a k b*normalRep k 237=0 from arrow_incompatible k b 14 32 [14, 9, 41] (normal_endpoints 237) h]
    exact Submodule.zero_mem _
lemma extension_238_63 : a k 63*normalRep k 238=normalRep k 352 := by
  exact (walk_snoc k 15 [15, 1, 34] 63).symm
lemma extension_238_64 : a k 64*normalRep k 238=0 := by
  change a k 64*walk k 15 [15, 1, 34]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_115 (a k) (relation_zero k) (e k 15)
lemma extension_238_65 : a k 65*normalRep k 238=0 := by
  change a k 65*walk k 15 [15, 1, 34]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_121 (a k) (relation_zero k) (e k 15)
lemma arrow_span_238 (b : Fin 75) : a k b*normalRep k 238 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_238_63 k]
      exact normal_mem k 352
    · rw [extension_238_64 k]
      exact Submodule.zero_mem _
    · rw [extension_238_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 238=0 from arrow_incompatible k b 15 41 [15, 1, 34] (normal_endpoints 238) h]
    exact Submodule.zero_mem _
lemma extension_239_8 : a k 8*normalRep k 239=normalRep k 353 := by
  exact (walk_snoc k 16 [17, 21, 69] 8).symm
lemma arrow_span_239 (b : Fin 75) : a k b*normalRep k 239 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_239_8 k]
      exact normal_mem k 353
  · rw [show a k b*normalRep k 239=0 from arrow_incompatible k b 16 8 [17, 21, 69] (normal_endpoints 239) h]
    exact Submodule.zero_mem _
lemma extension_240_22 : a k 22*normalRep k 240=normalRep k 354 := by
  exact (walk_snoc k 16 [17, 21, 70] 22).symm
lemma extension_240_23 : a k 23*normalRep k 240=(-normalRep k 353) := by
  change a k 23*walk k 16 [17, 21, 70]=(-walk k 16 [17, 21, 69, 8])
  rw [← walk_snoc]
  exact Universal.mul_reduced_203 (a k) (relation_zero k) (e k 16)
lemma arrow_span_240 (b : Fin 75) : a k b*normalRep k 240 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_240_22 k]
      exact normal_mem k 354
    · rw [extension_240_23 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 353)
  · rw [show a k b*normalRep k 240=0 from arrow_incompatible k b 16 19 [17, 21, 70] (normal_endpoints 240) h]
    exact Submodule.zero_mem _
lemma extension_241_43 : a k 43*normalRep k 241=0 := by
  change a k 43*walk k 17 [18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_167 (a k) (relation_zero k) (e k 17)
lemma extension_241_44 : a k 44*normalRep k 241=normalRep k 355 := by
  exact (walk_snoc k 17 [18, 9, 41] 44).symm
lemma arrow_span_241 (b : Fin 75) : a k b*normalRep k 241 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_241_43 k]
      exact Submodule.zero_mem _
    · rw [extension_241_44 k]
      exact normal_mem k 355
  · rw [show a k b*normalRep k 241=0 from arrow_incompatible k b 17 32 [18, 9, 41] (normal_endpoints 241) h]
    exact Submodule.zero_mem _
lemma extension_242_15 : a k 15*normalRep k 242=normalRep k 356 := by
  exact (walk_snoc k 17 [19, 53, 54] 15).symm
lemma extension_242_16 : a k 16*normalRep k 242=normalRep k 355 := by
  change a k 16*walk k 17 [19, 53, 54]=walk k 17 [18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_185 (a k) (relation_zero k) (e k 17)
lemma arrow_span_242 (b : Fin 75) : a k b*normalRep k 242 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_242_15 k]
      exact normal_mem k 356
    · rw [extension_242_16 k]
      exact normal_mem k 355
  · rw [show a k b*normalRep k 242=0 from arrow_incompatible k b 17 15 [19, 53, 54] (normal_endpoints 242) h]
    exact Submodule.zero_mem _
lemma extension_243_0 : a k 0*normalRep k 243=normalRep k 357 := by
  exact (walk_snoc k 18 [20, 30, 2] 0).symm
lemma arrow_span_243 (b : Fin 75) : a k b*normalRep k 243 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_243_0 k]
      exact normal_mem k 357
  · rw [show a k b*normalRep k 243=0 from arrow_incompatible k b 18 0 [20, 30, 2] (normal_endpoints 243) h]
    exact Submodule.zero_mem _
lemma extension_244_66 : a k 66*normalRep k 244=normalRep k 358 := by
  exact (walk_snoc k 18 [21, 69, 8] 66).symm
lemma extension_244_67 : a k 67*normalRep k 244=0 := by
  change a k 67*walk k 18 [21, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_124 (a k) (relation_zero k) (e k 18)
lemma extension_244_68 : a k 68*normalRep k 244=normalRep k 359 := by
  exact (walk_snoc k 18 [21, 69, 8] 68).symm
lemma arrow_span_244 (b : Fin 75) : a k b*normalRep k 244 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_244_66 k]
      exact normal_mem k 358
    · rw [extension_244_67 k]
      exact Submodule.zero_mem _
    · rw [extension_244_68 k]
      exact normal_mem k 359
  · rw [show a k b*normalRep k 244=0 from arrow_incompatible k b 18 42 [21, 69, 8] (normal_endpoints 244) h]
    exact Submodule.zero_mem _
lemma extension_245_3 : a k 3*normalRep k 245=normalRep k 359 := by
  change a k 3*walk k 18 [21, 70, 22]=walk k 18 [21, 69, 8, 68]
  rw [← walk_snoc]
  exact Universal.mul_reduced_144 (a k) (relation_zero k) (e k 18)
lemma arrow_span_245 (b : Fin 75) : a k b*normalRep k 245 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_245_3 k]
      exact normal_mem k 359
  · rw [show a k b*normalRep k 245=0 from arrow_incompatible k b 18 3 [21, 70, 22] (normal_endpoints 245) h]
    exact Submodule.zero_mem _
lemma extension_246_60 : a k 60*normalRep k 246=normalRep k 360 := by
  exact (walk_snoc k 19 [22, 3, 40] 60).symm
lemma extension_246_61 : a k 61*normalRep k 246=0 := by
  change a k 61*walk k 19 [22, 3, 40]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_147 (a k) (relation_zero k) (e k 19)
lemma extension_246_62 : a k 62*normalRep k 246=normalRep k 361 := by
  exact (walk_snoc k 19 [22, 3, 40] 62).symm
lemma arrow_span_246 (b : Fin 75) : a k b*normalRep k 246 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_246_60 k]
      exact normal_mem k 360
    · rw [extension_246_61 k]
      exact Submodule.zero_mem _
    · rw [extension_246_62 k]
      exact normal_mem k 361
  · rw [show a k b*normalRep k 246=0 from arrow_incompatible k b 19 40 [22, 3, 40] (normal_endpoints 246) h]
    exact Submodule.zero_mem _
lemma extension_247_18 : a k 18*normalRep k 247=normalRep k 362 := by
  exact (walk_snoc k 19 [23, 66, 24] 18).symm
lemma extension_247_19 : a k 19*normalRep k 247=normalRep k 361 := by
  change a k 19*walk k 19 [23, 66, 24]=walk k 19 [22, 3, 40, 62]
  rw [← walk_snoc]
  exact Universal.mul_reduced_150 (a k) (relation_zero k) (e k 19)
lemma arrow_span_247 (b : Fin 75) : a k b*normalRep k 247 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_247_18 k]
      exact normal_mem k 362
    · rw [extension_247_19 k]
      exact normal_mem k 361
  · rw [show a k b*normalRep k 247=0 from arrow_incompatible k b 19 17 [23, 66, 24] (normal_endpoints 247) h]
    exact Submodule.zero_mem _
lemma extension_248_41 : a k 41*normalRep k 248=normalRep k 363 := by
  exact (walk_snoc k 20 [24, 18, 9] 41).symm
lemma extension_248_42 : a k 42*normalRep k 248=0 := by
  change a k 42*walk k 20 [24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_126 (a k) (relation_zero k) (e k 20)
lemma arrow_span_248 (b : Fin 75) : a k b*normalRep k 248 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_248_41 k]
      exact normal_mem k 363
    · rw [extension_248_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 248=0 from arrow_incompatible k b 20 31 [24, 18, 9] (normal_endpoints 248) h]
    exact Submodule.zero_mem _
lemma extension_249_54 : a k 54*normalRep k 249=normalRep k 364 := by
  exact (walk_snoc k 20 [24, 19, 53] 54).symm
lemma extension_249_55 : a k 55*normalRep k 249=0 := by
  change a k 55*walk k 20 [24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_117 (a k) (relation_zero k) (e k 20)
lemma extension_249_56 : a k 56*normalRep k 249=normalRep k 363 := by
  change a k 56*walk k 20 [24, 19, 53]=walk k 20 [24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_180 (a k) (relation_zero k) (e k 20)
lemma arrow_span_249 (b : Fin 75) : a k b*normalRep k 249 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_249_54 k]
      exact normal_mem k 364
    · rw [extension_249_55 k]
      exact Submodule.zero_mem _
    · rw [extension_249_56 k]
      exact normal_mem k 363
  · rw [show a k b*normalRep k 249=0 from arrow_incompatible k b 20 38 [24, 19, 53] (normal_endpoints 249) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
