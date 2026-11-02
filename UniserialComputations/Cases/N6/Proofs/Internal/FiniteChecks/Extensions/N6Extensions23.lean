import N6NormalData
import N6Reduced14
import N6Reduced15
import N6Reduced16
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_1150_4 : a k 4*normalRep k 1150=normalRep k 1228 := by
  change a k 4*walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60]=walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_949 (a k) (relation_zero k) (e k 38)
lemma arrow_span_1150 (b : Fin 75) : a k b*normalRep k 1150 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1150_4 k]
      exact normal_mem k 1228
  · rw [show a k b*normalRep k 1150=0 from arrow_incompatible k b 38 4 [55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60] (normal_endpoints 1150) h]
    exact Submodule.zero_mem _
lemma extension_1151_43 : a k 43*normalRep k 1151=0 := by
  change a k 43*walk k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_899 (a k) (relation_zero k) (e k 39)
lemma extension_1151_44 : a k 44*normalRep k 1151=normalRep k 1229 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_1151 (b : Fin 75) : a k b*normalRep k 1151 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1151_43 k]
      exact Submodule.zero_mem _
    · rw [extension_1151_44 k]
      exact normal_mem k 1229
  · rw [show a k b*normalRep k 1151=0 from arrow_incompatible k b 39 32 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 1151) h]
    exact Submodule.zero_mem _
lemma extension_1152_15 : a k 15*normalRep k 1152=normalRep k 1230 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_1152_16 : a k 16*normalRep k 1152=normalRep k 1229 := by
  change a k 16*walk k 39 [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54]=walk k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_942 (a k) (relation_zero k) (e k 39)
lemma arrow_span_1152 (b : Fin 75) : a k b*normalRep k 1152 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1152_15 k]
      exact normal_mem k 1230
    · rw [extension_1152_16 k]
      exact normal_mem k 1229
  · rw [show a k b*normalRep k 1152=0 from arrow_incompatible k b 39 15 [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 1152) h]
    exact Submodule.zero_mem _
lemma arrow_span_1153 (b : Fin 75) : a k b*normalRep k 1153 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1153=0 from arrow_incompatible k b 40 46 [60, 4, 54, 15, 1, 34, 63, 20, 30, 2, 0] (normal_endpoints 1153) h]
    exact Submodule.zero_mem _
lemma extension_1154_24 : a k 24*normalRep k 1154=normalRep k 1231 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 24).symm
lemma extension_1154_25 : a k 25*normalRep k 1154=normalRep k 1232 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 25).symm
lemma arrow_span_1154 (b : Fin 75) : a k b*normalRep k 1154 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1154_24 k]
      exact normal_mem k 1231
    · rw [extension_1154_25 k]
      exact normal_mem k 1232
  · rw [show a k b*normalRep k 1154=0 from arrow_incompatible k b 40 20 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] (normal_endpoints 1154) h]
    exact Submodule.zero_mem _
lemma extension_1155_39 : a k 39*normalRep k 1155=0 := by
  change a k 39*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_890 (a k) (relation_zero k) (e k 40)
lemma extension_1155_40 : a k 40*normalRep k 1155=(-normalRep k 1232) := by
  change a k 40*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=(-walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_954 (a k) (relation_zero k) (e k 40)
lemma arrow_span_1155 (b : Fin 75) : a k b*normalRep k 1155 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1155_39 k]
      exact Submodule.zero_mem _
    · rw [extension_1155_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1232)
  · rw [show a k b*normalRep k 1155=0 from arrow_incompatible k b 40 30 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68] (normal_endpoints 1155) h]
    exact Submodule.zero_mem _
lemma extension_1156_28 : a k 28*normalRep k 1156=normalRep k 1233 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38] 28).symm
lemma extension_1156_29 : a k 29*normalRep k 1156=normalRep k 1231 := by
  change a k 29*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38]=walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]
  rw [← walk_snoc]
  exact Universal.mul_reduced_930 (a k) (relation_zero k) (e k 40)
lemma arrow_span_1156 (b : Fin 75) : a k b*normalRep k 1156 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1156_28 k]
      exact normal_mem k 1233
    · rw [extension_1156_29 k]
      exact normal_mem k 1231
  · rw [show a k b*normalRep k 1156=0 from arrow_incompatible k b 40 23 [61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38] (normal_endpoints 1156) h]
    exact Submodule.zero_mem _
lemma extension_1157_5 : a k 5*normalRep k 1157=normalRep k 1234 := by
  exact (walk_snoc k 41 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1157 (b : Fin 75) : a k b*normalRep k 1157 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1157_5 k]
      exact normal_mem k 1234
  · rw [show a k b*normalRep k 1157=0 from arrow_incompatible k b 41 5 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1157) h]
    exact Submodule.zero_mem _
lemma extension_1158_33 : a k 33*normalRep k 1158=0 := by
  change a k 33*walk k 41 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_885 (a k) (relation_zero k) (e k 41)
lemma extension_1158_34 : a k 34*normalRep k 1158=normalRep k 1234 := by
  change a k 34*walk k 41 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 41 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_947 (a k) (relation_zero k) (e k 41)
lemma arrow_span_1158 (b : Fin 75) : a k b*normalRep k 1158 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1158_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1158_34 k]
      exact normal_mem k 1234
  · rw [show a k b*normalRep k 1158=0 from arrow_incompatible k b 41 26 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1158) h]
    exact Submodule.zero_mem _
lemma extension_1159_2 : a k 2*normalRep k 1159=normalRep k 1235 := by
  exact (walk_snoc k 42 [66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1159 (b : Fin 75) : a k b*normalRep k 1159 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1159_2 k]
      exact normal_mem k 1235
  · rw [show a k b*normalRep k 1159=0 from arrow_incompatible k b 42 2 [66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1159) h]
    exact Submodule.zero_mem _
lemma extension_1160_8 : a k 8*normalRep k 1160=normalRep k 1236 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69] 8).symm
lemma arrow_span_1160 (b : Fin 75) : a k b*normalRep k 1160 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1160_8 k]
      exact normal_mem k 1236
  · rw [show a k b*normalRep k 1160=0 from arrow_incompatible k b 42 8 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69] (normal_endpoints 1160) h]
    exact Submodule.zero_mem _
lemma extension_1161_72 : a k 72*normalRep k 1161=normalRep k 1237 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71] 72).symm
lemma extension_1161_73 : a k 73*normalRep k 1161=normalRep k 1236 := by
  change a k 73*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71]=walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_955 (a k) (relation_zero k) (e k 42)
lemma arrow_span_1161 (b : Fin 75) : a k b*normalRep k 1161 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1161_72 k]
      exact normal_mem k 1237
    · rw [extension_1161_73 k]
      exact normal_mem k 1236
  · rw [show a k b*normalRep k 1161=0 from arrow_incompatible k b 42 44 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71] (normal_endpoints 1161) h]
    exact Submodule.zero_mem _
lemma extension_1162_22 : a k 22*normalRep k 1162=normalRep k 1238 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70] 22).symm
lemma extension_1162_23 : a k 23*normalRep k 1162=normalRep k 1236 := by
  change a k 23*walk k 42 [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70]=walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_956 (a k) (relation_zero k) (e k 42)
lemma arrow_span_1162 (b : Fin 75) : a k b*normalRep k 1162 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1162_22 k]
      exact normal_mem k 1238
    · rw [extension_1162_23 k]
      exact normal_mem k 1236
  · rw [show a k b*normalRep k 1162=0 from arrow_incompatible k b 42 19 [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70] (normal_endpoints 1162) h]
    exact Submodule.zero_mem _
lemma extension_1163_20 : a k 20*normalRep k 1163=normalRep k 1239 := by
  exact (walk_snoc k 43 [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1163_21 : a k 21*normalRep k 1163=0 := by
  change a k 21*walk k 43 [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_951 (a k) (relation_zero k) (e k 43)
lemma arrow_span_1163 (b : Fin 75) : a k b*normalRep k 1163 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1163_20 k]
      exact normal_mem k 1239
    · rw [extension_1163_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1163=0 from arrow_incompatible k b 43 18 [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1163) h]
    exact Submodule.zero_mem _
lemma extension_1164_20 : a k 20*normalRep k 1164=normalRep k 1240 := by
  exact (walk_snoc k 43 [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63] 20).symm
lemma extension_1164_21 : a k 21*normalRep k 1164=0 := by
  change a k 21*walk k 43 [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_952 (a k) (relation_zero k) (e k 43)
lemma arrow_span_1164 (b : Fin 75) : a k b*normalRep k 1164 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1164_20 k]
      exact normal_mem k 1240
    · rw [extension_1164_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1164=0 from arrow_incompatible k b 43 18 [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63] (normal_endpoints 1164) h]
    exact Submodule.zero_mem _
lemma extension_1165_30 : a k 30*normalRep k 1165=normalRep k 1241 := by
  exact (walk_snoc k 44 [72, 37, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1165_31 : a k 31*normalRep k 1165=0 := by
  change a k 31*walk k 44 [72, 37, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_916 (a k) (relation_zero k) (e k 44)
lemma arrow_span_1165 (b : Fin 75) : a k b*normalRep k 1165 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1165_30 k]
      exact normal_mem k 1241
    · rw [extension_1165_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1165=0 from arrow_incompatible k b 44 24 [72, 37, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1165) h]
    exact Submodule.zero_mem _
lemma extension_1166_69 : a k 69*normalRep k 1166=normalRep k 1242 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] 69).symm
lemma extension_1166_70 : a k 70*normalRep k 1166=0 := by
  change a k 70*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_935 (a k) (relation_zero k) (e k 44)
lemma extension_1166_71 : a k 71*normalRep k 1166=normalRep k 1243 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] 71).symm
lemma arrow_span_1166 (b : Fin 75) : a k b*normalRep k 1166 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1166_69 k]
      exact normal_mem k 1242
    · rw [extension_1166_70 k]
      exact Submodule.zero_mem _
    · rw [extension_1166_71 k]
      exact normal_mem k 1243
  · rw [show a k b*normalRep k 1166=0 from arrow_incompatible k b 44 43 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] (normal_endpoints 1166) h]
    exact Submodule.zero_mem _
lemma extension_1167_69 : a k 69*normalRep k 1167=(-normalRep k 1242) := by
  change a k 69*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]=(-walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69])
  rw [← walk_snoc]
  exact Universal.mul_reduced_928 (a k) (relation_zero k) (e k 44)
lemma extension_1167_70 : a k 70*normalRep k 1167=normalRep k 1244 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] 70).symm
lemma extension_1167_71 : a k 71*normalRep k 1167=0 := by
  change a k 71*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_917 (a k) (relation_zero k) (e k 44)
lemma arrow_span_1167 (b : Fin 75) : a k b*normalRep k 1167 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1167_69 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1242)
    · rw [extension_1167_70 k]
      exact normal_mem k 1244
    · rw [extension_1167_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1167=0 from arrow_incompatible k b 44 43 [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] (normal_endpoints 1167) h]
    exact Submodule.zero_mem _
lemma extension_1168_27 : a k 27*normalRep k 1168=normalRep k 1245 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55] 27).symm
lemma arrow_span_1168 (b : Fin 75) : a k b*normalRep k 1168 ∈ normalSpan k := by
  by_cases h : arrowSource b=22
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [27] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1168_27 k]
      exact normal_mem k 1245
  · rw [show a k b*normalRep k 1168=0 from arrow_incompatible k b 45 22 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55] (normal_endpoints 1168) h]
    exact Submodule.zero_mem _
lemma extension_1169_43 : a k 43*normalRep k 1169=normalRep k 1246 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56] 43).symm
lemma extension_1169_44 : a k 44*normalRep k 1169=normalRep k 1245 := by
  change a k 44*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27]
  rw [← walk_snoc]
  exact Universal.mul_reduced_943 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1169 (b : Fin 75) : a k b*normalRep k 1169 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1169_43 k]
      exact normal_mem k 1246
    · rw [extension_1169_44 k]
      exact normal_mem k 1245
  · rw [show a k b*normalRep k 1169=0 from arrow_incompatible k b 45 32 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56] (normal_endpoints 1169) h]
    exact Submodule.zero_mem _
lemma extension_1170_45 : a k 45*normalRep k 1170=normalRep k 1247 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 62, 52, 42] 45).symm
lemma extension_1170_46 : a k 46*normalRep k 1170=normalRep k 1246 := by
  change a k 46*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 62, 52, 42]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43]
  rw [← walk_snoc]
  exact Universal.mul_reduced_931 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1170 (b : Fin 75) : a k b*normalRep k 1170 ∈ normalSpan k := by
  by_cases h : arrowSource b=33
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [45, 46] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1170_45 k]
      exact normal_mem k 1247
    · rw [extension_1170_46 k]
      exact normal_mem k 1246
  · rw [show a k b*normalRep k 1170=0 from arrow_incompatible k b 45 33 [74, 10, 11, 26, 31, 73, 67, 32, 62, 52, 42] (normal_endpoints 1170) h]
    exact Submodule.zero_mem _
lemma extension_1171_0 : a k 0*normalRep k 1171=normalRep k 1248 := by
  exact (walk_snoc k 3 [3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 30, 2] 0).symm
lemma arrow_span_1171 (b : Fin 75) : a k b*normalRep k 1171 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1171_0 k]
      exact normal_mem k 1248
  · rw [show a k b*normalRep k 1171=0 from arrow_incompatible k b 3 0 [3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 30, 2] (normal_endpoints 1171) h]
    exact Submodule.zero_mem _
lemma extension_1172_57 : a k 57*normalRep k 1172=normalRep k 1249 := by
  exact (walk_snoc k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1172_58 : a k 58*normalRep k 1172=normalRep k 1250 := by
  exact (walk_snoc k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1172_59 : a k 59*normalRep k 1172=0 := by
  change a k 59*walk k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_981 (a k) (relation_zero k) (e k 6)
lemma arrow_span_1172 (b : Fin 75) : a k b*normalRep k 1172 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1172_57 k]
      exact normal_mem k 1249
    · rw [extension_1172_58 k]
      exact normal_mem k 1250
    · rw [extension_1172_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1172=0 from arrow_incompatible k b 6 39 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1172) h]
    exact Submodule.zero_mem _
lemma extension_1173_1 : a k 1*normalRep k 1173=normalRep k 1250 := by
  change a k 1*walk k 6 [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_978 (a k) (relation_zero k) (e k 6)
lemma arrow_span_1173 (b : Fin 75) : a k b*normalRep k 1173 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1173_1 k]
      exact normal_mem k 1250
  · rw [show a k b*normalRep k 1173=0 from arrow_incompatible k b 6 1 [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1173) h]
    exact Submodule.zero_mem _
lemma extension_1174_5 : a k 5*normalRep k 1174=normalRep k 1251 := by
  exact (walk_snoc k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1174 (b : Fin 75) : a k b*normalRep k 1174 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1174_5 k]
      exact normal_mem k 1251
  · rw [show a k b*normalRep k 1174=0 from arrow_incompatible k b 7 5 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1174) h]
    exact Submodule.zero_mem _
lemma extension_1175_33 : a k 33*normalRep k 1175=0 := by
  change a k 33*walk k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_959 (a k) (relation_zero k) (e k 7)
lemma extension_1175_34 : a k 34*normalRep k 1175=normalRep k 1251 := by
  change a k 34*walk k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1012 (a k) (relation_zero k) (e k 7)
lemma arrow_span_1175 (b : Fin 75) : a k b*normalRep k 1175 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1175_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1175_34 k]
      exact normal_mem k 1251
  · rw [show a k b*normalRep k 1175=0 from arrow_incompatible k b 7 26 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1175) h]
    exact Submodule.zero_mem _
lemma extension_1176_2 : a k 2*normalRep k 1176=normalRep k 1252 := by
  exact (walk_snoc k 8 [8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1176 (b : Fin 75) : a k b*normalRep k 1176 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1176_2 k]
      exact normal_mem k 1252
  · rw [show a k b*normalRep k 1176=0 from arrow_incompatible k b 8 2 [8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1176) h]
    exact Submodule.zero_mem _
lemma extension_1177_33 : a k 33*normalRep k 1177=normalRep k 1253 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58] 33).symm
lemma extension_1177_34 : a k 34*normalRep k 1177=normalRep k 1254 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58] 34).symm
lemma arrow_span_1177 (b : Fin 75) : a k b*normalRep k 1177 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1177_33 k]
      exact normal_mem k 1253
    · rw [extension_1177_34 k]
      exact normal_mem k 1254
  · rw [show a k b*normalRep k 1177=0 from arrow_incompatible k b 10 26 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58] (normal_endpoints 1177) h]
    exact Submodule.zero_mem _
lemma extension_1178_50 : a k 50*normalRep k 1178=normalRep k 1255 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59] 50).symm
lemma extension_1178_51 : a k 51*normalRep k 1178=normalRep k 1254 := by
  change a k 51*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1013 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1178 (b : Fin 75) : a k b*normalRep k 1178 ∈ normalSpan k := by
  by_cases h : arrowSource b=36
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [50, 51] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1178_50 k]
      exact normal_mem k 1255
    · rw [extension_1178_51 k]
      exact normal_mem k 1254
  · rw [show a k b*normalRep k 1178=0 from arrow_incompatible k b 10 36 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59] (normal_endpoints 1178) h]
    exact Submodule.zero_mem _
lemma extension_1179_7 : a k 7*normalRep k 1179=normalRep k 1255 := by
  change a k 7*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1004 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1179 (b : Fin 75) : a k b*normalRep k 1179 ∈ normalSpan k := by
  by_cases h : arrowSource b=7
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [7] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1179_7 k]
      exact normal_mem k 1255
  · rw [show a k b*normalRep k 1179=0 from arrow_incompatible k b 10 7 [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47] (normal_endpoints 1179) h]
    exact Submodule.zero_mem _
lemma extension_1180_13 : a k 13*normalRep k 1180=normalRep k 1256 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33] 13).symm
lemma arrow_span_1180 (b : Fin 75) : a k b*normalRep k 1180 ∈ normalSpan k := by
  by_cases h : arrowSource b=13
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [13] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1180_13 k]
      exact normal_mem k 1256
  · rw [show a k b*normalRep k 1180=0 from arrow_incompatible k b 11 13 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33] (normal_endpoints 1180) h]
    exact Submodule.zero_mem _
lemma extension_1181_63 : a k 63*normalRep k 1181=normalRep k 1257 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34] 63).symm
lemma extension_1181_64 : a k 64*normalRep k 1181=normalRep k 1258 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34] 64).symm
lemma extension_1181_65 : a k 65*normalRep k 1181=normalRep k 1256 := by
  change a k 65*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34]=walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13]
  rw [← walk_snoc]
  exact Universal.mul_reduced_998 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1181 (b : Fin 75) : a k b*normalRep k 1181 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1181_63 k]
      exact normal_mem k 1257
    · rw [extension_1181_64 k]
      exact normal_mem k 1258
    · rw [extension_1181_65 k]
      exact normal_mem k 1256
  · rw [show a k b*normalRep k 1181=0 from arrow_incompatible k b 11 41 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34] (normal_endpoints 1181) h]
    exact Submodule.zero_mem _
lemma extension_1182_17 : a k 17*normalRep k 1182=normalRep k 1257 := by
  change a k 17*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50]=walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1006 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1182 (b : Fin 75) : a k b*normalRep k 1182 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1182_17 k]
      exact normal_mem k 1257
  · rw [show a k b*normalRep k 1182=0 from arrow_incompatible k b 11 16 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50] (normal_endpoints 1182) h]
    exact Submodule.zero_mem _
lemma extension_1183_18 : a k 18*normalRep k 1183=normalRep k 1259 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 18).symm
lemma extension_1183_19 : a k 19*normalRep k 1183=normalRep k 1260 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 19).symm
lemma arrow_span_1183 (b : Fin 75) : a k b*normalRep k 1183 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1183_18 k]
      exact normal_mem k 1259
    · rw [extension_1183_19 k]
      exact normal_mem k 1260
  · rw [show a k b*normalRep k 1183=0 from arrow_incompatible k b 12 17 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] (normal_endpoints 1183) h]
    exact Submodule.zero_mem _
lemma extension_1184_60 : a k 60*normalRep k 1184=normalRep k 1261 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] 60).symm
lemma extension_1184_61 : a k 61*normalRep k 1184=0 := by
  change a k 61*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_991 (a k) (relation_zero k) (e k 12)
lemma extension_1184_62 : a k 62*normalRep k 1184=normalRep k 1260 := by
  change a k 62*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_993 (a k) (relation_zero k) (e k 12)
lemma arrow_span_1184 (b : Fin 75) : a k b*normalRep k 1184 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1184_60 k]
      exact normal_mem k 1261
    · rw [extension_1184_61 k]
      exact Submodule.zero_mem _
    · rw [extension_1184_62 k]
      exact normal_mem k 1260
  · rw [show a k b*normalRep k 1184=0 from arrow_incompatible k b 12 40 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] (normal_endpoints 1184) h]
    exact Submodule.zero_mem _
lemma extension_1185_14 : a k 14*normalRep k 1185=normalRep k 1259 := by
  change a k 14*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28]=walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18]
  rw [← walk_snoc]
  exact Universal.mul_reduced_996 (a k) (relation_zero k) (e k 12)
lemma arrow_span_1185 (b : Fin 75) : a k b*normalRep k 1185 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1185_14 k]
      exact normal_mem k 1259
  · rw [show a k b*normalRep k 1185=0 from arrow_incompatible k b 12 14 [12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28] (normal_endpoints 1185) h]
    exact Submodule.zero_mem _
lemma extension_1186_63 : a k 63*normalRep k 1186=normalRep k 1262 := by
  exact (walk_snoc k 13 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1186_64 : a k 64*normalRep k 1186=0 := by
  change a k 64*walk k 13 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_962 (a k) (relation_zero k) (e k 13)
lemma extension_1186_65 : a k 65*normalRep k 1186=0 := by
  change a k 65*walk k 13 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_974 (a k) (relation_zero k) (e k 13)
lemma arrow_span_1186 (b : Fin 75) : a k b*normalRep k 1186 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1186_63 k]
      exact normal_mem k 1262
    · rw [extension_1186_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1186_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1186=0 from arrow_incompatible k b 13 41 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1186) h]
    exact Submodule.zero_mem _
lemma extension_1187_63 : a k 63*normalRep k 1187=normalRep k 1263 := by
  exact (walk_snoc k 16 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1187_64 : a k 64*normalRep k 1187=0 := by
  change a k 64*walk k 16 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_963 (a k) (relation_zero k) (e k 16)
lemma extension_1187_65 : a k 65*normalRep k 1187=0 := by
  change a k 65*walk k 16 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_975 (a k) (relation_zero k) (e k 16)
lemma arrow_span_1187 (b : Fin 75) : a k b*normalRep k 1187 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1187_63 k]
      exact normal_mem k 1263
    · rw [extension_1187_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1187_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1187=0 from arrow_incompatible k b 16 41 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1187) h]
    exact Submodule.zero_mem _
lemma extension_1188_20 : a k 20*normalRep k 1188=normalRep k 1264 := by
  exact (walk_snoc k 18 [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1188_21 : a k 21*normalRep k 1188=0 := by
  change a k 21*walk k 18 [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1018 (a k) (relation_zero k) (e k 18)
lemma arrow_span_1188 (b : Fin 75) : a k b*normalRep k 1188 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1188_20 k]
      exact normal_mem k 1264
    · rw [extension_1188_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1188=0 from arrow_incompatible k b 18 18 [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1188) h]
    exact Submodule.zero_mem _
lemma extension_1189_2 : a k 2*normalRep k 1189=normalRep k 1265 := by
  exact (walk_snoc k 19 [22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 30] 2).symm
lemma arrow_span_1189 (b : Fin 75) : a k b*normalRep k 1189 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1189_2 k]
      exact normal_mem k 1265
  · rw [show a k b*normalRep k 1189=0 from arrow_incompatible k b 19 2 [22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 30] (normal_endpoints 1189) h]
    exact Submodule.zero_mem _
lemma arrow_span_1190 (b : Fin 75) : a k b*normalRep k 1190 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1190=0 from arrow_incompatible k b 20 46 [24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1190) h]
    exact Submodule.zero_mem _
lemma extension_1191_49 : a k 49*normalRep k 1191=normalRep k 1266 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13] 49).symm
lemma arrow_span_1191 (b : Fin 75) : a k b*normalRep k 1191 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1191_49 k]
      exact normal_mem k 1266
  · rw [show a k b*normalRep k 1191=0 from arrow_incompatible k b 21 35 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13] (normal_endpoints 1191) h]
    exact Submodule.zero_mem _
lemma extension_1192_20 : a k 20*normalRep k 1192=0 := by
  change a k 20*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_984 (a k) (relation_zero k) (e k 21)
lemma extension_1192_21 : a k 21*normalRep k 1192=normalRep k 1267 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63] 21).symm
lemma arrow_span_1192 (b : Fin 75) : a k b*normalRep k 1192 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1192_20 k]
      exact Submodule.zero_mem _
    · rw [extension_1192_21 k]
      exact normal_mem k 1267
  · rw [show a k b*normalRep k 1192=0 from arrow_incompatible k b 21 18 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63] (normal_endpoints 1192) h]
    exact Submodule.zero_mem _
lemma extension_1193_36 : a k 36*normalRep k 1193=normalRep k 1267 + normalRep k 1266 := by
  change a k 36*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64]=walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] + walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1019 (a k) (relation_zero k) (e k 21)
lemma arrow_span_1193 (b : Fin 75) : a k b*normalRep k 1193 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1193_36 k]
      exact (normalSpan k).add_mem (normal_mem k 1267) (normal_mem k 1266)
  · rw [show a k b*normalRep k 1193=0 from arrow_incompatible k b 21 28 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64] (normal_endpoints 1193) h]
    exact Submodule.zero_mem _
lemma extension_1194_43 : a k 43*normalRep k 1194=0 := by
  change a k 43*walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_971 (a k) (relation_zero k) (e k 22)
lemma extension_1194_44 : a k 44*normalRep k 1194=normalRep k 1268 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_1194 (b : Fin 75) : a k b*normalRep k 1194 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1194_43 k]
      exact Submodule.zero_mem _
    · rw [extension_1194_44 k]
      exact normal_mem k 1268
  · rw [show a k b*normalRep k 1194=0 from arrow_incompatible k b 22 32 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 1194) h]
    exact Submodule.zero_mem _
lemma extension_1195_15 : a k 15*normalRep k 1195=normalRep k 1269 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_1195_16 : a k 16*normalRep k 1195=normalRep k 1268 := by
  change a k 16*walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54]=walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1009 (a k) (relation_zero k) (e k 22)
lemma arrow_span_1195 (b : Fin 75) : a k b*normalRep k 1195 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1195_15 k]
      exact normal_mem k 1269
    · rw [extension_1195_16 k]
      exact normal_mem k 1268
  · rw [show a k b*normalRep k 1195=0 from arrow_incompatible k b 22 15 [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 1195) h]
    exact Submodule.zero_mem _
lemma arrow_span_1196 (b : Fin 75) : a k b*normalRep k 1196 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1196=0 from arrow_incompatible k b 23 46 [28, 14, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1196) h]
    exact Submodule.zero_mem _
lemma extension_1197_69 : a k 69*normalRep k 1197=normalRep k 1270 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] 69).symm
lemma extension_1197_70 : a k 70*normalRep k 1197=0 := by
  change a k 70*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1005 (a k) (relation_zero k) (e k 24)
lemma extension_1197_71 : a k 71*normalRep k 1197=normalRep k 1271 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] 71).symm
lemma arrow_span_1197 (b : Fin 75) : a k b*normalRep k 1197 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1197_69 k]
      exact normal_mem k 1270
    · rw [extension_1197_70 k]
      exact Submodule.zero_mem _
    · rw [extension_1197_71 k]
      exact normal_mem k 1271
  · rw [show a k b*normalRep k 1197=0 from arrow_incompatible k b 24 43 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] (normal_endpoints 1197) h]
    exact Submodule.zero_mem _
lemma extension_1198_69 : a k 69*normalRep k 1198=(-normalRep k 1270) := by
  change a k 69*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]=(-walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69])
  rw [← walk_snoc]
  exact Universal.mul_reduced_999 (a k) (relation_zero k) (e k 24)
lemma extension_1198_70 : a k 70*normalRep k 1198=normalRep k 1272 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] 70).symm
lemma extension_1198_71 : a k 71*normalRep k 1198=0 := by
  change a k 71*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_989 (a k) (relation_zero k) (e k 24)
lemma arrow_span_1198 (b : Fin 75) : a k b*normalRep k 1198 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1198_69 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1270)
    · rw [extension_1198_70 k]
      exact normal_mem k 1272
    · rw [extension_1198_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1198=0 from arrow_incompatible k b 24 43 [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] (normal_endpoints 1198) h]
    exact Submodule.zero_mem _
lemma extension_1199_24 : a k 24*normalRep k 1199=normalRep k 1273 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 24).symm
lemma extension_1199_25 : a k 25*normalRep k 1199=normalRep k 1274 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 25).symm
lemma arrow_span_1199 (b : Fin 75) : a k b*normalRep k 1199 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1199_24 k]
      exact normal_mem k 1273
    · rw [extension_1199_25 k]
      exact normal_mem k 1274
  · rw [show a k b*normalRep k 1199=0 from arrow_incompatible k b 25 20 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] (normal_endpoints 1199) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
