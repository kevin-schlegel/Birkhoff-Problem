import N6NormalData
import N6Reduced0
import N6Reduced1
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_150_4 : a k 4*normalRep k 150=normalRep k 249 := by
  change a k 4*walk k 20 [25, 60]=walk k 20 [24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_100 (a k) (relation_zero k) (e k 20)
lemma arrow_span_150 (b : Fin 75) : a k b*normalRep k 150 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_150_4 k]
      exact normal_mem k 249
  · rw [show a k b*normalRep k 150=0 from arrow_incompatible k b 20 4 [25, 60] (normal_endpoints 150) h]
    exact Submodule.zero_mem _
lemma extension_151_72 : a k 72*normalRep k 151=0 := by
  change a k 72*walk k 21 [26, 31]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_71 (a k) (relation_zero k) (e k 21)
lemma extension_151_73 : a k 73*normalRep k 151=normalRep k 250 := by
  exact (walk_snoc k 21 [26, 31] 73).symm
lemma arrow_span_151 (b : Fin 75) : a k b*normalRep k 151 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_151_72 k]
      exact Submodule.zero_mem _
    · rw [extension_151_73 k]
      exact normal_mem k 250
  · rw [show a k b*normalRep k 151=0 from arrow_incompatible k b 21 44 [26, 31] (normal_endpoints 151) h]
    exact Submodule.zero_mem _
lemma extension_152_33 : a k 33*normalRep k 152=normalRep k 251 := by
  exact (walk_snoc k 22 [27, 58] 33).symm
lemma extension_152_34 : a k 34*normalRep k 152=normalRep k 252 := by
  exact (walk_snoc k 22 [27, 58] 34).symm
lemma arrow_span_152 (b : Fin 75) : a k b*normalRep k 152 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_152_33 k]
      exact normal_mem k 251
    · rw [extension_152_34 k]
      exact normal_mem k 252
  · rw [show a k b*normalRep k 152=0 from arrow_incompatible k b 22 26 [27, 58] (normal_endpoints 152) h]
    exact Submodule.zero_mem _
lemma extension_153_50 : a k 50*normalRep k 153=normalRep k 253 := by
  exact (walk_snoc k 22 [27, 59] 50).symm
lemma extension_153_51 : a k 51*normalRep k 153=normalRep k 252 := by
  change a k 51*walk k 22 [27, 59]=walk k 22 [27, 58, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_98 (a k) (relation_zero k) (e k 22)
lemma arrow_span_153 (b : Fin 75) : a k b*normalRep k 153 ∈ normalSpan k := by
  by_cases h : arrowSource b=36
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [50, 51] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_153_50 k]
      exact normal_mem k 253
    · rw [extension_153_51 k]
      exact normal_mem k 252
  · rw [show a k b*normalRep k 153=0 from arrow_incompatible k b 22 36 [27, 59] (normal_endpoints 153) h]
    exact Submodule.zero_mem _
lemma extension_154_9 : a k 9*normalRep k 154=normalRep k 254 := by
  exact (walk_snoc k 23 [28, 14] 9).symm
lemma arrow_span_154 (b : Fin 75) : a k b*normalRep k 154 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_154_9 k]
      exact normal_mem k 254
  · rw [show a k b*normalRep k 154=0 from arrow_incompatible k b 23 9 [28, 14] (normal_endpoints 154) h]
    exact Submodule.zero_mem _
lemma extension_155_52 : a k 52*normalRep k 155=normalRep k 254 := by
  change a k 52*walk k 23 [29, 19]=walk k 23 [28, 14, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_58 (a k) (relation_zero k) (e k 23)
lemma extension_155_53 : a k 53*normalRep k 155=normalRep k 255 := by
  exact (walk_snoc k 23 [29, 19] 53).symm
lemma arrow_span_155 (b : Fin 75) : a k b*normalRep k 155 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_155_52 k]
      exact normal_mem k 254
    · rw [extension_155_53 k]
      exact normal_mem k 255
  · rw [show a k b*normalRep k 155=0 from arrow_incompatible k b 23 37 [29, 19] (normal_endpoints 155) h]
    exact Submodule.zero_mem _
lemma extension_156_0 : a k 0*normalRep k 156=normalRep k 256 := by
  exact (walk_snoc k 24 [30, 2] 0).symm
lemma arrow_span_156 (b : Fin 75) : a k b*normalRep k 156 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_156_0 k]
      exact normal_mem k 256
  · rw [show a k b*normalRep k 156=0 from arrow_incompatible k b 24 0 [30, 2] (normal_endpoints 156) h]
    exact Submodule.zero_mem _
lemma extension_157_66 : a k 66*normalRep k 157=0 := by
  change a k 66*walk k 24 [31, 73]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_112 (a k) (relation_zero k) (e k 24)
lemma extension_157_67 : a k 67*normalRep k 157=normalRep k 257 := by
  exact (walk_snoc k 24 [31, 73] 67).symm
lemma extension_157_68 : a k 68*normalRep k 157=normalRep k 258 := by
  exact (walk_snoc k 24 [31, 73] 68).symm
lemma arrow_span_157 (b : Fin 75) : a k b*normalRep k 157 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_157_66 k]
      exact Submodule.zero_mem _
    · rw [extension_157_67 k]
      exact normal_mem k 257
    · rw [extension_157_68 k]
      exact normal_mem k 258
  · rw [show a k b*normalRep k 157=0 from arrow_incompatible k b 24 42 [31, 73] (normal_endpoints 157) h]
    exact Submodule.zero_mem _
lemma extension_158_35 : a k 35*normalRep k 158=normalRep k 259 := by
  exact (walk_snoc k 25 [32, 61] 35).symm
lemma arrow_span_158 (b : Fin 75) : a k b*normalRep k 158 ∈ normalSpan k := by
  by_cases h : arrowSource b=27
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [35] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_158_35 k]
      exact normal_mem k 259
  · rw [show a k b*normalRep k 158=0 from arrow_incompatible k b 25 27 [32, 61] (normal_endpoints 158) h]
    exact Submodule.zero_mem _
lemma extension_159_52 : a k 52*normalRep k 159=normalRep k 260 := by
  exact (walk_snoc k 25 [32, 62] 52).symm
lemma extension_159_53 : a k 53*normalRep k 159=normalRep k 259 := by
  change a k 53*walk k 25 [32, 62]=walk k 25 [32, 61, 35]
  rw [← walk_snoc]
  exact Universal.mul_reduced_101 (a k) (relation_zero k) (e k 25)
lemma arrow_span_159 (b : Fin 75) : a k b*normalRep k 159 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_159_52 k]
      exact normal_mem k 260
    · rw [extension_159_53 k]
      exact normal_mem k 259
  · rw [show a k b*normalRep k 159=0 from arrow_incompatible k b 25 37 [32, 62] (normal_endpoints 159) h]
    exact Submodule.zero_mem _
lemma extension_160_49 : a k 49*normalRep k 160=normalRep k 261 := by
  exact (walk_snoc k 26 [33, 13] 49).symm
lemma arrow_span_160 (b : Fin 75) : a k b*normalRep k 160 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_160_49 k]
      exact normal_mem k 261
  · rw [show a k b*normalRep k 160=0 from arrow_incompatible k b 26 35 [33, 13] (normal_endpoints 160) h]
    exact Submodule.zero_mem _
lemma extension_161_20 : a k 20*normalRep k 161=normalRep k 262 := by
  exact (walk_snoc k 26 [34, 63] 20).symm
lemma extension_161_21 : a k 21*normalRep k 161=normalRep k 263 := by
  exact (walk_snoc k 26 [34, 63] 21).symm
lemma arrow_span_161 (b : Fin 75) : a k b*normalRep k 161 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_161_20 k]
      exact normal_mem k 262
    · rw [extension_161_21 k]
      exact normal_mem k 263
  · rw [show a k b*normalRep k 161=0 from arrow_incompatible k b 26 18 [34, 63] (normal_endpoints 161) h]
    exact Submodule.zero_mem _
lemma extension_162_36 : a k 36*normalRep k 162=normalRep k 263 + normalRep k 261 := by
  change a k 36*walk k 26 [34, 64]=walk k 26 [34, 63, 21] + walk k 26 [33, 13, 49]
  rw [← walk_snoc]
  exact Universal.mul_reduced_104 (a k) (relation_zero k) (e k 26)
lemma arrow_span_162 (b : Fin 75) : a k b*normalRep k 162 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_162_36 k]
      exact (normalSpan k).add_mem (normal_mem k 263) (normal_mem k 261)
  · rw [show a k b*normalRep k 162=0 from arrow_incompatible k b 26 28 [34, 64] (normal_endpoints 162) h]
    exact Submodule.zero_mem _
lemma extension_163_27 : a k 27*normalRep k 163=normalRep k 264 := by
  exact (walk_snoc k 27 [35, 55] 27).symm
lemma arrow_span_163 (b : Fin 75) : a k b*normalRep k 163 ∈ normalSpan k := by
  by_cases h : arrowSource b=22
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [27] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_163_27 k]
      exact normal_mem k 264
  · rw [show a k b*normalRep k 163=0 from arrow_incompatible k b 27 22 [35, 55] (normal_endpoints 163) h]
    exact Submodule.zero_mem _
lemma extension_164_43 : a k 43*normalRep k 164=normalRep k 265 := by
  exact (walk_snoc k 27 [35, 56] 43).symm
lemma extension_164_44 : a k 44*normalRep k 164=normalRep k 264 := by
  change a k 44*walk k 27 [35, 56]=walk k 27 [35, 55, 27]
  rw [← walk_snoc]
  exact Universal.mul_reduced_95 (a k) (relation_zero k) (e k 27)
lemma arrow_span_164 (b : Fin 75) : a k b*normalRep k 164 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_164_43 k]
      exact normal_mem k 265
    · rw [extension_164_44 k]
      exact normal_mem k 264
  · rw [show a k b*normalRep k 164=0 from arrow_incompatible k b 27 32 [35, 56] (normal_endpoints 164) h]
    exact Submodule.zero_mem _
lemma extension_165_22 : a k 22*normalRep k 165=normalRep k 266 := by
  exact (walk_snoc k 28 [36, 70] 22).symm
lemma extension_165_23 : a k 23*normalRep k 165=normalRep k 267 := by
  exact (walk_snoc k 28 [36, 70] 23).symm
lemma arrow_span_165 (b : Fin 75) : a k b*normalRep k 165 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_165_22 k]
      exact normal_mem k 266
    · rw [extension_165_23 k]
      exact normal_mem k 267
  · rw [show a k b*normalRep k 165=0 from arrow_incompatible k b 28 19 [36, 70] (normal_endpoints 165) h]
    exact Submodule.zero_mem _
lemma extension_166_72 : a k 72*normalRep k 166=normalRep k 268 := by
  exact (walk_snoc k 28 [36, 71] 72).symm
lemma extension_166_73 : a k 73*normalRep k 166=normalRep k 267 := by
  change a k 73*walk k 28 [36, 71]=walk k 28 [36, 70, 23]
  rw [← walk_snoc]
  exact Universal.mul_reduced_110 (a k) (relation_zero k) (e k 28)
lemma arrow_span_166 (b : Fin 75) : a k b*normalRep k 166 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_166_72 k]
      exact normal_mem k 268
    · rw [extension_166_73 k]
      exact normal_mem k 267
  · rw [show a k b*normalRep k 166=0 from arrow_incompatible k b 28 44 [36, 71] (normal_endpoints 166) h]
    exact Submodule.zero_mem _
lemma extension_167_18 : a k 18*normalRep k 167=normalRep k 269 := by
  exact (walk_snoc k 29 [37, 24] 18).symm
lemma extension_167_19 : a k 19*normalRep k 167=normalRep k 270 := by
  exact (walk_snoc k 29 [37, 24] 19).symm
lemma arrow_span_167 (b : Fin 75) : a k b*normalRep k 167 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_167_18 k]
      exact normal_mem k 269
    · rw [extension_167_19 k]
      exact normal_mem k 270
  · rw [show a k b*normalRep k 167=0 from arrow_incompatible k b 29 17 [37, 24] (normal_endpoints 167) h]
    exact Submodule.zero_mem _
lemma extension_168_60 : a k 60*normalRep k 168=normalRep k 271 := by
  exact (walk_snoc k 29 [37, 25] 60).symm
lemma extension_168_61 : a k 61*normalRep k 168=0 := by
  change a k 61*walk k 29 [37, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_64 (a k) (relation_zero k) (e k 29)
lemma extension_168_62 : a k 62*normalRep k 168=normalRep k 270 := by
  change a k 62*walk k 29 [37, 25]=walk k 29 [37, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_66 (a k) (relation_zero k) (e k 29)
lemma arrow_span_168 (b : Fin 75) : a k b*normalRep k 168 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_168_60 k]
      exact normal_mem k 271
    · rw [extension_168_61 k]
      exact Submodule.zero_mem _
    · rw [extension_168_62 k]
      exact normal_mem k 270
  · rw [show a k b*normalRep k 168=0 from arrow_incompatible k b 29 40 [37, 25] (normal_endpoints 168) h]
    exact Submodule.zero_mem _
lemma extension_169_14 : a k 14*normalRep k 169=normalRep k 269 := by
  change a k 14*walk k 29 [38, 28]=walk k 29 [37, 24, 18]
  rw [← walk_snoc]
  exact Universal.mul_reduced_70 (a k) (relation_zero k) (e k 29)
lemma arrow_span_169 (b : Fin 75) : a k b*normalRep k 169 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_169_14 k]
      exact normal_mem k 269
  · rw [show a k b*normalRep k 169=0 from arrow_incompatible k b 29 14 [38, 28] (normal_endpoints 169) h]
    exact Submodule.zero_mem _
lemma extension_170_35 : a k 35*normalRep k 170=normalRep k 272 := by
  exact (walk_snoc k 30 [39, 12] 35).symm
lemma arrow_span_170 (b : Fin 75) : a k b*normalRep k 170 ∈ normalSpan k := by
  by_cases h : arrowSource b=27
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [35] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_170_35 k]
      exact normal_mem k 272
  · rw [show a k b*normalRep k 170=0 from arrow_incompatible k b 30 27 [39, 12] (normal_endpoints 170) h]
    exact Submodule.zero_mem _
lemma extension_171_4 : a k 4*normalRep k 171=normalRep k 273 := by
  exact (walk_snoc k 30 [40, 60] 4).symm
lemma arrow_span_171 (b : Fin 75) : a k b*normalRep k 171 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_171_4 k]
      exact normal_mem k 273
  · rw [show a k b*normalRep k 171=0 from arrow_incompatible k b 30 4 [40, 60] (normal_endpoints 171) h]
    exact Submodule.zero_mem _
lemma extension_172_52 : a k 52*normalRep k 172=normalRep k 274 := by
  exact (walk_snoc k 30 [40, 62] 52).symm
lemma extension_172_53 : a k 53*normalRep k 172=normalRep k 273 + normalRep k 272 := by
  change a k 53*walk k 30 [40, 62]=walk k 30 [40, 60, 4] + walk k 30 [39, 12, 35]
  rw [← walk_snoc]
  exact Universal.mul_reduced_102 (a k) (relation_zero k) (e k 30)
lemma arrow_span_172 (b : Fin 75) : a k b*normalRep k 172 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_172_52 k]
      exact normal_mem k 274
    · rw [extension_172_53 k]
      exact (normalSpan k).add_mem (normal_mem k 273) (normal_mem k 272)
  · rw [show a k b*normalRep k 172=0 from arrow_incompatible k b 30 37 [40, 62] (normal_endpoints 172) h]
    exact Submodule.zero_mem _
lemma extension_173_47 : a k 47*normalRep k 173=normalRep k 275 := by
  exact (walk_snoc k 31 [41, 43] 47).symm
lemma extension_173_48 : a k 48*normalRep k 173=normalRep k 276 := by
  exact (walk_snoc k 31 [41, 43] 48).symm
lemma arrow_span_173 (b : Fin 75) : a k b*normalRep k 173 ∈ normalSpan k := by
  by_cases h : arrowSource b=34
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [47, 48] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_173_47 k]
      exact normal_mem k 275
    · rw [extension_173_48 k]
      exact normal_mem k 276
  · rw [show a k b*normalRep k 173=0 from arrow_incompatible k b 31 34 [41, 43] (normal_endpoints 173) h]
    exact Submodule.zero_mem _
lemma extension_174_57 : a k 57*normalRep k 174=normalRep k 277 := by
  exact (walk_snoc k 31 [41, 44] 57).symm
lemma extension_174_58 : a k 58*normalRep k 174=normalRep k 278 := by
  exact (walk_snoc k 31 [41, 44] 58).symm
lemma extension_174_59 : a k 59*normalRep k 174=normalRep k 276 := by
  change a k 59*walk k 31 [41, 44]=walk k 31 [41, 43, 48]
  rw [← walk_snoc]
  exact Universal.mul_reduced_83 (a k) (relation_zero k) (e k 31)
lemma arrow_span_174 (b : Fin 75) : a k b*normalRep k 174 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_174_57 k]
      exact normal_mem k 277
    · rw [extension_174_58 k]
      exact normal_mem k 278
    · rw [extension_174_59 k]
      exact normal_mem k 276
  · rw [show a k b*normalRep k 174=0 from arrow_incompatible k b 31 39 [41, 44] (normal_endpoints 174) h]
    exact Submodule.zero_mem _
lemma extension_175_6 : a k 6*normalRep k 175=normalRep k 275 := by
  change a k 6*walk k 31 [42, 45]=walk k 31 [41, 43, 47]
  rw [← walk_snoc]
  exact Universal.mul_reduced_85 (a k) (relation_zero k) (e k 31)
lemma arrow_span_175 (b : Fin 75) : a k b*normalRep k 175 ∈ normalSpan k := by
  by_cases h : arrowSource b=6
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [6] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_175_6 k]
      exact normal_mem k 275
  · rw [show a k b*normalRep k 175=0 from arrow_incompatible k b 31 6 [42, 45] (normal_endpoints 175) h]
    exact Submodule.zero_mem _
lemma extension_176_7 : a k 7*normalRep k 176=normalRep k 279 := by
  exact (walk_snoc k 32 [43, 47] 7).symm
lemma arrow_span_176 (b : Fin 75) : a k b*normalRep k 176 ∈ normalSpan k := by
  by_cases h : arrowSource b=7
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [7] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_176_7 k]
      exact normal_mem k 279
  · rw [show a k b*normalRep k 176=0 from arrow_incompatible k b 32 7 [43, 47] (normal_endpoints 176) h]
    exact Submodule.zero_mem _
lemma extension_177_50 : a k 50*normalRep k 177=normalRep k 279 := by
  change a k 50*walk k 32 [43, 48]=walk k 32 [43, 47, 7]
  rw [← walk_snoc]
  exact Universal.mul_reduced_86 (a k) (relation_zero k) (e k 32)
lemma extension_177_51 : a k 51*normalRep k 177=normalRep k 280 := by
  exact (walk_snoc k 32 [43, 48] 51).symm
lemma arrow_span_177 (b : Fin 75) : a k b*normalRep k 177 ∈ normalSpan k := by
  by_cases h : arrowSource b=36
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [50, 51] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_177_50 k]
      exact normal_mem k 279
    · rw [extension_177_51 k]
      exact normal_mem k 280
  · rw [show a k b*normalRep k 177=0 from arrow_incompatible k b 32 36 [43, 48] (normal_endpoints 177) h]
    exact Submodule.zero_mem _
lemma extension_178_5 : a k 5*normalRep k 178=normalRep k 281 := by
  exact (walk_snoc k 32 [44, 57] 5).symm
lemma arrow_span_178 (b : Fin 75) : a k b*normalRep k 178 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_178_5 k]
      exact normal_mem k 281
  · rw [show a k b*normalRep k 178=0 from arrow_incompatible k b 32 5 [44, 57] (normal_endpoints 178) h]
    exact Submodule.zero_mem _
lemma extension_179_33 : a k 33*normalRep k 179=normalRep k 282 := by
  exact (walk_snoc k 32 [44, 58] 33).symm
lemma extension_179_34 : a k 34*normalRep k 179=normalRep k 281 + normalRep k 280 := by
  change a k 34*walk k 32 [44, 58]=walk k 32 [44, 57, 5] + walk k 32 [43, 48, 51]
  rw [← walk_snoc]
  exact Universal.mul_reduced_99 (a k) (relation_zero k) (e k 32)
lemma arrow_span_179 (b : Fin 75) : a k b*normalRep k 179 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_179_33 k]
      exact normal_mem k 282
    · rw [extension_179_34 k]
      exact (normalSpan k).add_mem (normal_mem k 281) (normal_mem k 280)
  · rw [show a k b*normalRep k 179=0 from arrow_incompatible k b 32 26 [44, 58] (normal_endpoints 179) h]
    exact Submodule.zero_mem _
lemma extension_180_7 : a k 7*normalRep k 180=normalRep k 283 := by
  exact (walk_snoc k 33 [45, 6] 7).symm
lemma arrow_span_180 (b : Fin 75) : a k b*normalRep k 180 ∈ normalSpan k := by
  by_cases h : arrowSource b=7
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [7] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_180_7 k]
      exact normal_mem k 283
  · rw [show a k b*normalRep k 180=0 from arrow_incompatible k b 33 7 [45, 6] (normal_endpoints 180) h]
    exact Submodule.zero_mem _
lemma extension_181_50 : a k 50*normalRep k 181=normalRep k 283 := by
  change a k 50*walk k 33 [46, 48]=walk k 33 [45, 6, 7]
  rw [← walk_snoc]
  exact Universal.mul_reduced_87 (a k) (relation_zero k) (e k 33)
lemma extension_181_51 : a k 51*normalRep k 181=normalRep k 284 := by
  exact (walk_snoc k 33 [46, 48] 51).symm
lemma arrow_span_181 (b : Fin 75) : a k b*normalRep k 181 ∈ normalSpan k := by
  by_cases h : arrowSource b=36
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [50, 51] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_181_50 k]
      exact normal_mem k 283
    · rw [extension_181_51 k]
      exact normal_mem k 284
  · rw [show a k b*normalRep k 181=0 from arrow_incompatible k b 33 36 [46, 48] (normal_endpoints 181) h]
    exact Submodule.zero_mem _
lemma extension_182_17 : a k 17*normalRep k 182=normalRep k 285 := by
  exact (walk_snoc k 34 [47, 7] 17).symm
lemma arrow_span_182 (b : Fin 75) : a k b*normalRep k 182 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_182_17 k]
      exact normal_mem k 285
  · rw [show a k b*normalRep k 182=0 from arrow_incompatible k b 34 16 [47, 7] (normal_endpoints 182) h]
    exact Submodule.zero_mem _
lemma extension_183_63 : a k 63*normalRep k 183=normalRep k 285 := by
  change a k 63*walk k 34 [48, 51]=walk k 34 [47, 7, 17]
  rw [← walk_snoc]
  exact Universal.mul_reduced_90 (a k) (relation_zero k) (e k 34)
lemma extension_183_64 : a k 64*normalRep k 183=normalRep k 286 := by
  exact (walk_snoc k 34 [48, 51] 64).symm
lemma extension_183_65 : a k 65*normalRep k 183=normalRep k 287 := by
  exact (walk_snoc k 34 [48, 51] 65).symm
lemma arrow_span_183 (b : Fin 75) : a k b*normalRep k 183 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_183_63 k]
      exact normal_mem k 285
    · rw [extension_183_64 k]
      exact normal_mem k 286
    · rw [extension_183_65 k]
      exact normal_mem k 287
  · rw [show a k b*normalRep k 183=0 from arrow_incompatible k b 34 41 [48, 51] (normal_endpoints 183) h]
    exact Submodule.zero_mem _
lemma extension_184_8 : a k 8*normalRep k 184=normalRep k 288 := by
  exact (walk_snoc k 35 [49, 69] 8).symm
lemma arrow_span_184 (b : Fin 75) : a k b*normalRep k 184 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_184_8 k]
      exact normal_mem k 288
  · rw [show a k b*normalRep k 184=0 from arrow_incompatible k b 35 8 [49, 69] (normal_endpoints 184) h]
    exact Submodule.zero_mem _
lemma extension_185_72 : a k 72*normalRep k 185=normalRep k 289 := by
  exact (walk_snoc k 35 [49, 71] 72).symm
lemma extension_185_73 : a k 73*normalRep k 185=normalRep k 288 := by
  change a k 73*walk k 35 [49, 71]=walk k 35 [49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_111 (a k) (relation_zero k) (e k 35)
lemma arrow_span_185 (b : Fin 75) : a k b*normalRep k 185 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_185_72 k]
      exact normal_mem k 289
    · rw [extension_185_73 k]
      exact normal_mem k 288
  · rw [show a k b*normalRep k 185=0 from arrow_incompatible k b 35 44 [49, 71] (normal_endpoints 185) h]
    exact Submodule.zero_mem _
lemma extension_186_20 : a k 20*normalRep k 186=0 := by
  change a k 20*walk k 36 [50, 17]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_55 (a k) (relation_zero k) (e k 36)
lemma extension_186_21 : a k 21*normalRep k 186=normalRep k 290 := by
  exact (walk_snoc k 36 [50, 17] 21).symm
lemma arrow_span_186 (b : Fin 75) : a k b*normalRep k 186 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_186_20 k]
      exact Submodule.zero_mem _
    · rw [extension_186_21 k]
      exact normal_mem k 290
  · rw [show a k b*normalRep k 186=0 from arrow_incompatible k b 36 18 [50, 17] (normal_endpoints 186) h]
    exact Submodule.zero_mem _
lemma extension_187_36 : a k 36*normalRep k 187=normalRep k 291 := by
  exact (walk_snoc k 36 [51, 64] 36).symm
lemma arrow_span_187 (b : Fin 75) : a k b*normalRep k 187 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_187_36 k]
      exact normal_mem k 291
  · rw [show a k b*normalRep k 187=0 from arrow_incompatible k b 36 28 [51, 64] (normal_endpoints 187) h]
    exact Submodule.zero_mem _
lemma extension_188_49 : a k 49*normalRep k 188=(-normalRep k 290) + normalRep k 291 := by
  change a k 49*walk k 36 [51, 65]=(-walk k 36 [50, 17, 21]) + walk k 36 [51, 64, 36]
  rw [← walk_snoc]
  exact Universal.mul_reduced_105 (a k) (relation_zero k) (e k 36)
lemma arrow_span_188 (b : Fin 75) : a k b*normalRep k 188 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_188_49 k]
      exact (normalSpan k).add_mem ((normalSpan k).smul_mem (-1:k) (normal_mem k 290)) (normal_mem k 291)
  · rw [show a k b*normalRep k 188=0 from arrow_incompatible k b 36 35 [51, 65] (normal_endpoints 188) h]
    exact Submodule.zero_mem _
lemma extension_189_43 : a k 43*normalRep k 189=normalRep k 292 := by
  exact (walk_snoc k 37 [52, 41] 43).symm
lemma extension_189_44 : a k 44*normalRep k 189=normalRep k 293 := by
  exact (walk_snoc k 37 [52, 41] 44).symm
lemma arrow_span_189 (b : Fin 75) : a k b*normalRep k 189 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_189_43 k]
      exact normal_mem k 292
    · rw [extension_189_44 k]
      exact normal_mem k 293
  · rw [show a k b*normalRep k 189=0 from arrow_incompatible k b 37 32 [52, 41] (normal_endpoints 189) h]
    exact Submodule.zero_mem _
lemma extension_190_45 : a k 45*normalRep k 190=normalRep k 294 := by
  exact (walk_snoc k 37 [52, 42] 45).symm
lemma extension_190_46 : a k 46*normalRep k 190=normalRep k 292 := by
  change a k 46*walk k 37 [52, 42]=walk k 37 [52, 41, 43]
  rw [← walk_snoc]
  exact Universal.mul_reduced_82 (a k) (relation_zero k) (e k 37)
lemma arrow_span_190 (b : Fin 75) : a k b*normalRep k 190 ∈ normalSpan k := by
  by_cases h : arrowSource b=33
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [45, 46] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_190_45 k]
      exact normal_mem k 294
    · rw [extension_190_46 k]
      exact normal_mem k 292
  · rw [show a k b*normalRep k 190=0 from arrow_incompatible k b 37 33 [52, 42] (normal_endpoints 190) h]
    exact Submodule.zero_mem _
lemma extension_191_15 : a k 15*normalRep k 191=normalRep k 295 := by
  exact (walk_snoc k 37 [53, 54] 15).symm
lemma extension_191_16 : a k 16*normalRep k 191=normalRep k 296 := by
  exact (walk_snoc k 37 [53, 54] 16).symm
lemma arrow_span_191 (b : Fin 75) : a k b*normalRep k 191 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_191_15 k]
      exact normal_mem k 295
    · rw [extension_191_16 k]
      exact normal_mem k 296
  · rw [show a k b*normalRep k 191=0 from arrow_incompatible k b 37 15 [53, 54] (normal_endpoints 191) h]
    exact Submodule.zero_mem _
lemma extension_192_27 : a k 27*normalRep k 192=(-normalRep k 296) + normalRep k 293 := by
  change a k 27*walk k 37 [53, 55]=(-walk k 37 [53, 54, 16]) + walk k 37 [52, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_96 (a k) (relation_zero k) (e k 37)
lemma arrow_span_192 (b : Fin 75) : a k b*normalRep k 192 ∈ normalSpan k := by
  by_cases h : arrowSource b=22
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [27] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_192_27 k]
      exact (normalSpan k).add_mem ((normalSpan k).smul_mem (-1:k) (normal_mem k 296)) (normal_mem k 293)
  · rw [show a k b*normalRep k 192=0 from arrow_incompatible k b 37 22 [53, 55] (normal_endpoints 192) h]
    exact Submodule.zero_mem _
lemma extension_193_1 : a k 1*normalRep k 193=normalRep k 297 := by
  exact (walk_snoc k 38 [54, 15] 1).symm
lemma arrow_span_193 (b : Fin 75) : a k b*normalRep k 193 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_193_1 k]
      exact normal_mem k 297
  · rw [show a k b*normalRep k 193=0 from arrow_incompatible k b 38 1 [54, 15] (normal_endpoints 193) h]
    exact Submodule.zero_mem _
lemma extension_194_57 : a k 57*normalRep k 194=normalRep k 298 := by
  exact (walk_snoc k 38 [54, 16] 57).symm
lemma extension_194_58 : a k 58*normalRep k 194=normalRep k 297 := by
  change a k 58*walk k 38 [54, 16]=walk k 38 [54, 15, 1]
  rw [← walk_snoc]
  exact Universal.mul_reduced_52 (a k) (relation_zero k) (e k 38)
lemma extension_194_59 : a k 59*normalRep k 194=0 := by
  change a k 59*walk k 38 [54, 16]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_53 (a k) (relation_zero k) (e k 38)
lemma arrow_span_194 (b : Fin 75) : a k b*normalRep k 194 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_194_57 k]
      exact normal_mem k 298
    · rw [extension_194_58 k]
      exact normal_mem k 297
    · rw [extension_194_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 194=0 from arrow_incompatible k b 38 39 [54, 16] (normal_endpoints 194) h]
    exact Submodule.zero_mem _
lemma extension_195_57 : a k 57*normalRep k 195=0 := by
  change a k 57*walk k 38 [55, 27]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_69 (a k) (relation_zero k) (e k 38)
lemma extension_195_58 : a k 58*normalRep k 195=normalRep k 299 := by
  exact (walk_snoc k 38 [55, 27] 58).symm
lemma extension_195_59 : a k 59*normalRep k 195=normalRep k 300 := by
  exact (walk_snoc k 38 [55, 27] 59).symm
lemma arrow_span_195 (b : Fin 75) : a k b*normalRep k 195 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_195_57 k]
      exact Submodule.zero_mem _
    · rw [extension_195_58 k]
      exact normal_mem k 299
    · rw [extension_195_59 k]
      exact normal_mem k 300
  · rw [show a k b*normalRep k 195=0 from arrow_incompatible k b 38 39 [55, 27] (normal_endpoints 195) h]
    exact Submodule.zero_mem _
lemma extension_196_47 : a k 47*normalRep k 196=normalRep k 301 := by
  exact (walk_snoc k 38 [56, 43] 47).symm
lemma extension_196_48 : a k 48*normalRep k 196=normalRep k 300 := by
  change a k 48*walk k 38 [56, 43]=walk k 38 [55, 27, 59]
  rw [← walk_snoc]
  exact Universal.mul_reduced_84 (a k) (relation_zero k) (e k 38)
lemma arrow_span_196 (b : Fin 75) : a k b*normalRep k 196 ∈ normalSpan k := by
  by_cases h : arrowSource b=34
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [47, 48] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_196_47 k]
      exact normal_mem k 301
    · rw [extension_196_48 k]
      exact normal_mem k 300
  · rw [show a k b*normalRep k 196=0 from arrow_incompatible k b 38 34 [56, 43] (normal_endpoints 196) h]
    exact Submodule.zero_mem _
lemma extension_197_63 : a k 63*normalRep k 197=normalRep k 302 := by
  exact (walk_snoc k 39 [57, 5] 63).symm
lemma extension_197_64 : a k 64*normalRep k 197=0 := by
  change a k 64*walk k 39 [57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_46 (a k) (relation_zero k) (e k 39)
lemma extension_197_65 : a k 65*normalRep k 197=0 := by
  change a k 65*walk k 39 [57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_47 (a k) (relation_zero k) (e k 39)
lemma arrow_span_197 (b : Fin 75) : a k b*normalRep k 197 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_197_63 k]
      exact normal_mem k 302
    · rw [extension_197_64 k]
      exact Submodule.zero_mem _
    · rw [extension_197_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 197=0 from arrow_incompatible k b 39 41 [57, 5] (normal_endpoints 197) h]
    exact Submodule.zero_mem _
lemma extension_198_13 : a k 13*normalRep k 198=normalRep k 303 := by
  exact (walk_snoc k 39 [58, 33] 13).symm
lemma arrow_span_198 (b : Fin 75) : a k b*normalRep k 198 ∈ normalSpan k := by
  by_cases h : arrowSource b=13
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [13] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_198_13 k]
      exact normal_mem k 303
  · rw [show a k b*normalRep k 198=0 from arrow_incompatible k b 39 13 [58, 33] (normal_endpoints 198) h]
    exact Submodule.zero_mem _
lemma extension_199_63 : a k 63*normalRep k 199=normalRep k 304 := by
  exact (walk_snoc k 39 [58, 34] 63).symm
lemma extension_199_64 : a k 64*normalRep k 199=normalRep k 305 := by
  exact (walk_snoc k 39 [58, 34] 64).symm
lemma extension_199_65 : a k 65*normalRep k 199=normalRep k 303 := by
  change a k 65*walk k 39 [58, 34]=walk k 39 [58, 33, 13]
  rw [← walk_snoc]
  exact Universal.mul_reduced_74 (a k) (relation_zero k) (e k 39)
lemma arrow_span_199 (b : Fin 75) : a k b*normalRep k 199 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_199_63 k]
      exact normal_mem k 304
    · rw [extension_199_64 k]
      exact normal_mem k 305
    · rw [extension_199_65 k]
      exact normal_mem k 303
  · rw [show a k b*normalRep k 199=0 from arrow_incompatible k b 39 41 [58, 34] (normal_endpoints 199) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
