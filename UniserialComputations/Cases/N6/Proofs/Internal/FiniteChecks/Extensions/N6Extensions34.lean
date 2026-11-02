import N6NormalData
import N6Reduced23
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma arrow_span_1700 (b : Fin 75) : a k b*normalRep k 1700 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1700=0 from arrow_incompatible k b 21 46 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1700) h]
    exact Submodule.zero_mem _
lemma extension_1701_30 : a k 30*normalRep k 1701=normalRep k 1704 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1701_31 : a k 31*normalRep k 1701=0 := by
  change a k 31*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1400 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1701 (b : Fin 75) : a k b*normalRep k 1701 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1701_30 k]
      exact normal_mem k 1704
    · rw [extension_1701_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1701=0 from arrow_incompatible k b 45 24 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1701) h]
    exact Submodule.zero_mem _
lemma extension_1702_0 : a k 0*normalRep k 1702=normalRep k 1705 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1702 (b : Fin 75) : a k b*normalRep k 1702 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1702_0 k]
      exact normal_mem k 1705
  · rw [show a k b*normalRep k 1702=0 from arrow_incompatible k b 10 0 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1702) h]
    exact Submodule.zero_mem _
lemma arrow_span_1703 (b : Fin 75) : a k b*normalRep k 1703 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1703=0 from arrow_incompatible k b 11 46 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1703) h]
    exact Submodule.zero_mem _
lemma extension_1704_2 : a k 2*normalRep k 1704=normalRep k 1706 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1704 (b : Fin 75) : a k b*normalRep k 1704 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1704_2 k]
      exact normal_mem k 1706
  · rw [show a k b*normalRep k 1704=0 from arrow_incompatible k b 45 2 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1704) h]
    exact Submodule.zero_mem _
lemma arrow_span_1705 (b : Fin 75) : a k b*normalRep k 1705 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1705=0 from arrow_incompatible k b 10 46 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1705) h]
    exact Submodule.zero_mem _
lemma extension_1706_0 : a k 0*normalRep k 1706=normalRep k 1707 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1706 (b : Fin 75) : a k b*normalRep k 1706 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1706_0 k]
      exact normal_mem k 1707
  · rw [show a k b*normalRep k 1706=0 from arrow_incompatible k b 45 0 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1706) h]
    exact Submodule.zero_mem _
lemma arrow_span_1707 (b : Fin 75) : a k b*normalRep k 1707 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1707=0 from arrow_incompatible k b 45 46 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1707) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
