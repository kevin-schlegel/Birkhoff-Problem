import N6QuiverData
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
def relationSource : Fin 47 → Fin 47 := ![1,1,3,3,4,4,5,5,8,8,9,9,15,15,16,17,17,18,18,19,19,20,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44]
def relationTarget : Fin 47 → Fin 47 := ![13,28,12,33,22,34,28,35,12,25,13,33,26,36,24,22,31,44,44,25,30,27,37,2,5,9,29,4,35,15,8,17,27,34,36,7,16,19,18,32,39,41,38,43,40,42,20]
def relationTerms : Fin 47 → List (Int × List (Fin 75)) := ![[(1,[1, 33])],[(1,[1, 34, 64])],[(1,[3, 39])],[(1,[3, 40, 62, 52, 42])],[(1,[4, 55])],[(1,[4, 56, 43])],[(1,[5, 64])],[(1,[5, 65])],[(1,[8, 68, 39])],[(1,[8, 67])],[(1,[9, 41, 44, 58, 33])],[(1,[9, 42])],[(-1,[15, 1]),(1,[16, 58])],[(1,[16, 59])],[(1,[17, 20])],[(1,[19, 53, 55])],[(-1,[18, 9]),(1,[19, 52])],[(1,[20, 31])],[(1,[21, 71])],[(1,[23, 67])],[(1,[22, 3]),(1,[23, 68])],[(1,[25, 61])],[(-1,[24, 19]),(1,[25, 62])],[(1,[26, 30])],[(1,[27, 57])],[(-1,[28, 14]),(1,[29, 18])],[(1,[31, 72])],[(1,[32, 60])],[(-1,[33, 13]),(1,[34, 65])],[(1,[35, 54])],[(1,[36, 69])],[(-1,[37, 24]),(1,[38, 29])],[(-1,[39, 12]),(1,[40, 61])],[(-1,[41, 43]),(1,[42, 46])],[(-1,[43, 48]),(1,[44, 59])],[(-1,[45, 6]),(1,[46, 47])],[(-1,[47, 7]),(1,[48, 50])],[(1,[49, 70])],[(-1,[50, 17]),(1,[51, 63])],[(-1,[52, 41]),(1,[53, 56])],[(-1,[54, 16]),(-1,[55, 27]),(1,[56, 44])],[(1,[57, 5]),(-1,[58, 34]),(1,[59, 51])],[(-1,[60, 4]),(-1,[61, 35]),(1,[62, 53])],[(1,[63, 21]),(-1,[64, 36]),(1,[65, 49])],[(1,[66, 25]),(-1,[67, 32]),(1,[68, 40])],[(-1,[69, 8]),(-1,[70, 23]),(1,[71, 73])],[(-1,[72, 37]),(1,[73, 66])]]
def walkEnd (s : Fin 47) : List (Fin 75) → Option (Fin 47)
  | [] => some s
  | a::p => if arrowSource a=s then walkEnd (arrowTarget a) p else none
theorem relation_endpoints : ∀ z, (relationTerms z).all (fun t => walkEnd (relationSource z) t.2 == some (relationTarget z))=true := by decide
theorem relation_minimum_degree : ∀ z, (relationTerms z).all (fun t => 2≤t.2.length)=true := by decide
variable (k : Type*) [CommRing k]
def wordMatrix (p : List (Fin 75)) : Matrix (Fin 2) (Fin 2) k := (p.reverse.map (arrowMatrix k)).prod
def relationValue (z : Fin 47) : Matrix (Fin 2) (Fin 2) k := ((relationTerms z).map (fun t => (t.1 : k) • wordMatrix k t.2)).sum
theorem relation_0 : relationValue k 0=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_1 : relationValue k 1=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_2 : relationValue k 2=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_3 : relationValue k 3=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_4 : relationValue k 4=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_5 : relationValue k 5=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_6 : relationValue k 6=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_7 : relationValue k 7=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_8 : relationValue k 8=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_9 : relationValue k 9=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_10 : relationValue k 10=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_11 : relationValue k 11=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_12 : relationValue k 12=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_13 : relationValue k 13=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_14 : relationValue k 14=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_15 : relationValue k 15=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_16 : relationValue k 16=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_17 : relationValue k 17=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_18 : relationValue k 18=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_19 : relationValue k 19=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_20 : relationValue k 20=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_21 : relationValue k 21=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_22 : relationValue k 22=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_23 : relationValue k 23=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_24 : relationValue k 24=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_25 : relationValue k 25=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_26 : relationValue k 26=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_27 : relationValue k 27=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_28 : relationValue k 28=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_29 : relationValue k 29=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_30 : relationValue k 30=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_31 : relationValue k 31=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_32 : relationValue k 32=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_33 : relationValue k 33=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_34 : relationValue k 34=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_35 : relationValue k 35=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_36 : relationValue k 36=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_37 : relationValue k 37=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_38 : relationValue k 38=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_39 : relationValue k 39=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_40 : relationValue k 40=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_41 : relationValue k 41=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_42 : relationValue k 42=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_43 : relationValue k 43=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_44 : relationValue k 44=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_45 : relationValue k 45=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relation_46 : relationValue k 46=0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [relationValue,relationTerms,wordMatrix,arrowMatrix,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Matrix.mul_apply,Fin.sum_univ_succ]
theorem relations_vanish : ∀ z, relationValue k z=0 := by
  intro z
  fin_cases z
  · exact relation_0 k
  · exact relation_1 k
  · exact relation_2 k
  · exact relation_3 k
  · exact relation_4 k
  · exact relation_5 k
  · exact relation_6 k
  · exact relation_7 k
  · exact relation_8 k
  · exact relation_9 k
  · exact relation_10 k
  · exact relation_11 k
  · exact relation_12 k
  · exact relation_13 k
  · exact relation_14 k
  · exact relation_15 k
  · exact relation_16 k
  · exact relation_17 k
  · exact relation_18 k
  · exact relation_19 k
  · exact relation_20 k
  · exact relation_21 k
  · exact relation_22 k
  · exact relation_23 k
  · exact relation_24 k
  · exact relation_25 k
  · exact relation_26 k
  · exact relation_27 k
  · exact relation_28 k
  · exact relation_29 k
  · exact relation_30 k
  · exact relation_31 k
  · exact relation_32 k
  · exact relation_33 k
  · exact relation_34 k
  · exact relation_35 k
  · exact relation_36 k
  · exact relation_37 k
  · exact relation_38 k
  · exact relation_39 k
  · exact relation_40 k
  · exact relation_41 k
  · exact relation_42 k
  · exact relation_43 k
  · exact relation_44 k
  · exact relation_45 k
  · exact relation_46 k
end UniserialComputations.N6
