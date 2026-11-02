import N6HomSpace
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
variable (k : Type*) [CommRing k]
theorem normal_form_0 (A : Block k)
    (h1 : A 0 1=0)
    (h2 : A 1 0=0)
    (h3 : A 1 1=0)
    : Normal k 0 A := by
  unfold Normal
  ext r c
  fin_cases r <;> fin_cases c
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h1
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h2
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h3
theorem normal_form_1 (A : Block k)
    (h0 : A 0 0=0)
    (h1 : A 0 1=0)
    (h2 : A 1 0=0)
    (h3 : A 1 1=0)
    : Normal k 1 A := by
  unfold Normal
  ext r c
  fin_cases r <;> fin_cases c
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h0
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h1
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h2
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h3
theorem normal_form_2 (A : Block k)
    (h0 : A 0 0=0)
    (h1 : A 0 1=0)
    (h3 : A 1 1=0)
    : Normal k 2 A := by
  unfold Normal
  ext r c
  fin_cases r <;> fin_cases c
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h0
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h1
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h3
theorem normal_form_3 (A : Block k)
    (h1 : A 0 1=0)
    (h3 : A 1 1=0)
    : Normal k 3 A := by
  unfold Normal
  ext r c
  fin_cases r <;> fin_cases c
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h1
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h3
theorem normal_form_4 (A : Block k)
    (h1 : A 0 1=0)
    (h2 : A 1 0=(-1)*A 0 0)
    (h3 : A 1 1=0)
    : Normal k 4 A := by
  unfold Normal
  ext r c
  fin_cases r <;> fin_cases c
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h1
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h2
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h3
theorem normal_form_5 (A : Block k)
    (h2 : A 1 0=0)
    (h3 : A 1 1=0)
    : Normal k 5 A := by
  unfold Normal
  ext r c
  fin_cases r <;> fin_cases c
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h2
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h3
theorem normal_form_6 (A : Block k)
    (h1 : A 0 1=0)
    (h3 : A 1 1=(1)*A 0 0)
    : Normal k 6 A := by
  unfold Normal
  ext r c
  fin_cases r <;> fin_cases c
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h1
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h3
theorem normal_form_7 (A : Block k)
    (h0 : A 0 0=0)
    (h1 : A 0 1=0)
    : Normal k 7 A := by
  unfold Normal
  ext r c
  fin_cases r <;> fin_cases c
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h0
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h1
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
theorem normal_form_8 (A : Block k)
    (h1 : A 0 1=0)
    : Normal k 8 A := by
  unfold Normal
  ext r c
  fin_cases r <;> fin_cases c
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h1
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
theorem normal_form_9 (A : Block k)
    (h1 : A 0 1=0)
    (h3 : A 1 1=(-1)*A 0 0)
    : Normal k 9 A := by
  unfold Normal
  ext r c
  fin_cases r <;> fin_cases c
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h1
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h3
theorem normal_form_10 (A : Block k)
    (h0 : A 0 0=0)
    (h2 : A 1 0=0)
    (h3 : A 1 1=0)
    : Normal k 10 A := by
  unfold Normal
  ext r c
  fin_cases r <;> fin_cases c
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h0
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h2
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h3
theorem normal_form_11 (A : Block k)
    (h1 : A 0 1=(1)*A 0 0)
    (h2 : A 1 0=0)
    (h3 : A 1 1=0)
    : Normal k 11 A := by
  unfold Normal
  ext r c
  fin_cases r <;> fin_cases c
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h1
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h2
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h3
theorem normal_form_12 (A : Block k)
    (h1 : A 0 1=0)
    (h2 : A 1 0=0)
    (h3 : A 1 1=(1)*A 0 0)
    : Normal k 12 A := by
  unfold Normal
  ext r c
  fin_cases r <;> fin_cases c
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h1
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h2
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h3
theorem normal_form_13 (A : Block k)
    (h0 : A 0 0=0)
    (h1 : A 0 1=0)
    (h3 : A 1 1=(1)*A 1 0)
    : Normal k 13 A := by
  unfold Normal
  ext r c
  fin_cases r <;> fin_cases c
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h0
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h1
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
  · norm_num [project,param,coords,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
    linear_combination -h3
end UniserialComputations.N6
