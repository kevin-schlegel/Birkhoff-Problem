import Case6Data
import N6Data

noncomputable section
namespace UniserialComputations.Uniform.Case6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
variable {R : Type*} [CommRing R] (π : R)
theorem embedding_eq_0 : Data.objects6.embedding π 0 = N6.embedding π 0 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_1 : Data.objects6.embedding π 1 = N6.embedding π 1 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_2 : Data.objects6.embedding π 2 = N6.embedding π 2 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_3 : Data.objects6.embedding π 3 = N6.embedding π 3 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_4 : Data.objects6.embedding π 4 = N6.embedding π 4 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_5 : Data.objects6.embedding π 5 = N6.embedding π 5 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_6 : Data.objects6.embedding π 6 = N6.embedding π 6 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_7 : Data.objects6.embedding π 7 = N6.embedding π 7 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
end UniserialComputations.Uniform.Case6
