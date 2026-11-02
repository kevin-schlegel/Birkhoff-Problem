import Case6Data
import N6Data

noncomputable section
namespace UniserialComputations.Uniform.Case6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
variable {R : Type*} [CommRing R] (π : R)
theorem embedding_eq_32 : Data.objects6.embedding π 32 = N6.embedding π 32 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_33 : Data.objects6.embedding π 33 = N6.embedding π 33 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_34 : Data.objects6.embedding π 34 = N6.embedding π 34 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_35 : Data.objects6.embedding π 35 = N6.embedding π 35 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_36 : Data.objects6.embedding π 36 = N6.embedding π 36 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_37 : Data.objects6.embedding π 37 = N6.embedding π 37 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_38 : Data.objects6.embedding π 38 = N6.embedding π 38 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_39 : Data.objects6.embedding π 39 = N6.embedding π 39 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
end UniserialComputations.Uniform.Case6
