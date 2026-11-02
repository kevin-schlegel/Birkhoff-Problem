import Case6Data
import N6Data

noncomputable section
namespace UniserialComputations.Uniform.Case6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
variable {R : Type*} [CommRing R] (π : R)
theorem embedding_eq_24 : Data.objects6.embedding π 24 = N6.embedding π 24 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_25 : Data.objects6.embedding π 25 = N6.embedding π 25 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_26 : Data.objects6.embedding π 26 = N6.embedding π 26 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_27 : Data.objects6.embedding π 27 = N6.embedding π 27 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_28 : Data.objects6.embedding π 28 = N6.embedding π 28 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_29 : Data.objects6.embedding π 29 = N6.embedding π 29 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_30 : Data.objects6.embedding π 30 = N6.embedding π 30 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_31 : Data.objects6.embedding π 31 = N6.embedding π 31 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
end UniserialComputations.Uniform.Case6
