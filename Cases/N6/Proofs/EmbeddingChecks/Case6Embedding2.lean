import Case6Data
import N6Data

noncomputable section
namespace UniserialComputations.Uniform.Case6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
variable {R : Type*} [CommRing R] (π : R)
theorem embedding_eq_16 : Data.objects6.embedding π 16 = N6.embedding π 16 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_17 : Data.objects6.embedding π 17 = N6.embedding π 17 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_18 : Data.objects6.embedding π 18 = N6.embedding π 18 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_19 : Data.objects6.embedding π 19 = N6.embedding π 19 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_20 : Data.objects6.embedding π 20 = N6.embedding π 20 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_21 : Data.objects6.embedding π 21 = N6.embedding π 21 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_22 : Data.objects6.embedding π 22 = N6.embedding π 22 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_23 : Data.objects6.embedding π 23 = N6.embedding π 23 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
end UniserialComputations.Uniform.Case6
