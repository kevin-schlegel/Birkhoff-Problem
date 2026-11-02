import Case6Data
import N6Data

noncomputable section
namespace UniserialComputations.Uniform.Case6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
variable {R : Type*} [CommRing R] (π : R)
theorem embedding_eq_40 : Data.objects6.embedding π 40 = N6.embedding π 40 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_41 : Data.objects6.embedding π 41 = N6.embedding π 41 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_42 : Data.objects6.embedding π 42 = N6.embedding π 42 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_43 : Data.objects6.embedding π 43 = N6.embedding π 43 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_44 : Data.objects6.embedding π 44 = N6.embedding π 44 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_45 : Data.objects6.embedding π 45 = N6.embedding π 45 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
theorem embedding_eq_46 : Data.objects6.embedding π 46 = N6.embedding π 46 := by
  ext r c
  fin_cases r <;> fin_cases c
  all_goals norm_num [Data.objects6, ObjectFamily.embedding, N6.embedding]
end UniserialComputations.Uniform.Case6
