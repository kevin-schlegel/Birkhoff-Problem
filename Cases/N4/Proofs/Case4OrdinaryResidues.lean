import Case4Additional

/-! Residue constraints for the additional length-4 embeddings. -/

noncomputable section
namespace UniserialComputations.Uniform.Case4
set_option maxHeartbeats 5000000

theorem residue_ambient_26_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 4 R k π ρ)
    (f : Data.additional4.Hom π 0 0) :
    ρ (f.ambient 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 4 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h8 := f.commutes 0 0
  norm_num [Data.additional4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h8
  have h10 := f.commutes 1 0
  norm_num [Data.additional4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h10
  have ht : π ^ (4-1) * (f.ambient 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (-1) * π ^ 2 * h8 + (1) * π ^ 1 * h10 + ((-1) * π ^ 0 * (f.ambient 1 0) + (1) * π ^ 0 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_26_0 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 4 R k π ρ)
    (f : Data.additional4.Hom π 0 0) :
    ρ (f.source 0 0) = ρ (f.ambient 0 0) := by
  have hn : π ^ 4 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h8 := f.commutes 0 0
  norm_num [Data.additional4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h8
  have ht : π ^ (4-1) * (f.source 0 0 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (-1) * π ^ 2 * h8
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_26_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 4 R k π ρ)
    (f : Data.additional4.Hom π 0 0) :
    ρ (f.source 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 4 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h5 := f.source_descent 0 1
  norm_num [Data.additional4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h5
  have h8 := f.commutes 0 0
  norm_num [Data.additional4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h8
  have h10 := f.commutes 1 0
  norm_num [Data.additional4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h10
  have h11 := f.commutes 1 1
  norm_num [Data.additional4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h11
  have ht : π ^ (4-1) * (f.source 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (-1) * π ^ 0 * h5 + (-1) * π ^ 2 * h8 + (1) * π ^ 1 * h10 + (-1) * π ^ 0 * h11 + ((-1) * π ^ 0 * (f.ambient 1 0) + (1) * π ^ 0 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

end UniserialComputations.Uniform.Case4
