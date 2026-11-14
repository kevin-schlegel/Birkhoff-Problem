import Case5Additional

/-! Residue constraints for the additional length-5 embeddings. -/

noncomputable section
namespace UniserialComputations.Uniform.Case5
set_option maxHeartbeats 5000000

theorem residue_ambient_33_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 0 0) :
    ρ (f.ambient 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h15 := f.commutes 1 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h15
  have ht : π ^ (5-1) * (f.ambient 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (-1) * π ^ 2 * h13 + (1) * π ^ 1 * h15 + ((1) * π ^ 2 * (f.ambient 0 2) + (-1) * π ^ 1 * (f.ambient 1 0) + (-1) * π ^ 4 * (f.ambient 1 2) + (1) * π ^ 0 * (f.source 1 0) + (-1) * π ^ 2 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_33_0 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 0 0) :
    ρ (f.source 0 0) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have ht : π ^ (5-1) * (f.source 0 0 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (-1) * π ^ 2 * h13 + ((1) * π ^ 2 * (f.ambient 0 2) + (-1) * π ^ 2 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_33_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 0 0) :
    ρ (f.source 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h10 := f.source_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h10
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h15 := f.commutes 1 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h15
  have h16 := f.commutes 1 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h16
  have ht : π ^ (5-1) * (f.source 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (-1) * π ^ 0 * h10 + (-1) * π ^ 2 * h13 + (1) * π ^ 1 * h15 + (-1) * π ^ 0 * h16 + ((1) * π ^ 2 * (f.ambient 0 2) + (-1) * π ^ 1 * (f.ambient 1 0) + (1) * π ^ 3 * (f.ambient 1 0) + (1) * π ^ 3 * (f.ambient 1 2) + (-1) * π ^ 4 * (f.ambient 1 2) + (1) * π ^ 0 * (f.source 1 0) + (-1) * π ^ 2 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_ambient_35_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 1 1) :
    ρ (f.ambient 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h15 := f.commutes 1 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h15
  have ht : π ^ (5-1) * (f.ambient 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 1 * h1 + (-1) * π ^ 3 * h13 + (1) * π ^ 1 * h15 + ((1) * π ^ 3 * (f.ambient 0 2) + (-1) * π ^ 0 * (f.ambient 1 0) + (-1) * π ^ 4 * (f.ambient 1 2) + (1) * π ^ 0 * (f.source 1 0) + (-1) * π ^ 3 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_35_0 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 1 1) :
    ρ (f.source 0 0) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have ht : π ^ (5-1) * (f.source 0 0 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 1 * h1 + (-1) * π ^ 3 * h13 + ((1) * π ^ 3 * (f.ambient 0 2) + (-1) * π ^ 3 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_35_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 1 1) :
    ρ (f.source 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h10 := f.source_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h10
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h15 := f.commutes 1 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h15
  have h16 := f.commutes 1 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h16
  have ht : π ^ (5-1) * (f.source 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 1 * h1 + (-1) * π ^ 1 * h10 + (-1) * π ^ 3 * h13 + (1) * π ^ 1 * h15 + (-1) * π ^ 0 * h16 + ((1) * π ^ 3 * (f.ambient 0 2) + (-1) * π ^ 0 * (f.ambient 1 0) + (1) * π ^ 3 * (f.ambient 1 0) + (1) * π ^ 3 * (f.ambient 1 2) + (-1) * π ^ 4 * (f.ambient 1 2) + (1) * π ^ 0 * (f.source 1 0) + (-1) * π ^ 3 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_ambient_38_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 2 2) :
    ρ (f.ambient 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h15 := f.commutes 1 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h15
  have ht : π ^ (5-1) * (f.ambient 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (-1) * π ^ 2 * h13 + (1) * π ^ 1 * h15 + ((1) * π ^ 2 * (f.ambient 0 2) + (-1) * π ^ 0 * (f.ambient 1 0) + (-1) * π ^ 3 * (f.ambient 1 2) + (1) * π ^ 0 * (f.source 1 0) + (-1) * π ^ 2 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_38_0 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 2 2) :
    ρ (f.source 0 0) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have ht : π ^ (5-1) * (f.source 0 0 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (-1) * π ^ 2 * h13 + ((1) * π ^ 2 * (f.ambient 0 2) + (-1) * π ^ 2 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_38_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 2 2) :
    ρ (f.source 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h10 := f.source_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h10
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h15 := f.commutes 1 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h15
  have h16 := f.commutes 1 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h16
  have ht : π ^ (5-1) * (f.source 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (-1) * π ^ 0 * h10 + (-1) * π ^ 2 * h13 + (1) * π ^ 1 * h15 + (-1) * π ^ 0 * h16 + ((1) * π ^ 2 * (f.ambient 0 2) + (-1) * π ^ 0 * (f.ambient 1 0) + (1) * π ^ 2 * (f.ambient 1 0) + (1) * π ^ 2 * (f.ambient 1 2) + (-1) * π ^ 3 * (f.ambient 1 2) + (1) * π ^ 0 * (f.source 1 0) + (-1) * π ^ 2 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_ambient_40_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 3 3) :
    ρ (f.ambient 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h15 := f.commutes 1 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h15
  have ht : π ^ (5-1) * (f.ambient 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (-1) * π ^ 3 * h13 + (1) * π ^ 2 * h15 + ((1) * π ^ 3 * (f.ambient 0 2) + (-1) * π ^ 0 * (f.ambient 1 0) + (-1) * π ^ 4 * (f.ambient 1 2) + (1) * π ^ 1 * (f.source 1 0) + (-1) * π ^ 3 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_40_0 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 3 3) :
    ρ (f.source 0 0) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have ht : π ^ (5-1) * (f.source 0 0 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (-1) * π ^ 3 * h13 + ((1) * π ^ 3 * (f.ambient 0 2) + (-1) * π ^ 3 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_40_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 3 3) :
    ρ (f.source 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h10 := f.source_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h10
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h15 := f.commutes 1 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h15
  have h16 := f.commutes 1 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h16
  have ht : π ^ (5-1) * (f.source 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (-1) * π ^ 0 * h10 + (-1) * π ^ 3 * h13 + (1) * π ^ 2 * h15 + (-1) * π ^ 0 * h16 + ((1) * π ^ 3 * (f.ambient 0 2) + (-1) * π ^ 0 * (f.ambient 1 0) + (1) * π ^ 2 * (f.ambient 1 0) + (1) * π ^ 2 * (f.ambient 1 2) + (-1) * π ^ 4 * (f.ambient 1 2) + (1) * π ^ 1 * (f.source 1 0) + (-1) * π ^ 3 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_ambient_41_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 4 4) :
    ρ (f.ambient 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h15 := f.commutes 1 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h15
  have ht : π ^ (5-1) * (f.ambient 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (-1) * π ^ 3 * h13 + (1) * π ^ 2 * h15 + ((1) * π ^ 3 * (f.ambient 0 2) + (-1) * π ^ 0 * (f.ambient 1 0) + (-1) * π ^ 4 * (f.ambient 1 2) + (1) * π ^ 0 * (f.source 1 0) + (-1) * π ^ 3 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_41_0 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 4 4) :
    ρ (f.source 0 0) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have ht : π ^ (5-1) * (f.source 0 0 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (-1) * π ^ 3 * h13 + ((1) * π ^ 3 * (f.ambient 0 2) + (-1) * π ^ 3 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_41_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 4 4) :
    ρ (f.source 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h10 := f.source_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h10
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h15 := f.commutes 1 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h15
  have h16 := f.commutes 1 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h16
  have ht : π ^ (5-1) * (f.source 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (-1) * π ^ 0 * h10 + (-1) * π ^ 3 * h13 + (1) * π ^ 2 * h15 + (-1) * π ^ 1 * h16 + ((1) * π ^ 3 * (f.ambient 0 2) + (-1) * π ^ 0 * (f.ambient 1 0) + (1) * π ^ 3 * (f.ambient 1 0) + (1) * π ^ 3 * (f.ambient 1 2) + (-1) * π ^ 4 * (f.ambient 1 2) + (1) * π ^ 0 * (f.source 1 0) + (-1) * π ^ 3 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_ambient_42_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 5 5) :
    ρ (f.ambient 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h15 := f.commutes 1 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h15
  have ht : π ^ (5-1) * (f.ambient 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (-1) * π ^ 3 * h13 + (1) * π ^ 2 * h15 + ((1) * π ^ 3 * (f.ambient 0 2) + (-1) * π ^ 0 * (f.ambient 1 0) + (-1) * π ^ 4 * (f.ambient 1 2) + (1) * π ^ 0 * (f.source 1 0) + (-1) * π ^ 3 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_ambient_42_2 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 5 5) :
    ρ (f.ambient 2 2) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h5 := f.ambient_descent 1 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h5
  have h10 := f.source_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h10
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h15 := f.commutes 1 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h15
  have h16 := f.commutes 1 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h16
  have h18 := f.commutes 2 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h18
  have ht : π ^ (5-1) * (f.ambient 2 2 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (1) * π ^ 0 * h5 + (-1) * π ^ 0 * h10 + (-1) * π ^ 3 * h13 + (1) * π ^ 2 * h15 + (-1) * π ^ 1 * h16 + (1) * π ^ 0 * h18 + ((1) * π ^ 3 * (f.ambient 0 2) + (-1) * π ^ 0 * (f.ambient 1 0) + (1) * π ^ 3 * (f.ambient 1 0) + (-1) * π ^ 4 * (f.ambient 1 2) + (-1) * π ^ 4 * (f.ambient 2 0) + (-1) * π ^ 0 * (f.ambient 2 1) + (1) * π ^ 4 * (f.source 0 1) + (1) * π ^ 0 * (f.source 1 0) + (-1) * π ^ 3 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_42_0 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 5 5) :
    ρ (f.source 0 0) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have ht : π ^ (5-1) * (f.source 0 0 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (-1) * π ^ 3 * h13 + ((1) * π ^ 3 * (f.ambient 0 2) + (-1) * π ^ 3 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_42_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 5 5) :
    ρ (f.source 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h5 := f.ambient_descent 1 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h5
  have h10 := f.source_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h10
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h15 := f.commutes 1 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h15
  have h16 := f.commutes 1 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h16
  have ht : π ^ (5-1) * (f.source 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (1) * π ^ 0 * h5 + (-1) * π ^ 0 * h10 + (-1) * π ^ 3 * h13 + (1) * π ^ 2 * h15 + (-1) * π ^ 1 * h16 + ((1) * π ^ 3 * (f.ambient 0 2) + (-1) * π ^ 0 * (f.ambient 1 0) + (1) * π ^ 3 * (f.ambient 1 0) + (-1) * π ^ 4 * (f.ambient 1 2) + (1) * π ^ 0 * (f.source 1 0) + (-1) * π ^ 3 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_ambient_44_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 6 6) :
    ρ (f.ambient 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h2 := f.ambient_descent 0 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h2
  have h5 := f.ambient_descent 1 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h5
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h15 := f.commutes 1 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h15
  have ht : π ^ (5-1) * (f.ambient 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (1) * π ^ 1 * h2 + (-1) * π ^ 0 * h5 + (-1) * π ^ 2 * h13 + (1) * π ^ 1 * h15 + ((-1) * π ^ 0 * (f.ambient 1 0) + (1) * π ^ 0 * (f.source 1 0) + (-1) * π ^ 2 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_ambient_44_2 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 6 6) :
    ρ (f.ambient 2 2) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h2 := f.ambient_descent 0 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h2
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h17 := f.commutes 2 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h17
  have ht : π ^ (5-1) * (f.ambient 2 2 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (1) * π ^ 1 * h2 + (-1) * π ^ 2 * h13 + (1) * π ^ 0 * h17 + ((-1) * π ^ 1 * (f.ambient 2 0) + (-1) * π ^ 0 * (f.ambient 2 1) + (-1) * π ^ 2 * (f.source 1 0) + (1) * π ^ 4 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_44_0 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 6 6) :
    ρ (f.source 0 0) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h2 := f.ambient_descent 0 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h2
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have ht : π ^ (5-1) * (f.source 0 0 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (1) * π ^ 1 * h2 + (-1) * π ^ 2 * h13 + ((-1) * π ^ 2 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_44_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 6 6) :
    ρ (f.source 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h2 := f.ambient_descent 0 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h2
  have h5 := f.ambient_descent 1 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h5
  have h10 := f.source_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h10
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h15 := f.commutes 1 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h15
  have h16 := f.commutes 1 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h16
  have ht : π ^ (5-1) * (f.source 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (1) * π ^ 1 * h2 + (-1) * π ^ 0 * h5 + (-1) * π ^ 0 * h10 + (-1) * π ^ 2 * h13 + (1) * π ^ 1 * h15 + (-1) * π ^ 0 * h16 + ((-1) * π ^ 0 * (f.ambient 1 0) + (1) * π ^ 2 * (f.ambient 1 0) + (1) * π ^ 2 * (f.ambient 1 2) + (1) * π ^ 0 * (f.source 1 0) + (-1) * π ^ 2 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_ambient_45_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 7 7) :
    ρ (f.ambient 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h15 := f.commutes 1 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h15
  have h17 := f.commutes 2 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h17
  have ht : π ^ (5-1) * (f.ambient 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (-1) * π ^ 2 * h13 + (1) * π ^ 1 * h15 + (-1) * π ^ 0 * h17 + ((1) * π ^ 2 * (f.ambient 0 2) + (-1) * π ^ 0 * (f.ambient 1 0) + (-1) * π ^ 3 * (f.ambient 1 2) + (1) * π ^ 1 * (f.ambient 2 0) + (1) * π ^ 0 * (f.ambient 2 1) + (1) * π ^ 4 * (f.ambient 2 2) + (-1) * π ^ 4 * (f.source 0 0) + (-1) * π ^ 2 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_ambient_45_2 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 7 7) :
    ρ (f.ambient 2 2) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h5 := f.ambient_descent 1 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h5
  have h10 := f.source_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h10
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h15 := f.commutes 1 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h15
  have h16 := f.commutes 1 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h16
  have h17 := f.commutes 2 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h17
  have h18 := f.commutes 2 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h18
  have ht : π ^ (5-1) * (f.ambient 2 2 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (1) * π ^ 0 * h5 + (-1) * π ^ 0 * h10 + (-1) * π ^ 2 * h13 + (1) * π ^ 1 * h15 + (-1) * π ^ 1 * h16 + (-1) * π ^ 0 * h17 + (1) * π ^ 0 * h18 + ((1) * π ^ 2 * (f.ambient 0 2) + (-1) * π ^ 0 * (f.ambient 1 0) + (1) * π ^ 3 * (f.ambient 1 0) + (-1) * π ^ 3 * (f.ambient 1 2) + (1) * π ^ 1 * (f.ambient 2 0) + (-1) * π ^ 4 * (f.ambient 2 0) + (1) * π ^ 4 * (f.ambient 2 2) + (-1) * π ^ 4 * (f.source 0 0) + (1) * π ^ 4 * (f.source 0 1) + (-1) * π ^ 2 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_45_0 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 7 7) :
    ρ (f.source 0 0) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have ht : π ^ (5-1) * (f.source 0 0 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (-1) * π ^ 2 * h13 + ((1) * π ^ 2 * (f.ambient 0 2) + (-1) * π ^ 2 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_45_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 7 7) :
    ρ (f.source 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h5 := f.ambient_descent 1 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h5
  have h10 := f.source_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h10
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h15 := f.commutes 1 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h15
  have h16 := f.commutes 1 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h16
  have h17 := f.commutes 2 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h17
  have ht : π ^ (5-1) * (f.source 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (1) * π ^ 0 * h5 + (-1) * π ^ 0 * h10 + (-1) * π ^ 2 * h13 + (1) * π ^ 1 * h15 + (-1) * π ^ 1 * h16 + (-1) * π ^ 0 * h17 + ((1) * π ^ 2 * (f.ambient 0 2) + (-1) * π ^ 0 * (f.ambient 1 0) + (1) * π ^ 3 * (f.ambient 1 0) + (-1) * π ^ 3 * (f.ambient 1 2) + (1) * π ^ 1 * (f.ambient 2 0) + (1) * π ^ 0 * (f.ambient 2 1) + (1) * π ^ 4 * (f.ambient 2 2) + (-1) * π ^ 4 * (f.source 0 0) + (-1) * π ^ 2 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_ambient_46_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 8 8) :
    ρ (f.ambient 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h2 := f.ambient_descent 0 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h2
  have h10 := f.source_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h10
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h15 := f.commutes 1 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h15
  have h16 := f.commutes 1 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h16
  have ht : π ^ (5-1) * (f.ambient 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (1) * π ^ 0 * h2 + (-1) * π ^ 0 * h10 + (-1) * π ^ 2 * h13 + (1) * π ^ 1 * h15 + (-1) * π ^ 0 * h16 + ((-1) * π ^ 0 * (f.ambient 1 0) + (1) * π ^ 2 * (f.ambient 1 0) + (1) * π ^ 2 * (f.ambient 1 1) + (-1) * π ^ 2 * (f.source 1 0) + (1) * π ^ 3 * (f.source 1 0) + (-1) * π ^ 2 * (f.source 1 1)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_ambient_46_2 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 8 8) :
    ρ (f.ambient 2 2) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h2 := f.ambient_descent 0 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h2
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h17 := f.commutes 2 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h17
  have ht : π ^ (5-1) * (f.ambient 2 2 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (1) * π ^ 0 * h2 + (-1) * π ^ 2 * h13 + (1) * π ^ 1 * h17 + ((-1) * π ^ 1 * (f.ambient 2 0) + (-1) * π ^ 0 * (f.ambient 2 1) + (1) * π ^ 0 * (f.source 1 0) + (-1) * π ^ 2 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_46_0 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 8 8) :
    ρ (f.source 0 0) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h2 := f.ambient_descent 0 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h2
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have ht : π ^ (5-1) * (f.source 0 0 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (1) * π ^ 0 * h2 + (-1) * π ^ 2 * h13 + ((-1) * π ^ 2 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_46_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 8 8) :
    ρ (f.source 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h2 := f.ambient_descent 0 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h2
  have h10 := f.source_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h10
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h17 := f.commutes 2 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h17
  have h18 := f.commutes 2 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h18
  have ht : π ^ (5-1) * (f.source 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (1) * π ^ 0 * h2 + (-1) * π ^ 0 * h10 + (-1) * π ^ 2 * h13 + (1) * π ^ 1 * h17 + (-1) * π ^ 0 * h18 + ((-1) * π ^ 1 * (f.ambient 2 0) + (1) * π ^ 3 * (f.ambient 2 0) + (-1) * π ^ 0 * (f.ambient 2 1) + (1) * π ^ 3 * (f.ambient 2 1) + (1) * π ^ 0 * (f.source 1 0) + (-1) * π ^ 2 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_ambient_47_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 9 9) :
    ρ (f.ambient 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h15 := f.commutes 1 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h15
  have ht : π ^ (5-1) * (f.ambient 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (-1) * π ^ 3 * h13 + (1) * π ^ 2 * h15 + ((1) * π ^ 3 * (f.ambient 0 2) + (-1) * π ^ 0 * (f.ambient 1 0) + (-1) * π ^ 4 * (f.ambient 1 2) + (1) * π ^ 0 * (f.source 1 0) + (-1) * π ^ 3 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_ambient_47_2 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 9 9) :
    ρ (f.ambient 2 2) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h5 := f.ambient_descent 1 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h5
  have h10 := f.source_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h10
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h15 := f.commutes 1 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h15
  have h16 := f.commutes 1 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h16
  have h17 := f.commutes 2 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h17
  have h18 := f.commutes 2 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h18
  have ht : π ^ (5-1) * (f.ambient 2 2 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (1) * π ^ 0 * h5 + (-1) * π ^ 0 * h10 + (-1) * π ^ 3 * h13 + (1) * π ^ 2 * h15 + (-1) * π ^ 1 * h16 + (-1) * π ^ 1 * h17 + (1) * π ^ 0 * h18 + ((1) * π ^ 3 * (f.ambient 0 2) + (-1) * π ^ 0 * (f.ambient 1 0) + (1) * π ^ 3 * (f.ambient 1 0) + (-1) * π ^ 4 * (f.ambient 1 2) + (1) * π ^ 0 * (f.ambient 2 0) + (-1) * π ^ 3 * (f.ambient 2 0) + (1) * π ^ 4 * (f.ambient 2 2) + (-1) * π ^ 4 * (f.source 0 0) + (1) * π ^ 3 * (f.source 0 1) + (-1) * π ^ 3 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_47_0 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 9 9) :
    ρ (f.source 0 0) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have ht : π ^ (5-1) * (f.source 0 0 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (-1) * π ^ 3 * h13 + ((1) * π ^ 3 * (f.ambient 0 2) + (-1) * π ^ 3 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_47_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 9 9) :
    ρ (f.source 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h1 := f.ambient_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h1
  have h5 := f.ambient_descent 1 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h5
  have h10 := f.source_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h10
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h15 := f.commutes 1 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h15
  have h16 := f.commutes 1 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h16
  have ht : π ^ (5-1) * (f.source 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h1 + (1) * π ^ 0 * h5 + (-1) * π ^ 0 * h10 + (-1) * π ^ 3 * h13 + (1) * π ^ 2 * h15 + (-1) * π ^ 1 * h16 + ((1) * π ^ 3 * (f.ambient 0 2) + (-1) * π ^ 0 * (f.ambient 1 0) + (1) * π ^ 3 * (f.ambient 1 0) + (-1) * π ^ 4 * (f.ambient 1 2) + (1) * π ^ 0 * (f.source 1 0) + (-1) * π ^ 3 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_ambient_48_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 10 10) :
    ρ (f.ambient 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h2 := f.ambient_descent 0 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h2
  have h14 := f.commutes 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h14
  have h15 := f.commutes 1 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h15
  have h16 := f.commutes 1 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h16
  have h17 := f.commutes 2 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h17
  have h18 := f.commutes 2 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h18
  have ht : π ^ (5-1) * (f.ambient 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h2 + (-1) * π ^ 1 * h14 + (1) * π ^ 2 * h15 + (-1) * π ^ 1 * h16 + (-1) * π ^ 1 * h17 + (1) * π ^ 0 * h18 + ((1) * π ^ 1 * (f.ambient 0 1) + (1) * π ^ 0 * (f.ambient 1 0) + (-1) * π ^ 3 * (f.ambient 1 0) + (1) * π ^ 2 * (f.ambient 1 1) + (-1) * π ^ 1 * (f.ambient 2 0) + (1) * π ^ 4 * (f.ambient 2 0) + (1) * π ^ 0 * (f.ambient 2 1) + (-1) * π ^ 3 * (f.ambient 2 1) + (-1) * π ^ 1 * (f.source 0 1) + (-1) * π ^ 0 * (f.source 1 0) + (1) * π ^ 3 * (f.source 1 0) + (-1) * π ^ 2 * (f.source 1 1)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_ambient_48_2 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 10 10) :
    ρ (f.ambient 2 2) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h2 := f.ambient_descent 0 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h2
  have h5 := f.ambient_descent 1 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h5
  have h14 := f.commutes 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h14
  have h16 := f.commutes 1 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h16
  have h18 := f.commutes 2 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h18
  have ht : π ^ (5-1) * (f.ambient 2 2 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h2 + (1) * π ^ 0 * h5 + (-1) * π ^ 1 * h14 + (-1) * π ^ 1 * h16 + (1) * π ^ 0 * h18 + ((1) * π ^ 1 * (f.ambient 0 1) + (1) * π ^ 0 * (f.ambient 1 0) + (1) * π ^ 2 * (f.ambient 1 1) + (-1) * π ^ 1 * (f.ambient 2 0) + (-1) * π ^ 3 * (f.ambient 2 1) + (-1) * π ^ 1 * (f.source 0 1) + (-1) * π ^ 2 * (f.source 1 1)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_48_0 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 10 10) :
    ρ (f.source 0 0) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h2 := f.ambient_descent 0 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h2
  have h5 := f.ambient_descent 1 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h5
  have h14 := f.commutes 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h14
  have h16 := f.commutes 1 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h16
  have h17 := f.commutes 2 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h17
  have h18 := f.commutes 2 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h18
  have ht : π ^ (5-1) * (f.source 0 0 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h2 + (1) * π ^ 0 * h5 + (-1) * π ^ 1 * h14 + (-1) * π ^ 1 * h16 + (-1) * π ^ 1 * h17 + (1) * π ^ 0 * h18 + ((1) * π ^ 1 * (f.ambient 0 1) + (1) * π ^ 0 * (f.ambient 1 0) + (1) * π ^ 2 * (f.ambient 1 1) + (-1) * π ^ 1 * (f.ambient 2 0) + (1) * π ^ 4 * (f.ambient 2 0) + (1) * π ^ 0 * (f.ambient 2 1) + (-1) * π ^ 3 * (f.ambient 2 1) + (-1) * π ^ 1 * (f.source 0 1) + (-1) * π ^ 0 * (f.source 1 0) + (-1) * π ^ 2 * (f.source 1 1)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_48_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 10 10) :
    ρ (f.source 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h2 := f.ambient_descent 0 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h2
  have h14 := f.commutes 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h14
  have ht : π ^ (5-1) * (f.source 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 0 * h2 + (-1) * π ^ 1 * h14 + ((1) * π ^ 1 * (f.ambient 0 1) + (-1) * π ^ 1 * (f.source 0 1)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_ambient_49_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 11 11) :
    ρ (f.ambient 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h2 := f.ambient_descent 0 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h2
  have h5 := f.ambient_descent 1 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h5
  have h10 := f.source_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h10
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h16 := f.commutes 1 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h16
  have h17 := f.commutes 2 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h17
  have h18 := f.commutes 2 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h18
  have ht : π ^ (5-1) * (f.ambient 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 1 * h2 + (-1) * π ^ 0 * h5 + (-1) * π ^ 0 * h10 + (-1) * π ^ 3 * h13 + (1) * π ^ 1 * h16 + (1) * π ^ 1 * h17 + (-1) * π ^ 0 * h18 + ((1) * π ^ 3 * (f.ambient 0 1) + (-1) * π ^ 2 * (f.ambient 1 0) + (-1) * π ^ 0 * (f.ambient 2 0) + (1) * π ^ 3 * (f.ambient 2 0) + (1) * π ^ 0 * (f.ambient 2 1) + (-1) * π ^ 4 * (f.ambient 2 1) + (1) * π ^ 2 * (f.source 0 1) + (1) * π ^ 0 * (f.source 1 0) + (-1) * π ^ 3 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_ambient_49_2 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 11 11) :
    ρ (f.ambient 2 2) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h2 := f.ambient_descent 0 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h2
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h17 := f.commutes 2 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h17
  have ht : π ^ (5-1) * (f.ambient 2 2 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 1 * h2 + (-1) * π ^ 3 * h13 + (1) * π ^ 1 * h17 + ((1) * π ^ 3 * (f.ambient 0 1) + (-1) * π ^ 0 * (f.ambient 2 0) + (-1) * π ^ 4 * (f.ambient 2 1) + (1) * π ^ 0 * (f.source 1 0) + (-1) * π ^ 3 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_49_0 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 11 11) :
    ρ (f.source 0 0) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h2 := f.ambient_descent 0 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h2
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have ht : π ^ (5-1) * (f.source 0 0 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 1 * h2 + (-1) * π ^ 3 * h13 + ((1) * π ^ 3 * (f.ambient 0 1) + (-1) * π ^ 3 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

theorem residue_source_49_1 {R k : Type*} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters 5 R k π ρ)
    (f : Data.additional5.Hom π 11 11) :
    ρ (f.source 1 1) = ρ (f.ambient 0 0) := by
  have hn : π ^ 5 = 0 := h.nilpotent
  have h2 := f.ambient_descent 0 2
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h2
  have h10 := f.source_descent 0 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h10
  have h13 := f.commutes 0 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h13
  have h17 := f.commutes 2 0
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h17
  have h18 := f.commutes 2 1
  norm_num [Data.additional5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at h18
  have ht : π ^ (5-1) * (f.source 1 1 - f.ambient 0 0) = 0 := by
    linear_combination (1) * π ^ 1 * h2 + (-1) * π ^ 0 * h10 + (-1) * π ^ 3 * h13 + (1) * π ^ 1 * h17 + (-1) * π ^ 0 * h18 + ((1) * π ^ 3 * (f.ambient 0 1) + (-1) * π ^ 0 * (f.ambient 2 0) + (1) * π ^ 3 * (f.ambient 2 0) + (1) * π ^ 0 * (f.ambient 2 1) + (-1) * π ^ 4 * (f.ambient 2 1) + (1) * π ^ 0 * (f.source 1 0) + (-1) * π ^ 3 * (f.source 1 0)) * hn
  have hz := (h.top_annihilator _).mp ht
  simpa only [map_sub, sub_eq_zero] using hz

end UniserialComputations.Uniform.Case5
