import Case5OrdinaryResidues
import UniformOrdinaryLocal

/-! Embeddings and ordinary locality for the additional length-5 objects. -/

noncomputable section
namespace UniserialComputations.Uniform.Case5
set_option maxHeartbeats 5000000
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h : RingParameters 5 R k π ρ)
include h

theorem embedding_33 : Data.additional5.IsEmbedding π 0 := by
  constructor
  · intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [ObjectFamily.embedding, Data.additional5]
    all_goals ring_nf
    all_goals exact h.power_zero _ (by decide)
  · intro x hx
    have h0 := hx 0
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0
    have h1 := hx 1
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h1
    have h2 := hx 2
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h2
    have hn : π ^ 5 = 0 := h.nilpotent
    intro c
    fin_cases c
    · change π ^ 2 * x 0 = 0
      linear_combination (1) * π ^ 0 * h0 + ((-1) * π ^ 0 * x 1) * hn
    · change π ^ 4 * x 1 = 0
      linear_combination (-1) * π ^ 1 * h0 + (1) * π ^ 0 * h1 + ((1) * π ^ 1 * x 1) * hn

theorem embedding_35 : Data.additional5.IsEmbedding π 1 := by
  constructor
  · intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [ObjectFamily.embedding, Data.additional5]
    all_goals ring_nf
    all_goals exact h.power_zero _ (by decide)
  · intro x hx
    have h0 := hx 0
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0
    have h1 := hx 1
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h1
    have h2 := hx 2
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h2
    have hn : π ^ 5 = 0 := h.nilpotent
    intro c
    fin_cases c
    · change π ^ 1 * x 0 = 0
      linear_combination (1) * π ^ 0 * h0 + ((-1) * π ^ 0 * x 1) * hn
    · change π ^ 4 * x 1 = 0
      linear_combination (-1) * π ^ 2 * h0 + (1) * π ^ 0 * h1 + ((1) * π ^ 2 * x 1) * hn

theorem embedding_38 : Data.additional5.IsEmbedding π 2 := by
  constructor
  · intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [ObjectFamily.embedding, Data.additional5]
    all_goals ring_nf
    all_goals exact h.power_zero _ (by decide)
  · intro x hx
    have h0 := hx 0
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0
    have h1 := hx 1
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h1
    have h2 := hx 2
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h2
    have hn : π ^ 5 = 0 := h.nilpotent
    intro c
    fin_cases c
    · change π ^ 2 * x 0 = 0
      linear_combination (1) * π ^ 0 * h0 + ((-1) * π ^ 0 * x 1) * hn
    · change π ^ 4 * x 1 = 0
      linear_combination (-1) * π ^ 1 * h0 + (1) * π ^ 0 * h1 + ((1) * π ^ 1 * x 1) * hn

theorem embedding_40 : Data.additional5.IsEmbedding π 3 := by
  constructor
  · intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [ObjectFamily.embedding, Data.additional5]
    all_goals ring_nf
    all_goals exact h.power_zero _ (by decide)
  · intro x hx
    have h0 := hx 0
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0
    have h1 := hx 1
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h1
    have h2 := hx 2
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h2
    have hn : π ^ 5 = 0 := h.nilpotent
    intro c
    fin_cases c
    · change π ^ 1 * x 0 = 0
      linear_combination (1) * π ^ 0 * h0 + ((-1) * π ^ 0 * x 1) * hn
    · change π ^ 4 * x 1 = 0
      linear_combination (-1) * π ^ 1 * h0 + (1) * π ^ 0 * h1 + ((1) * π ^ 1 * x 1) * hn

theorem embedding_41 : Data.additional5.IsEmbedding π 4 := by
  constructor
  · intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [ObjectFamily.embedding, Data.additional5]
    all_goals ring_nf
    all_goals exact h.power_zero _ (by decide)
  · intro x hx
    have h0 := hx 0
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0
    have h1 := hx 1
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h1
    have h2 := hx 2
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h2
    have hn : π ^ 5 = 0 := h.nilpotent
    intro c
    fin_cases c
    · change π ^ 1 * x 0 = 0
      linear_combination (1) * π ^ 0 * h0 + ((-1) * π ^ 0 * x 1) * hn
    · change π ^ 3 * x 1 = 0
      linear_combination (-1) * π ^ 1 * h0 + (1) * π ^ 0 * h1 + ((1) * π ^ 1 * x 1) * hn

theorem embedding_42 : Data.additional5.IsEmbedding π 5 := by
  constructor
  · intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [ObjectFamily.embedding, Data.additional5]
    all_goals ring_nf
    all_goals exact h.power_zero _ (by decide)
  · intro x hx
    have h0 := hx 0
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0
    have h1 := hx 1
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h1
    have h2 := hx 2
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h2
    have hn : π ^ 5 = 0 := h.nilpotent
    intro c
    fin_cases c
    · change π ^ 1 * x 0 = 0
      linear_combination (1) * π ^ 0 * h0 + ((-1) * π ^ 0 * x 1) * hn
    · change π ^ 3 * x 1 = 0
      linear_combination (-1) * π ^ 1 * h0 + (1) * π ^ 0 * h1 + ((1) * π ^ 1 * x 1) * hn

theorem embedding_44 : Data.additional5.IsEmbedding π 6 := by
  constructor
  · intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [ObjectFamily.embedding, Data.additional5]
    all_goals ring_nf
    all_goals exact h.power_zero _ (by decide)
  · intro x hx
    have h0 := hx 0
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0
    have h1 := hx 1
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h1
    have h2 := hx 2
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h2
    have hn : π ^ 5 = 0 := h.nilpotent
    intro c
    fin_cases c
    · change π ^ 2 * x 0 = 0
      linear_combination (1) * π ^ 0 * h0 + ((-1) * π ^ 0 * x 1) * hn
    · change π ^ 4 * x 1 = 0
      linear_combination (-1) * π ^ 1 * h0 + (1) * π ^ 0 * h1 + ((1) * π ^ 1 * x 1) * hn

theorem embedding_45 : Data.additional5.IsEmbedding π 7 := by
  constructor
  · intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [ObjectFamily.embedding, Data.additional5]
    all_goals ring_nf
    all_goals exact h.power_zero _ (by decide)
  · intro x hx
    have h0 := hx 0
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0
    have h1 := hx 1
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h1
    have h2 := hx 2
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h2
    have hn : π ^ 5 = 0 := h.nilpotent
    intro c
    fin_cases c
    · change π ^ 2 * x 0 = 0
      linear_combination (1) * π ^ 0 * h0 + ((-1) * π ^ 0 * x 1) * hn
    · change π ^ 3 * x 1 = 0
      linear_combination (-1) * π ^ 1 * h0 + (1) * π ^ 0 * h1 + ((1) * π ^ 1 * x 1) * hn

theorem embedding_46 : Data.additional5.IsEmbedding π 8 := by
  constructor
  · intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [ObjectFamily.embedding, Data.additional5]
    all_goals ring_nf
    all_goals exact h.power_zero _ (by decide)
  · intro x hx
    have h0 := hx 0
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0
    have h1 := hx 1
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h1
    have h2 := hx 2
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h2
    have hn : π ^ 5 = 0 := h.nilpotent
    intro c
    fin_cases c
    · change π ^ 2 * x 0 = 0
      linear_combination (1) * π ^ 0 * h0 + ((-1) * π ^ 0 * x 1) * hn
    · change π ^ 4 * x 1 = 0
      linear_combination (-1) * π ^ 1 * h0 + (1) * π ^ 0 * h2 + ((1) * π ^ 1 * x 1) * hn

theorem embedding_47 : Data.additional5.IsEmbedding π 9 := by
  constructor
  · intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [ObjectFamily.embedding, Data.additional5]
    all_goals ring_nf
    all_goals exact h.power_zero _ (by decide)
  · intro x hx
    have h0 := hx 0
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0
    have h1 := hx 1
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h1
    have h2 := hx 2
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h2
    have hn : π ^ 5 = 0 := h.nilpotent
    intro c
    fin_cases c
    · change π ^ 1 * x 0 = 0
      linear_combination (1) * π ^ 0 * h0 + ((-1) * π ^ 0 * x 1) * hn
    · change π ^ 3 * x 1 = 0
      linear_combination (-1) * π ^ 1 * h0 + (1) * π ^ 0 * h1 + ((1) * π ^ 1 * x 1) * hn

theorem embedding_48 : Data.additional5.IsEmbedding π 10 := by
  constructor
  · intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [ObjectFamily.embedding, Data.additional5]
    all_goals ring_nf
    all_goals exact h.power_zero _ (by decide)
  · intro x hx
    have h0 := hx 0
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0
    have h1 := hx 1
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h1
    have h2 := hx 2
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h2
    have hn : π ^ 5 = 0 := h.nilpotent
    intro c
    fin_cases c
    · change π ^ 2 * x 0 = 0
      linear_combination (1) * π ^ 0 * h1 + ((-1) * π ^ 1 * x 1) * hn
    · change π ^ 3 * x 1 = 0
      linear_combination (1) * π ^ 0 * h0 + ((-1) * π ^ 0 * x 0) * hn

theorem embedding_49 : Data.additional5.IsEmbedding π 11 := by
  constructor
  · intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [ObjectFamily.embedding, Data.additional5]
    all_goals ring_nf
    all_goals exact h.power_zero _ (by decide)
  · intro x hx
    have h0 := hx 0
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0
    have h1 := hx 1
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h1
    have h2 := hx 2
    norm_num [ObjectFamily.embedding, Data.additional5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h2
    have hn : π ^ 5 = 0 := h.nilpotent
    intro c
    fin_cases c
    · change π ^ 1 * x 0 = 0
      linear_combination (1) * π ^ 0 * h0 + ((-1) * π ^ 0 * x 1) * hn
    · change π ^ 3 * x 1 = 0
      linear_combination (1) * π ^ 0 * h1 + ((-1) * π ^ 1 * x 0) * hn

theorem embeddings (i : Fin Data.additional5.vertices) : Data.additional5.IsEmbedding π i := by
  fin_cases i
  · exact embedding_33 π ρ h
  · exact embedding_35 π ρ h
  · exact embedding_38 π ρ h
  · exact embedding_40 π ρ h
  · exact embedding_41 π ρ h
  · exact embedding_42 π ρ h
  · exact embedding_44 π ρ h
  · exact embedding_45 π ρ h
  · exact embedding_46 π ρ h
  · exact embedding_47 π ρ h
  · exact embedding_48 π ρ h
  · exact embedding_49 π ρ h

theorem ordinary_local (i : Fin Data.additional5.vertices) :
    IsLocalRing (Data.additional5.OrdinaryEnd π ρ h i) := by
  apply Data.additional5.ordinary_local_of_diagonal_residues π ρ h i 0
  · fin_cases i <;> rfl
  · fin_cases i <;> decide
  · fin_cases i <;> decide
  · intro f
    fin_cases i
    · constructor
      · intro a ha
        fin_cases a
        · rfl
        · exact residue_ambient_33_1 π ρ h f
        · norm_num [Data.additional5] at ha
      · intro a
        fin_cases a
        · exact residue_source_33_0 π ρ h f
        · exact residue_source_33_1 π ρ h f
    · constructor
      · intro a ha
        fin_cases a
        · rfl
        · exact residue_ambient_35_1 π ρ h f
        · norm_num [Data.additional5] at ha
      · intro a
        fin_cases a
        · exact residue_source_35_0 π ρ h f
        · exact residue_source_35_1 π ρ h f
    · constructor
      · intro a ha
        fin_cases a
        · rfl
        · exact residue_ambient_38_1 π ρ h f
        · norm_num [Data.additional5] at ha
      · intro a
        fin_cases a
        · exact residue_source_38_0 π ρ h f
        · exact residue_source_38_1 π ρ h f
    · constructor
      · intro a ha
        fin_cases a
        · rfl
        · exact residue_ambient_40_1 π ρ h f
        · norm_num [Data.additional5] at ha
      · intro a
        fin_cases a
        · exact residue_source_40_0 π ρ h f
        · exact residue_source_40_1 π ρ h f
    · constructor
      · intro a ha
        fin_cases a
        · rfl
        · exact residue_ambient_41_1 π ρ h f
        · norm_num [Data.additional5] at ha
      · intro a
        fin_cases a
        · exact residue_source_41_0 π ρ h f
        · exact residue_source_41_1 π ρ h f
    · constructor
      · intro a ha
        fin_cases a
        · rfl
        · exact residue_ambient_42_1 π ρ h f
        · exact residue_ambient_42_2 π ρ h f
      · intro a
        fin_cases a
        · exact residue_source_42_0 π ρ h f
        · exact residue_source_42_1 π ρ h f
    · constructor
      · intro a ha
        fin_cases a
        · rfl
        · exact residue_ambient_44_1 π ρ h f
        · exact residue_ambient_44_2 π ρ h f
      · intro a
        fin_cases a
        · exact residue_source_44_0 π ρ h f
        · exact residue_source_44_1 π ρ h f
    · constructor
      · intro a ha
        fin_cases a
        · rfl
        · exact residue_ambient_45_1 π ρ h f
        · exact residue_ambient_45_2 π ρ h f
      · intro a
        fin_cases a
        · exact residue_source_45_0 π ρ h f
        · exact residue_source_45_1 π ρ h f
    · constructor
      · intro a ha
        fin_cases a
        · rfl
        · exact residue_ambient_46_1 π ρ h f
        · exact residue_ambient_46_2 π ρ h f
      · intro a
        fin_cases a
        · exact residue_source_46_0 π ρ h f
        · exact residue_source_46_1 π ρ h f
    · constructor
      · intro a ha
        fin_cases a
        · rfl
        · exact residue_ambient_47_1 π ρ h f
        · exact residue_ambient_47_2 π ρ h f
      · intro a
        fin_cases a
        · exact residue_source_47_0 π ρ h f
        · exact residue_source_47_1 π ρ h f
    · constructor
      · intro a ha
        fin_cases a
        · rfl
        · exact residue_ambient_48_1 π ρ h f
        · exact residue_ambient_48_2 π ρ h f
      · intro a
        fin_cases a
        · exact residue_source_48_0 π ρ h f
        · exact residue_source_48_1 π ρ h f
    · constructor
      · intro a ha
        fin_cases a
        · rfl
        · exact residue_ambient_49_1 π ρ h f
        · exact residue_ambient_49_2 π ρ h f
      · intro a
        fin_cases a
        · exact residue_source_49_0 π ρ h f
        · exact residue_source_49_1 π ρ h f

end UniserialComputations.Uniform.Case5
