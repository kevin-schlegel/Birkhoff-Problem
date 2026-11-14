import Case4OrdinaryResidues
import UniformOrdinaryLocal

/-! Embeddings and ordinary locality for the additional length-4 objects. -/

noncomputable section
namespace UniserialComputations.Uniform.Case4
set_option maxHeartbeats 5000000
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h : RingParameters 4 R k π ρ)
include h

theorem embedding_26 : Data.additional4.IsEmbedding π 0 := by
  constructor
  · intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [ObjectFamily.embedding, Data.additional4]
    all_goals ring_nf
    all_goals exact h.power_zero _ (by decide)
  · intro x hx
    have h0 := hx 0
    norm_num [ObjectFamily.embedding, Data.additional4, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0
    have h1 := hx 1
    norm_num [ObjectFamily.embedding, Data.additional4, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h1
    have hn : π ^ 4 = 0 := h.nilpotent
    intro c
    fin_cases c
    · change π ^ 1 * x 0 = 0
      linear_combination (1) * π ^ 0 * h0
    · change π ^ 3 * x 1 = 0
      linear_combination (-1) * π ^ 1 * h0 + (1) * π ^ 0 * h1

theorem embeddings (i : Fin Data.additional4.vertices) : Data.additional4.IsEmbedding π i := by
  fin_cases i
  · exact embedding_26 π ρ h

theorem ordinary_local (i : Fin Data.additional4.vertices) :
    IsLocalRing (Data.additional4.OrdinaryEnd π ρ h i) := by
  apply Data.additional4.ordinary_local_of_diagonal_residues π ρ h i 0
  · fin_cases i; rfl
  · fin_cases i; decide
  · fin_cases i; decide
  · intro f
    fin_cases i
    · constructor
      · intro a ha
        fin_cases a
        · rfl
        · exact residue_ambient_26_1 π ρ h f
      · intro a
        fin_cases a
        · exact residue_source_26_0 π ρ h f
        · exact residue_source_26_1 π ρ h f

end UniserialComputations.Uniform.Case4
