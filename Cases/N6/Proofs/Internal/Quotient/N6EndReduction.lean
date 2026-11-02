import N6EndAlgebra
import N6Realization
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h6 : π^6=0) (ann : ∀ r,π^5*r=0 ↔ ρ r=0)
abbrev RawFamily := ∀ i j : Fin 47, HomData π i j
/-- Concrete reduction of all ambient blocks; the kernel is exactly the specified ideal. -/
def reduceFamily (f : RawFamily π) : End k :=
  ⟨assemble k (fun i j => reduceHom π ρ (f i j)),by
    intro i j
    rw [block_assemble k _ (fun i j => normal_padded k i j (image_normal π ρ h6 ann i j (f i j)))]
    exact image_normal π ρ h6 ann i j (f i j)⟩
theorem reduceFamily_block (f : RawFamily π) (i j : Fin 47) :
    block k (reduceFamily π ρ h6 ann f).val i j=reduceHom π ρ (f i j) :=
  block_assemble k _ (fun i j => normal_padded k i j (image_normal π ρ h6 ann i j (f i j))) i j
theorem reduceFamily_surjective (surj : Function.Surjective ρ) :
    Function.Surjective (reduceFamily π ρ h6 ann) := by
  intro A
  choose f hf using fun i j => realizes_normal π ρ h6 ann surj i j (block k A.val i j) (A.property i j)
  refine ⟨f,?_⟩
  apply Subtype.ext
  change assemble k (fun i j => reduceHom π ρ (f i j))=A.val
  have hh : (fun i j => reduceHom π ρ (f i j))=block k A.val := by funext i j; exact hf i j
  rw [hh,assemble_block]
theorem reduceFamily_exact (f g : RawFamily π) :
    reduceFamily π ρ h6 ann f=reduceFamily π ρ h6 ann g ↔ ∀ i j, Equivalent π (f i j) (g i j) := by
  constructor
  · intro h i j
    have hh := congrArg (fun A : End k => block k A.val i j) h
    rw [reduceFamily_block,reduceFamily_block] at hh
    exact (quotient_exact π ρ h6 ann (f i j) (g i j)).mpr hh
  · intro h
    apply Subtype.ext
    ext r c
    have hh := (quotient_exact π ρ h6 ann (f r.1 c.1) (g r.1 c.1)).mp (h r.1 c.1)
    exact congrFun (congrFun hh (part r.1 r.2)) (part c.1 c.2)
theorem reduceFamily_add (f g : RawFamily π) :
    reduceFamily π ρ h6 ann (fun i j => homAdd π (f i j) (g i j)) =
      reduceFamily π ρ h6 ann f+reduceFamily π ρ h6 ann g := by
  apply Subtype.ext
  ext r c
  exact congrFun (congrFun (reduce_homAdd π ρ (f r.1 c.1) (g r.1 c.1)) (part r.1 r.2)) (part c.1 c.2)
theorem reduceFamily_scale (x : R) (f : RawFamily π) :
    reduceFamily π ρ h6 ann (fun i j => homScale π x (f i j)) = ρ x • reduceFamily π ρ h6 ann f := by
  apply Subtype.ext
  ext r c
  exact congrFun (congrFun (reduce_homScale π ρ x (f r.1 c.1)) (part r.1 r.2)) (part c.1 c.2)
theorem reduceFamily_pi_zero (f : RawFamily π) :
    reduceFamily π ρ h6 ann (fun i j => homScale π π (f i j))=0 := by
  rw [reduceFamily_scale,residue_pi π ρ h6 ann,zero_smul]
theorem reduceMatrix_sum {ι : Type*} [Fintype ι] (i j : Fin 47) (M : ι → Matrix (Fin 4) (Fin 4) R) :
    reduceMatrix ρ i j (∑ a,M a)=∑ a,reduceMatrix ρ i j (M a) := by
  ext r c
  simp only [reduceMatrix,Matrix.sum_apply,map_sum]
  by_cases h : r.val<freeRank i ∧ c.val<freeRank j <;> simp [h]
/-- Multiplication agrees with composition of the original ambient matrices,
with the sum over intermediate summands written explicitly. -/
theorem reduction_product_blocks (f g : RawFamily π) (i j : Fin 47) :
    reduceMatrix ρ i j (∑ l : Fin 47,(f i l).M*(g l j).M) =
      block k ((reduceFamily π ρ h6 ann f).val*(reduceFamily π ρ h6 ann g).val) i j := by
  rw [reduceMatrix_sum,block_mul]
  apply Finset.sum_congr rfl
  intro l _
  rw [reduceFamily_block,reduceFamily_block]
  exact reduce_composition π ρ ann (f i l) (g l j)
end UniserialComputations.N6
