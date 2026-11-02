import N5Reduction
noncomputable section
namespace UniserialComputations.N5.Raw
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
def rawAdd (f g : RawMatrix π) : RawMatrix π := fun i j => homAdd π (f i j) (g i j)
def rawScale (r : R) (f : RawMatrix π) : RawMatrix π := fun i j => homScale π r (f i j)
theorem reduce_add (f g : RawMatrix π) :
    reduction π ρ (rawAdd π f g)=reduction π ρ f+reduction π ρ g := by
  ext i j
  simp [reduction,rawAdd,homAdd]
theorem reduce_scale (r : R) (f : RawMatrix π) :
    reduction π ρ (rawScale π r f)=ρ r • reduction π ρ f := by
  ext i j
  simp [reduction,rawScale,homScale,smul_eq_mul]
theorem pi_action_zero (h5 : π^5=0) (ann : ∀ r, π^4*r=0 ↔ ρ r=0) (f : RawMatrix π) :
    reduction π ρ (rawScale π π f)=0 := by
  rw [reduce_scale,residue_pi π ρ h5 ann,zero_smul]
end UniserialComputations.N5.Raw
