import N6HomSpace
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
variable (k : Type*) [Field k]
def homSpace (t : Fin 14) : Submodule k (Block k) where
  carrier := {A | Normal k t A}
  zero_mem' := normal_zero k t
  add_mem' := normal_add k
  smul_mem' := normal_smul k
def extendCoords (t : Fin 14) (x : Fin (kindDim t) → k) : Fin 3 → k :=
  fun b => if h : b.val<kindDim t then x ⟨b.val,h⟩ else 0
def homParam (t : Fin 14) : (Fin (kindDim t) → k) →ₗ[k] homSpace k t where
  toFun x := ⟨param k t (extendCoords k t x),param_normal k t _⟩
  map_add' x y := by
    apply Subtype.ext
    change param k t (extendCoords k t (x+y))=param k t (extendCoords k t x)+param k t (extendCoords k t y)
    rw [← param_add]
    congr 1
    funext b
    simp only [Pi.add_apply,Pi.smul_apply,extendCoords]
    split_ifs <;> simp
  map_smul' a x := by
    apply Subtype.ext
    change param k t (extendCoords k t (a • x))=a • param k t (extendCoords k t x)
    rw [← param_smul]
    congr 1
    funext b
    simp only [Pi.add_apply,Pi.smul_apply,extendCoords]
    split_ifs <;> simp
lemma homParam_injective (t : Fin 14) : Function.Injective (homParam k t) := by
  intro x y h
  have hv := congrArg Subtype.val h
  funext b
  let q : Fin 3 := ⟨b.val,lt_of_lt_of_le b.isLt (kind_dim_le t)⟩
  have hh := congrArg (fun A : Block k => coords k t A q) hv
  change coords k t (param k t (extendCoords k t x)) q = coords k t (param k t (extendCoords k t y)) q at hh
  rw [coords_param k t _ q b.isLt,coords_param k t _ q b.isLt] at hh
  simpa [extendCoords,q,b.isLt] using hh
lemma homParam_surjective (t : Fin 14) : Function.Surjective (homParam k t) := by
  intro A
  let x : Fin (kindDim t) → k := fun b => coords k t A.val ⟨b.val,lt_of_lt_of_le b.isLt (kind_dim_le t)⟩
  refine ⟨x,?_⟩
  apply Subtype.ext
  change param k t (extendCoords k t x)=A.val
  rw [← A.property]
  change (∑ b : Fin 3, extendCoords k t x b • basisBlock k t b)=∑ b : Fin 3,coords k t A.val b • basisBlock k t b
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : b.val<kindDim t
  · simp [extendCoords,hb,x]
  · simp [extendCoords,hb,basis_inactive k t b (by omega)]
def homEquiv (t : Fin 14) : (Fin (kindDim t) → k) ≃ₗ[k] homSpace k t :=
  LinearEquiv.ofBijective (homParam k t) ⟨homParam_injective k t,homParam_surjective k t⟩
instance homSpaceFinite (t : Fin 14) : FiniteDimensional k (homSpace k t) :=
  (homEquiv k t).finiteDimensional
 theorem homSpace_finrank (t : Fin 14) : Module.finrank k (homSpace k t)=kindDim t := by
  rw [← (homEquiv k t).finrank_eq]
  simp
abbrev EndBlocks := ∀ i j : Fin 47, homSpace k (homKind i j)
theorem endBlocks_finrank : Module.finrank k (EndBlocks k)=1708 := by
  simp only [EndBlocks,Module.finrank_pi_fintype,homSpace_finrank]
  exact dimension_count
end UniserialComputations.N6
