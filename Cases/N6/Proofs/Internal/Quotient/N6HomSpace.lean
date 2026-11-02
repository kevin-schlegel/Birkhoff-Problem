import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
variable (k : Type*) [CommRing k]
abbrev Block := Matrix (Fin 2) (Fin 2) k
def basisBlock (t : Fin 14) (b : Fin 3) : Block k := fun r c => (basisInt t b r c : k)
def param (t : Fin 14) (x : Fin 3 → k) : Block k := ∑ b, x b • basisBlock k t b
def coords (t : Fin 14) (A : Block k) : Fin 3 → k := fun b => A (pivotRow t b) (pivotCol t b)
def project (t : Fin 14) (A : Block k) : Block k := param k t (coords k t A)
def Normal (t : Fin 14) (A : Block k) : Prop := project k t A=A
instance (t : Fin 14) (A : Block ℤ) : Decidable (Normal ℤ t A) := inferInstanceAs (Decidable (_ = _))
theorem basis_inactive (t : Fin 14) (b : Fin 3) (hb : kindDim t≤b.val) : basisBlock k t b=0 := by
  fin_cases t <;> fin_cases b
  all_goals norm_num [kindDim] at hb
  all_goals ext r c; fin_cases r <;> fin_cases c <;> simp [basisBlock,basisInt]
theorem coords_param (t : Fin 14) (x : Fin 3 → k) (b : Fin 3) (hb : b.val<kindDim t) :
    coords k t (param k t x) b=x b := by
  fin_cases t <;> fin_cases b
  all_goals norm_num [kindDim] at hb
  all_goals simp [coords,param,basisBlock,basisInt,pivotRow,pivotCol,Fin.sum_univ_succ]
theorem param_add (t : Fin 14) (x y : Fin 3 → k) : param k t (x+y)=param k t x+param k t y := by
  simp [param,add_smul,Finset.sum_add_distrib]
theorem param_smul (t : Fin 14) (a : k) (x : Fin 3 → k) : param k t (a • x)=a • param k t x := by
  simp [param,Finset.smul_sum,mul_smul]
theorem param_normal (t : Fin 14) (x : Fin 3 → k) : Normal k t (param k t x) := by
  unfold Normal project param
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : b.val<kindDim t
  · change coords k t (param k t x) b • basisBlock k t b = x b • basisBlock k t b
    rw [coords_param k t x b hb]
  · rw [basis_inactive k t b (by omega),smul_zero,smul_zero]
theorem normal_zero (t : Fin 14) : Normal k t 0 := by simp [Normal,project,param,coords]
theorem normal_add {t : Fin 14} {A B : Block k} (ha : Normal k t A) (hb : Normal k t B) : Normal k t (A+B) := by
  change param k t (coords k t A+coords k t B)=A+B
  change param k t (coords k t A)=A at ha
  change param k t (coords k t B)=B at hb
  rw [param_add,ha,hb]
theorem normal_smul {t : Fin 14} (a : k) {A : Block k} (ha : Normal k t A) : Normal k t (a • A) := by
  change param k t (a • coords k t A)=a • A
  change param k t (coords k t A)=A at ha
  rw [param_smul,ha]
theorem normal_sum {ι : Type*} [Fintype ι] {t : Fin 14} (A : ι → Block k) (h : ∀ i,Normal k t (A i)) : Normal k t (∑ i,A i) := by
  classical
  have hs : ∀ s : Finset ι, Normal k t (∑ i ∈ s,A i) := by
    intro s; induction s using Finset.induction_on with
    | empty => simpa using normal_zero k t
    | @insert a s ha ih => simpa [Finset.sum_insert ha] using normal_add k (h a) ih
  simpa using hs Finset.univ
end UniserialComputations.N6
