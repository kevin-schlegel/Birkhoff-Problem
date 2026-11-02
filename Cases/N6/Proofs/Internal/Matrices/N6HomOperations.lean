import N6Matrix
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
def homZero (i j : Fin 47) : HomData π i j where
  M := 0
  U := 0
  ambient_descent := by intros; simp
  source_descent := by intros; simp
  commutes := by intros; simp
def homAdd {i j : Fin 47} (f g : HomData π i j) : HomData π i j where
  M := f.M+g.M
  U := f.U+g.U
  ambient_descent := by intros; simp only [Matrix.add_apply,mul_add,f.ambient_descent,g.ambient_descent,add_zero]
  source_descent := by intros; simp only [Matrix.add_apply,mul_add,f.source_descent,g.source_descent,add_zero]
  commutes := by
    intro r c
    simp only [Matrix.add_mul,Matrix.mul_add,Matrix.add_apply]
    linear_combination f.commutes r c + g.commutes r c
def homScale {i j : Fin 47} (x : R) (f : HomData π i j) : HomData π i j where
  M := x • f.M
  U := x • f.U
  ambient_descent := by
    intro r c
    simp only [Matrix.smul_apply,smul_eq_mul]
    linear_combination x*f.ambient_descent r c
  source_descent := by
    intro r c
    simp only [Matrix.smul_apply,smul_eq_mul]
    linear_combination x*f.source_descent r c
  commutes := by
    intro r c
    simp only [Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_apply,smul_eq_mul]
    linear_combination x*f.commutes r c
theorem reduce_homAdd {i j : Fin 47} (f g : HomData π i j) :
    reduceHom π ρ (homAdd π f g)=reduceHom π ρ f+reduceHom π ρ g := reduce_add ρ i j f.M g.M
theorem reduce_homScale {i j : Fin 47} (x : R) (f : HomData π i j) :
    reduceHom π ρ (homScale π x f)=ρ x • reduceHom π ρ f := reduce_scale ρ i j x f.M
def homSum3 {i j : Fin 47} (f : Fin 3 → HomData π i j) : HomData π i j :=
  homAdd π (f 0) (homAdd π (f 1) (f 2))
theorem reduce_homSum3 {i j : Fin 47} (f : Fin 3 → HomData π i j) :
    reduceHom π ρ (homSum3 π f)=∑ b : Fin 3,reduceHom π ρ (f b) := by
  simp [homSum3,reduce_homAdd,Fin.sum_univ_succ]
end UniserialComputations.N6
