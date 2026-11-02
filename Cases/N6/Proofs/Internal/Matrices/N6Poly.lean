import N6Matrix
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
abbrev Poly6 := Fin 6 → ℤ
def mono6 (a : ℤ) (d : ℕ) : Poly6 := fun t => if t.val=d then a else 0
def mul6 (p q : Poly6) : Poly6 := fun d => ∑ a : Fin 6, ∑ b : Fin 6,
  if a.val+b.val=d.val then p a*q b else 0
def eval6 {R : Type*} [CommRing R] (π : R) (p : Poly6) : R :=
  ∑ d : Fin 6, (p d : R)*π^d.val
variable {R : Type*} [CommRing R] (π : R) (h6 : π^6=0)
theorem eval6_add (p q : Poly6) : eval6 π (p+q)=eval6 π p+eval6 π q := by
  simp [eval6,add_mul,Finset.sum_add_distrib]
theorem eval6_neg (p : Poly6) : eval6 π (-p)= -eval6 π p := by simp [eval6]
theorem eval6_sub (p q : Poly6) : eval6 π (p-q)=eval6 π p-eval6 π q := by
  simp [eval6,sub_mul,Finset.sum_sub_distrib]
theorem eval6_zero : eval6 π 0=0 := by simp [eval6]
theorem eval6_sum {ι : Type*} [Fintype ι] (p : ι → Poly6) :
    eval6 π (∑ a, p a)=∑ a,eval6 π (p a) := by
  simp only [eval6,Finset.sum_apply,Int.cast_sum,Finset.sum_mul]
  exact Finset.sum_comm
include h6 in
theorem eval6_mono (a : ℤ) (d : ℕ) : eval6 π (mono6 a d)=(a:R)*π^d := by
  by_cases hd : d<6
  · interval_cases d <;> norm_num [eval6,mono6,Fin.sum_univ_succ]
  · have hz := high_power π h6 d (by omega)
    have ht : ∀ t : Fin 6, t.val≠d := by intro t; omega
    simp [eval6,mono6,ht,hz]
include h6 in
theorem eval6_mul (p q : Poly6) : eval6 π (mul6 p q)=eval6 π p*eval6 π q := by
  have hp7 := high_power π h6 7 (by decide)
  have hp8 := high_power π h6 8 (by decide)
  have hp9 := high_power π h6 9 (by decide)
  have hp10 := high_power π h6 10 (by decide)
  simp [eval6,mul6,Fin.sum_univ_succ]
  ring_nf
  simp [h6,hp7,hp8,hp9,hp10]
variable {k : Type*} [Field k] (ρ : R →+* k)
theorem residue_eval6 (hp : ρ π=0) (p : Poly6) : ρ (eval6 π p)=(p 0 : k) := by
  simp [eval6,Fin.sum_univ_succ,map_add,map_mul,map_pow,hp]
end UniserialComputations.N6
