import N6PolyEmbedding
import N6PolyFast
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
structure PolyHom (i j : Fin 47) where
  M : Matrix (Fin 4) (Fin 4) Poly6
  U : Matrix (Fin 2) (Fin 2) Poly6
  ambient_descent : ∀ r c, fastMul6 (mono6 1 (6-ambientLength i r+ambientLength j c)) (M r c)=0
  source_descent : ∀ r c, fastMul6 (mono6 1 (6-sourceLength i r+sourceLength j c)) (U r c)=0
  commutes : ∀ r c, fastMul6 (mono6 1 (6-ambientLength i r))
    ((∑ t : Fin 4, fastMul6 (M r t) (polyEmbedding j t c)) -
     (∑ t : Fin 2, fastMul6 (polyEmbedding i r t) (U t c)))=0
def PolyHom.zero (i j : Fin 47) : PolyHom i j where
  M := 0
  U := 0
  ambient_descent := by intros; ext d; simp [fastMul6]; fin_cases d <;> simp
  source_descent := by intros; ext d; simp [fastMul6]; fin_cases d <;> simp
  commutes := by
    intro r c
    have hz (p : Poly6) : fastMul6 0 p=0 ∧ fastMul6 p 0=0 := by constructor <;> (ext d; fin_cases d <;> simp [fastMul6])
    simp only [Matrix.zero_apply,(hz _).1,(hz _).2,Finset.sum_const_zero,sub_self]
    all_goals exact (hz _).2
variable {R : Type*} [CommRing R] (π : R) (h6 : π^6=0)
def PolyHom.evaluate {i j : Fin 47} (f : PolyHom i j) : HomData π i j where
  M := fun r c => eval6 π (f.M r c)
  U := fun r c => eval6 π (f.U r c)
  ambient_descent := by
    intro r c
    have h := congrArg (eval6 π) (f.ambient_descent r c)
    simpa only [eval6_fastMul π h6,eval6_mono π h6,eval6_zero,Int.cast_one,one_mul,pow_add] using h
  source_descent := by
    intro r c
    have h := congrArg (eval6 π) (f.source_descent r c)
    simpa only [eval6_fastMul π h6,eval6_mono π h6,eval6_zero,Int.cast_one,one_mul,pow_add] using h
  commutes := by
    intro r c
    change π^(6-ambientLength i r)*((∑ t : Fin 4,eval6 π (f.M r t)*embedding π j t c) -
      (∑ t : Fin 2,embedding π i r t*eval6 π (f.U t c)))=0
    have h := congrArg (eval6 π) (f.commutes r c)
    simpa only [eval6_fastMul π h6,eval6_mono π h6,eval6_zero,eval6_sub,eval6_sum,
      eval_embedding π h6,Int.cast_one,one_mul,Matrix.mul_apply] using h
def PolyHom.freeBlock {i j : Fin 47} (f : PolyHom i j) : Matrix (Fin 2) (Fin 2) ℤ :=
  fun r c => if r.val<freeRank i ∧ c.val<freeRank j then f.M (freeSlot i r) (freeSlot j c) 0 else 0
theorem PolyHom.reduce_evaluate {k : Type*} [Field k] (ρ : R →+* k)
    (ann : ∀ r,π^5*r=0 ↔ ρ r=0) {i j : Fin 47} (f : PolyHom i j) :
    reduceHom π ρ (f.evaluate π h6)=fun r c => (f.freeBlock r c : k) := by
  ext r c
  simp only [reduceHom,reduceMatrix,PolyHom.evaluate,PolyHom.freeBlock]
  split_ifs
  · exact residue_eval6 π ρ (residue_pi π ρ h6 ann) _
  · simp
end UniserialComputations.N6
