import N6Poly
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
def fastMul6 (p q : Poly6) : Poly6 :=
  ![p 0*q 0,
    p 0*q 1+p 1*q 0,
    p 0*q 2+p 1*q 1+p 2*q 0,
    p 0*q 3+p 1*q 2+p 2*q 1+p 3*q 0,
    p 0*q 4+p 1*q 3+p 2*q 2+p 3*q 1+p 4*q 0,
    p 0*q 5+p 1*q 4+p 2*q 3+p 3*q 2+p 4*q 1+p 5*q 0]
theorem fastMul6_eq (p q : Poly6) : fastMul6 p q=mul6 p q := by
  funext d
  fin_cases d <;> simp [fastMul6,mul6,Fin.sum_univ_succ] <;> ring
theorem eval6_fastMul {R : Type*} [CommRing R] (π : R) (h6 : π^6=0) (p q : Poly6) :
    eval6 π (fastMul6 p q)=eval6 π p*eval6 π q := by rw [fastMul6_eq,eval6_mul π h6]
end UniserialComputations.N6
