import N6BasisLifts0
import N6BasisLifts1
import N6BasisLifts2
import N6BasisLifts3
import N6BasisLifts4
import N6BasisLifts5
import N6BasisLifts6
import N6BasisLifts7
import N6BasisLifts8
import N6BasisLifts9
import N6BasisLifts10
import N6BasisLifts11
import N6BasisLifts12
import N6BasisLifts13
import N6BasisLifts14
import N6BasisLifts15
import N6BasisLifts16
import N6BasisLifts17
import N6BasisLifts18
import N6BasisLifts19
import N6BasisLifts20
import N6BasisLifts21
import N6BasisLifts22
import N6BasisLifts23
import N6BasisLifts24
import N6BasisLifts25
import N6BasisLifts26
import N6BasisLifts27
import N6BasisLifts28
import N6BasisLifts29
import N6BasisLifts30
import N6BasisLifts31
import N6BasisLifts32
import N6BasisLifts33
import N6BasisLifts34
import N6BasisLifts35
import N6BasisLifts36
import N6BasisLifts37
import N6BasisLifts38
import N6BasisLifts39
import N6BasisLifts40
import N6BasisLifts41
import N6BasisLifts42
import N6BasisLifts43
import N6BasisLifts44
import N6BasisLifts45
import N6BasisLifts46
import N6HomSpace
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
def polyBasisLift (i j : Fin 47) (b : Fin 3) : PolyHom i j :=
  match i with
  | ⟨0,_⟩ => polyLiftRow0 j b
  | ⟨1,_⟩ => polyLiftRow1 j b
  | ⟨2,_⟩ => polyLiftRow2 j b
  | ⟨3,_⟩ => polyLiftRow3 j b
  | ⟨4,_⟩ => polyLiftRow4 j b
  | ⟨5,_⟩ => polyLiftRow5 j b
  | ⟨6,_⟩ => polyLiftRow6 j b
  | ⟨7,_⟩ => polyLiftRow7 j b
  | ⟨8,_⟩ => polyLiftRow8 j b
  | ⟨9,_⟩ => polyLiftRow9 j b
  | ⟨10,_⟩ => polyLiftRow10 j b
  | ⟨11,_⟩ => polyLiftRow11 j b
  | ⟨12,_⟩ => polyLiftRow12 j b
  | ⟨13,_⟩ => polyLiftRow13 j b
  | ⟨14,_⟩ => polyLiftRow14 j b
  | ⟨15,_⟩ => polyLiftRow15 j b
  | ⟨16,_⟩ => polyLiftRow16 j b
  | ⟨17,_⟩ => polyLiftRow17 j b
  | ⟨18,_⟩ => polyLiftRow18 j b
  | ⟨19,_⟩ => polyLiftRow19 j b
  | ⟨20,_⟩ => polyLiftRow20 j b
  | ⟨21,_⟩ => polyLiftRow21 j b
  | ⟨22,_⟩ => polyLiftRow22 j b
  | ⟨23,_⟩ => polyLiftRow23 j b
  | ⟨24,_⟩ => polyLiftRow24 j b
  | ⟨25,_⟩ => polyLiftRow25 j b
  | ⟨26,_⟩ => polyLiftRow26 j b
  | ⟨27,_⟩ => polyLiftRow27 j b
  | ⟨28,_⟩ => polyLiftRow28 j b
  | ⟨29,_⟩ => polyLiftRow29 j b
  | ⟨30,_⟩ => polyLiftRow30 j b
  | ⟨31,_⟩ => polyLiftRow31 j b
  | ⟨32,_⟩ => polyLiftRow32 j b
  | ⟨33,_⟩ => polyLiftRow33 j b
  | ⟨34,_⟩ => polyLiftRow34 j b
  | ⟨35,_⟩ => polyLiftRow35 j b
  | ⟨36,_⟩ => polyLiftRow36 j b
  | ⟨37,_⟩ => polyLiftRow37 j b
  | ⟨38,_⟩ => polyLiftRow38 j b
  | ⟨39,_⟩ => polyLiftRow39 j b
  | ⟨40,_⟩ => polyLiftRow40 j b
  | ⟨41,_⟩ => polyLiftRow41 j b
  | ⟨42,_⟩ => polyLiftRow42 j b
  | ⟨43,_⟩ => polyLiftRow43 j b
  | ⟨44,_⟩ => polyLiftRow44 j b
  | ⟨45,_⟩ => polyLiftRow45 j b
  | ⟨46,_⟩ => polyLiftRow46 j b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyBasisLift_free (i j : Fin 47) (b : Fin 3) : (polyBasisLift i j b).freeBlock=basisInt (homKind i j) b := by
  fin_cases i
  · exact polyLiftRowFree0 j b
  · exact polyLiftRowFree1 j b
  · exact polyLiftRowFree2 j b
  · exact polyLiftRowFree3 j b
  · exact polyLiftRowFree4 j b
  · exact polyLiftRowFree5 j b
  · exact polyLiftRowFree6 j b
  · exact polyLiftRowFree7 j b
  · exact polyLiftRowFree8 j b
  · exact polyLiftRowFree9 j b
  · exact polyLiftRowFree10 j b
  · exact polyLiftRowFree11 j b
  · exact polyLiftRowFree12 j b
  · exact polyLiftRowFree13 j b
  · exact polyLiftRowFree14 j b
  · exact polyLiftRowFree15 j b
  · exact polyLiftRowFree16 j b
  · exact polyLiftRowFree17 j b
  · exact polyLiftRowFree18 j b
  · exact polyLiftRowFree19 j b
  · exact polyLiftRowFree20 j b
  · exact polyLiftRowFree21 j b
  · exact polyLiftRowFree22 j b
  · exact polyLiftRowFree23 j b
  · exact polyLiftRowFree24 j b
  · exact polyLiftRowFree25 j b
  · exact polyLiftRowFree26 j b
  · exact polyLiftRowFree27 j b
  · exact polyLiftRowFree28 j b
  · exact polyLiftRowFree29 j b
  · exact polyLiftRowFree30 j b
  · exact polyLiftRowFree31 j b
  · exact polyLiftRowFree32 j b
  · exact polyLiftRowFree33 j b
  · exact polyLiftRowFree34 j b
  · exact polyLiftRowFree35 j b
  · exact polyLiftRowFree36 j b
  · exact polyLiftRowFree37 j b
  · exact polyLiftRowFree38 j b
  · exact polyLiftRowFree39 j b
  · exact polyLiftRowFree40 j b
  · exact polyLiftRowFree41 j b
  · exact polyLiftRowFree42 j b
  · exact polyLiftRowFree43 j b
  · exact polyLiftRowFree44 j b
  · exact polyLiftRowFree45 j b
  · exact polyLiftRowFree46 j b
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
def basisLift (h6 : π^6=0) (i j : Fin 47) (b : Fin 3) : HomData π i j :=
  (polyBasisLift i j b).evaluate π h6
theorem basisLift_reduces (h6 : π^6=0) (ann : ∀ r,π^5*r=0 ↔ ρ r=0) (i j : Fin 47) (b : Fin 3) :
    reduceHom π ρ (basisLift π h6 i j b)=basisBlock k (homKind i j) b := by
  unfold basisLift
  rw [PolyHom.reduce_evaluate π h6 ρ ann,polyBasisLift_free]
  rfl
end UniserialComputations.N6
