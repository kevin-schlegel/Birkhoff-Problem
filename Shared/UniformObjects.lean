import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.TransferInstance
import Mathlib.Tactic

noncomputable section
namespace UniserialComputations.Uniform
universe u v

/-- A finite family of embeddings between sums of cyclic modules.
An entry `(c,e)` denotes `c * π^e`. Rows are ambient summands and columns
are source summands. A length-zero summand denotes the zero module. -/
structure ObjectFamily where
  length : Nat
  vertices : Nat
  ambientSlots : Nat
  sourceSlots : Nat
  labels : Fin vertices → String
  ambientLength : Fin vertices → Fin ambientSlots → Nat
  sourceLength : Fin vertices → Fin sourceSlots → Nat
  entry : Fin vertices → Fin ambientSlots → Fin sourceSlots → Int × Nat
  ambientBound : ∀ i r, ambientLength i r ≤ length
  sourceBound : ∀ i r, sourceLength i r ≤ length

namespace ObjectFamily
variable (D : ObjectFamily) {R : Type u} [CommRing R] (π : R)

def embedding (i : Fin D.vertices) :
    Matrix (Fin D.ambientSlots) (Fin D.sourceSlots) R :=
  fun r c => (D.entry i r c).1 * π ^ (D.entry i r c).2

/-- A commuting square from object `j` to object `i`.
The weighted equations express descent to cyclic summands and commutation
modulo the target cyclic summand. -/
structure Hom (i j : Fin D.vertices) where
  ambient : Matrix (Fin D.ambientSlots) (Fin D.ambientSlots) R
  source : Matrix (Fin D.sourceSlots) (Fin D.sourceSlots) R
  ambient_descent : ∀ r c,
    π ^ (D.length - D.ambientLength i r) * π ^ D.ambientLength j c * ambient r c = 0
  source_descent : ∀ r c,
    π ^ (D.length - D.sourceLength i r) * π ^ D.sourceLength j c * source r c = 0
  commutes : ∀ r c,
    π ^ (D.length - D.ambientLength i r) *
      ((ambient * D.embedding π j) r c - (D.embedding π i * source) r c) = 0

abbrev EndRepresentatives := ∀ i j, D.Hom π i j

/-- The quotient relation is π^(n-1)-annihilation of every ambient block. -/
def Equivalent (f g : D.EndRepresentatives π) : Prop :=
  ∀ i j r c, π ^ (D.length - D.ambientLength i r) * π ^ (D.length - 1) *
    ((f i j).ambient r c - (g i j).ambient r c) = 0

def quotientSetoid : Setoid (D.EndRepresentatives π) where
  r := D.Equivalent π
  iseqv := {
    refl := by intro f i j r c; simp
    symm := by
      intro f g h i j r c
      dsimp [Equivalent] at h
      linear_combination -h i j r c
    trans := by
      intro f g h hfg hgh i j r c
      dsimp [Equivalent] at hfg hgh
      linear_combination hfg i j r c + hgh i j r c }

abbrev EndQuotient := Quotient (D.quotientSetoid π)

def classOf (f : D.EndRepresentatives π) : D.EndQuotient π := Quotient.mk _ f

theorem classOf_eq (f g : D.EndRepresentatives π) :
    D.classOf π f = D.classOf π g ↔ D.Equivalent π f g := Quotient.eq

end ObjectFamily

/-- Elementary hypotheses for a length-n principal chain ring and its residue map.
The annihilator formula identifies cyclic congruences with the weighted equations
in `ObjectFamily.Hom`. -/
structure RingParameters (n : Nat) (R : Type u) (k : Type v)
    [CommRing R] [Field k] (π : R) (ρ : R →+* k) : Prop where
  positive : 0 < n
  nilpotent : π ^ n = 0
  residue_surjective : Function.Surjective ρ
  residue_kernel : ∀ r, ρ r = 0 ↔ ∃ t, r = π * t
  annihilator : ∀ l, l ≤ n → ∀ r,
    π ^ (n-l) * r = 0 ↔ ∃ t, r = π ^ l * t

namespace RingParameters
variable {n : Nat} {R : Type u} {k : Type v} [CommRing R] [Field k]
  {π : R} {ρ : R →+* k} (h : RingParameters n R k π ρ)

include h in
theorem top_annihilator (r : R) : π ^ (n-1) * r = 0 ↔ ρ r = 0 := by
  rw [h.annihilator 1 h.positive, h.residue_kernel]
  simp only [pow_one]

include h in
theorem residue_pi : ρ π = 0 :=
  (h.residue_kernel π).mpr ⟨1, by simp⟩

end RingParameters
end UniserialComputations.Uniform
