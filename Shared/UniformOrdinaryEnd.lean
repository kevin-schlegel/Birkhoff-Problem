import UniformOperations
import Mathlib.RingTheory.Congruence.Basic

/-!
# Ordinary endomorphisms of a cyclic-module embedding

An endomorphism is a pair of matrices satisfying descent and the commuting
square. Representatives are identified exactly when both induced cyclic-module
maps are equal. No ideal of morphisms factoring through smaller objects is used.
-/

noncomputable section
namespace UniserialComputations.Uniform
universe u v

namespace CyclicMatrix
variable {R : Type u} [CommRing R] {m : Nat}

def Equal (n : Nat) (π : R) (lengths : Fin m → Nat)
    (A B : Matrix (Fin m) (Fin m) R) : Prop :=
  ∀ r c, π ^ (n - lengths r) * (A r c - B r c) = 0

theorem refl (n : Nat) (π : R) (l : Fin m → Nat) (A : Matrix (Fin m) (Fin m) R) :
    Equal n π l A A := by intro r c; simp

theorem symm {n : Nat} {π : R} {l : Fin m → Nat} {A B : Matrix (Fin m) (Fin m) R}
    (h : Equal n π l A B) : Equal n π l B A := by
  intro r c
  linear_combination -h r c

theorem trans {n : Nat} {π : R} {l : Fin m → Nat}
    {A B C : Matrix (Fin m) (Fin m) R}
    (h : Equal n π l A B) (g : Equal n π l B C) : Equal n π l A C := by
  intro r c
  linear_combination h r c + g r c

theorem add {n : Nat} {π : R} {l : Fin m → Nat}
    {A B C E : Matrix (Fin m) (Fin m) R}
    (h : Equal n π l A B) (g : Equal n π l C E) : Equal n π l (A + C) (B + E) := by
  intro r c
  simp only [Matrix.add_apply]
  linear_combination h r c + g r c

theorem mul (D : ObjectFamily) (π : R) {k : Type v} [Field k] {ρ : R →+* k}
    (h : RingParameters D.length R k π ρ) (l : Fin m → Nat)
    (bounds : ∀ r, l r ≤ D.length) {A B C E : Matrix (Fin m) (Fin m) R}
    (descent : ∀ r c, π ^ (D.length - l r) * π ^ l c * A r c = 0)
    (hAB : Equal D.length π l A B) (hCE : Equal D.length π l C E) :
    Equal D.length π l (A * C) (B * E) := by
  intro r c
  have split : A * C - B * E = A * (C - E) + (A - B) * E := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  change π ^ (D.length - l r) * ((A * C - B * E) r c) = 0
  rw [split, Matrix.add_apply, mul_add]
  have H := ObjectFamily.Hom.weighted_sum D π h l bounds
    (π ^ (D.length - l r)) (fun a => A r a) (fun a => (C - E) a c)
    (descent r) (fun a => hCE a c)
  change _ + _ = 0
  rw [show π ^ (D.length - l r) * (A * (C - E)) r c = 0 from H, zero_add]
  simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, Matrix.sub_apply]
  exact Finset.sum_eq_zero (fun a _ => by rw [hAB r a, zero_mul])
end CyclicMatrix

namespace ObjectFamily
variable (D : ObjectFamily) {R : Type u} {k : Type v} [CommRing R] [Field k]
  (π : R) (ρ : R →+* k) (h : RingParameters D.length R k π ρ) (i : Fin D.vertices)

/-- The given matrix descends to the cyclic modules and is injective there.
The kernel condition is expressed on arbitrary representatives of source vectors. -/
def IsEmbedding : Prop :=
  (∀ r c, π ^ (D.length - D.ambientLength i r) * π ^ D.sourceLength i c *
    D.embedding π i r c = 0) ∧
  (∀ x : Fin D.sourceSlots → R,
    (∀ r, π ^ (D.length - D.ambientLength i r) * (Matrix.mulVec (D.embedding π i) x) r = 0) →
    ∀ c, π ^ (D.length - D.sourceLength i c) * x c = 0)

/-- The algebra of representative commuting squares for one listed object. -/
def squareAlgebra : Subalgebra R
    (Matrix (Fin D.ambientSlots) (Fin D.ambientSlots) R ×
      Matrix (Fin D.sourceSlots) (Fin D.sourceSlots) R) where
  carrier := {p | ∃ f : D.Hom π i i, (f.ambient, f.source) = p}
  zero_mem' := ⟨Hom.zero D π i i, rfl⟩
  one_mem' := ⟨Hom.identity D π h i, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨Hom.add D π f g, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨Hom.comp D π h f g, rfl⟩
  algebraMap_mem' r := by
    refine ⟨Hom.scale D π r (Hom.identity D π h i), ?_⟩
    simp only [Hom.scale, Hom.identity, Algebra.algebraMap_eq_smul_one]
    rfl

abbrev Square := D.squareAlgebra π ρ h i

def squareOf (f : D.Hom π i i) : D.Square π ρ h i :=
  ⟨(f.ambient, f.source), f, rfl⟩

theorem squareOf_surjective : Function.Surjective (D.squareOf π ρ h i) := by
  rintro ⟨p, f, hf⟩
  exact ⟨f, Subtype.ext hf⟩

theorem square_ambient_descent (f : D.Square π ρ h i) :
    ∀ r c, π ^ (D.length - D.ambientLength i r) *
      π ^ D.ambientLength i c * f.val.1 r c = 0 := by
  obtain ⟨g, rfl⟩ := D.squareOf_surjective π ρ h i f
  exact g.ambient_descent

theorem square_source_descent (f : D.Square π ρ h i) :
    ∀ r c, π ^ (D.length - D.sourceLength i r) *
      π ^ D.sourceLength i c * f.val.2 r c = 0 := by
  obtain ⟨g, rfl⟩ := D.squareOf_surjective π ρ h i f
  exact g.source_descent

/-- Equality of the ambient and source maps on their cyclic summands. -/
def ordinaryCongruence : RingCon (D.Square π ρ h i) where
  r f g := CyclicMatrix.Equal D.length π (D.ambientLength i) f.val.1 g.val.1 ∧
    CyclicMatrix.Equal D.length π (D.sourceLength i) f.val.2 g.val.2
  iseqv := {
    refl := fun f => ⟨CyclicMatrix.refl D.length π (D.ambientLength i) f.val.1,
      CyclicMatrix.refl D.length π (D.sourceLength i) f.val.2⟩
    symm := fun e => ⟨CyclicMatrix.symm e.1, CyclicMatrix.symm e.2⟩
    trans := fun e f => ⟨CyclicMatrix.trans e.1 f.1, CyclicMatrix.trans e.2 f.2⟩ }
  add' e f := ⟨CyclicMatrix.add e.1 f.1, CyclicMatrix.add e.2 f.2⟩
  mul' {a _b _c _d} e f := ⟨
    CyclicMatrix.mul D π h _ (D.ambientBound i) (D.square_ambient_descent π ρ h i a) e.1 f.1,
    CyclicMatrix.mul D π h _ (D.sourceBound i) (D.square_source_descent π ρ h i a) e.2 f.2⟩

/-- The ordinary endomorphism ring of the represented cyclic-module arrow.
Only equality of actual module maps is imposed. For an embedding this is
`End` in the monomorphism category itself. -/
def OrdinaryEnd := (D.ordinaryCongruence π ρ h i).Quotient

instance ordinaryEndRing : Ring (D.OrdinaryEnd π ρ h i) :=
  inferInstanceAs (Ring (D.ordinaryCongruence π ρ h i).Quotient)

instance ordinaryEndAlgebra : Algebra R (D.OrdinaryEnd π ρ h i) :=
  inferInstanceAs (Algebra R (D.ordinaryCongruence π ρ h i).Quotient)

def ordinaryClass (f : D.Hom π i i) : D.OrdinaryEnd π ρ h i :=
  (D.ordinaryCongruence π ρ h i).mkₐ R (D.squareOf π ρ h i f)

theorem ordinaryClass_surjective : Function.Surjective (D.ordinaryClass π ρ h i) :=
  (RingCon.mkₐ_surjective _).comp (D.squareOf_surjective π ρ h i)

/-- The exact equality criterion for ordinary endomorphisms. In particular,
there is no additional factor `π^(n-1)` in either congruence. -/
theorem ordinaryClass_eq (f g : D.Hom π i i) :
    D.ordinaryClass π ρ h i f = D.ordinaryClass π ρ h i g ↔
      CyclicMatrix.Equal D.length π (D.ambientLength i) f.ambient g.ambient ∧
      CyclicMatrix.Equal D.length π (D.sourceLength i) f.source g.source := (D.ordinaryCongruence π ρ h i).eq

@[simp] theorem ordinaryClass_zero :
    D.ordinaryClass π ρ h i (Hom.zero D π i i) = 0 := rfl

@[simp] theorem ordinaryClass_one :
    D.ordinaryClass π ρ h i (Hom.identity D π h i) = 1 := rfl

@[simp] theorem ordinaryClass_add (f g : D.Hom π i i) :
    D.ordinaryClass π ρ h i (Hom.add D π f g) =
      D.ordinaryClass π ρ h i f + D.ordinaryClass π ρ h i g := rfl

@[simp] theorem ordinaryClass_mul (f g : D.Hom π i i) :
    D.ordinaryClass π ρ h i (Hom.comp D π h f g) =
      D.ordinaryClass π ρ h i f * D.ordinaryClass π ρ h i g := rfl

/-- Equality of ordinary endomorphisms is precisely congruence of each entry
modulo the annihilator of its target cyclic summand. -/
theorem ordinaryClass_eq_iff_cyclic_congruence (f g : D.Hom π i i) :
    D.ordinaryClass π ρ h i f = D.ordinaryClass π ρ h i g ↔
      (∀ r c, ∃ t, f.ambient r c - g.ambient r c = π ^ D.ambientLength i r * t) ∧
      (∀ r c, ∃ t, f.source r c - g.source r c = π ^ D.sourceLength i r * t) := by
  rw [D.ordinaryClass_eq π ρ h i]
  simp only [CyclicMatrix.Equal, h.annihilator _ (D.ambientBound i _),
    h.annihilator _ (D.sourceBound i _)]

end ObjectFamily
end UniserialComputations.Uniform
