import UniformOperations

noncomputable section
namespace UniserialComputations.Uniform
set_option linter.unusedSectionVars false
universe u v

/-- An enumeration of precisely the ambient summands of maximal length. -/
structure FreeCoordinates (D : ObjectFamily) (F : Type*) where
  vertex : F → Fin D.vertices
  row : F → Fin D.ambientSlots
  valid : ∀ a, D.ambientLength (vertex a) (row a) = D.length
  injective : Function.Injective (fun a => (vertex a, row a))
  complete : ∀ i r, D.ambientLength i r = D.length → ∃ a, vertex a = i ∧ row a = r

namespace FreeCoordinates
variable {D : ObjectFamily} {F : Type*} [Fintype F] [DecidableEq F]
  (C : FreeCoordinates D F)

def freeEquiv : F ≃ {p : Fin D.vertices × Fin D.ambientSlots //
    D.ambientLength p.1 p.2 = D.length} :=
  Equiv.ofBijective (fun a => ⟨(C.vertex a, C.row a), C.valid a⟩) ⟨
    fun _ _ h => C.injective (congrArg Subtype.val h), by
      rintro ⟨⟨i,r⟩,h⟩
      obtain ⟨a,ha,hb⟩ := C.complete i r h
      exact ⟨a, Subtype.ext (Prod.ext ha hb)⟩⟩

theorem sum_free {K : Type*} [AddCommMonoid K]
    (f : Fin D.vertices → Fin D.ambientSlots → K)
    (hz : ∀ i r, D.ambientLength i r ≠ D.length → f i r = 0) :
    (∑ a : F, f (C.vertex a) (C.row a)) = ∑ i, ∑ r, f i r := by
  have he := (C.freeEquiv).sum_comp (fun p => f p.val.1 p.val.2)
  change (∑ a : F, f (C.vertex a) (C.row a)) = _ at he
  rw [he]
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun p : Fin D.vertices × Fin D.ambientSlots => D.ambientLength p.1 p.2 = D.length)
    (fun p => f p.1 p.2)
  have hz' : (∑ p : {p : Fin D.vertices × Fin D.ambientSlots //
      ¬ D.ambientLength p.1 p.2 = D.length}, f p.val.1 p.val.2) = 0 :=
    Finset.sum_eq_zero (fun p _ => hz _ _ p.property)
  rw [hz', add_zero, Fintype.sum_prod_type] at hs
  exact hs

variable {R : Type u} {k : Type v} [CommRing R] [Field k]
  (π : R) (ρ : R →+* k) (h : RingParameters D.length R k π ρ)

def reduce (f : D.EndRepresentatives π) : Matrix F F k :=
  fun a b => ρ ((f (C.vertex a) (C.vertex b)).ambient (C.row a) (C.row b))

include h in
theorem off_free {i j} (f : D.Hom π i j) (r c)
    (hr : D.ambientLength i r = D.length)
    (hc : D.ambientLength j c ≠ D.length) : ρ (f.ambient r c) = 0 := by
  apply (h.top_annihilator _).mp
  have hd := f.ambient_descent r c
  simp only [hr, Nat.sub_self, pow_zero, one_mul] at hd
  have hb : D.ambientLength j c ≤ D.length-1 := by
    have := D.ambientBound j c
    omega
  have H := congrArg (fun x : R => π^(D.length-1-D.ambientLength j c)*x) hd
  simpa only [← mul_assoc, ← pow_add, Nat.sub_add_cancel hb, mul_zero] using H

include h in
theorem exact (f g : D.EndRepresentatives π) :
    C.reduce π ρ f = C.reduce π ρ g ↔ D.Equivalent π f g := by
  constructor
  · intro H i j r c
    by_cases hr : D.ambientLength i r = D.length
    · simp only [hr, Nat.sub_self, pow_zero, one_mul]
      rw [h.top_annihilator, map_sub, sub_eq_zero]
      by_cases hc : D.ambientLength j c = D.length
      · obtain ⟨a,rfl,rfl⟩ := C.complete i r hr
        obtain ⟨b,rfl,rfl⟩ := C.complete j c hc
        exact congrFun (congrFun H a) b
      · rw [off_free π ρ h (f i j) r c hr hc, off_free π ρ h (g i j) r c hr hc]
    · have hb : D.length ≤ (D.length-D.ambientLength i r)+(D.length-1) := by
        have := D.ambientBound i r
        have := h.positive
        omega
      obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hb
      rw [← pow_add, hd, pow_add, h.nilpotent, zero_mul, zero_mul]
  · intro H
    ext a b
    have e := H (C.vertex a) (C.vertex b) (C.row a) (C.row b)
    simpa only [C.valid a, Nat.sub_self, pow_zero, one_mul, h.top_annihilator,
      map_sub, sub_eq_zero, reduce] using e

def zero : D.EndRepresentatives π := fun i j => ObjectFamily.Hom.zero D π i j
def add (f g : D.EndRepresentatives π) : D.EndRepresentatives π :=
  fun i j => ObjectFamily.Hom.add D π (f i j) (g i j)
def scale (x : R) (f : D.EndRepresentatives π) : D.EndRepresentatives π :=
  fun i j => ObjectFamily.Hom.scale D π x (f i j)
def mul (f g : D.EndRepresentatives π) : D.EndRepresentatives π :=
  fun i j => ObjectFamily.Hom.sum D π (fun l => ObjectFamily.Hom.comp D π h (f i l) (g l j))
def one : D.EndRepresentatives π := fun i j =>
  if e : i = j then e ▸ ObjectFamily.Hom.identity D π h i else ObjectFamily.Hom.zero D π i j

@[simp] theorem reduce_zero : C.reduce π ρ (zero π) = 0 := by ext; simp [reduce,zero,ObjectFamily.Hom.zero]
@[simp] theorem reduce_add (f g : D.EndRepresentatives π) :
    C.reduce π ρ (add π f g) = C.reduce π ρ f + C.reduce π ρ g := by
  ext; simp [reduce,add,ObjectFamily.Hom.add]
@[simp] theorem reduce_scale (x : R) (f : D.EndRepresentatives π) :
    C.reduce π ρ (scale π x f) = ρ x • C.reduce π ρ f := by
  ext; simp [reduce,scale,ObjectFamily.Hom.scale]

theorem reduce_mul (f g : D.EndRepresentatives π) :
    C.reduce π ρ (mul π ρ h f g) = C.reduce π ρ f * C.reduce π ρ g := by
  ext a b
  simp only [reduce, mul, ObjectFamily.Hom.sum, ObjectFamily.Hom.comp,
    Matrix.sum_apply, map_sum, Matrix.mul_apply, map_mul]
  symm
  exact C.sum_free (fun i r =>
    ρ ((f (C.vertex a) i).ambient (C.row a) r) *
    ρ ((g i (C.vertex b)).ambient r (C.row b))) (by
      intro i r hr
      rw [off_free π ρ h (f (C.vertex a) i) (C.row a) r (C.valid a) hr, zero_mul])

theorem reduce_one : C.reduce π ρ (one π ρ h) = 1 := by
  ext a b
  by_cases hv : C.vertex a = C.vertex b
  · have aux : ∀ i j, i = j → (one π ρ h i j).ambient = 1 := by
      intro i j e
      subst j
      simp [one, ObjectFamily.Hom.identity]
    have hm := aux _ _ hv
    simp only [reduce, hm, Matrix.one_apply, apply_ite, map_one, map_zero]
    by_cases hab : a = b
    · subst b; simp
    · have hr : C.row a ≠ C.row b := fun hr => hab (C.injective (Prod.ext hv hr))
      simp [hab, hr]
  · have hab : a ≠ b := fun e => hv (congrArg C.vertex e)
    simp [reduce, one, hv, hab, ObjectFamily.Hom.zero]

/-- The image of all commuting squares, reduced on their free ambient blocks. -/
def imageAlgebra : Subalgebra k (Matrix F F k) where
  carrier := {M | ∃ f : D.EndRepresentatives π, C.reduce π ρ f = M}
  zero_mem' := ⟨zero π, C.reduce_zero π ρ⟩
  one_mem' := ⟨one π ρ h, C.reduce_one π ρ h⟩
  add_mem' := by
    rintro _ _ ⟨f,rfl⟩ ⟨g,rfl⟩
    exact ⟨add π f g, C.reduce_add π ρ f g⟩
  mul_mem' := by
    rintro _ _ ⟨f,rfl⟩ ⟨g,rfl⟩
    exact ⟨mul π ρ h f g, C.reduce_mul π ρ h f g⟩
  algebraMap_mem' := by
    intro x
    obtain ⟨r,hr⟩ := h.residue_surjective x
    refine ⟨scale π r (one π ρ h), ?_⟩
    rw [C.reduce_scale, C.reduce_one, hr, Algebra.smul_def, mul_one]

def quotientEquiv : D.EndQuotient π ≃ C.imageAlgebra π ρ h where
  toFun := Quotient.lift (fun f => ⟨C.reduce π ρ f, f, rfl⟩)
    (fun f g H => Subtype.ext ((C.exact π ρ h f g).mpr H))
  invFun M := D.classOf π (Classical.choose M.property)
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h f =>
      apply Quotient.sound
      exact (C.exact π ρ h _ f).mp (Classical.choose_spec (show ∃ g, C.reduce π ρ g = C.reduce π ρ f from ⟨f,rfl⟩))
  right_inv := by
    intro M
    apply Subtype.ext
    exact Classical.choose_spec M.property

end FreeCoordinates

/-- The algebra on the actual annihilation quotient, identified with its
faithful free-coordinate image. -/
def EndAlgebra {D : ObjectFamily} {F : Type*} [Fintype F] [DecidableEq F]
    (C : FreeCoordinates D F) {R : Type u} {k : Type v} [CommRing R] [Field k]
    (π : R) (ρ : R →+* k) (h : RingParameters D.length R k π ρ) := D.EndQuotient π

namespace EndAlgebra
variable {D : ObjectFamily} {F : Type*} [Fintype F] [DecidableEq F]
  (C : FreeCoordinates D F) {R : Type u} {k : Type v} [CommRing R] [Field k]
  (π : R) (ρ : R →+* k) (h : RingParameters D.length R k π ρ)

def imageEquiv : EndAlgebra C π ρ h ≃ C.imageAlgebra π ρ h := C.quotientEquiv π ρ h
instance : Ring (EndAlgebra C π ρ h) := (imageEquiv C π ρ h).ring
instance : Algebra k (EndAlgebra C π ρ h) := (imageEquiv C π ρ h).algebra k
def imageAlgEquiv : EndAlgebra C π ρ h ≃ₐ[k] C.imageAlgebra π ρ h :=
  (imageEquiv C π ρ h).algEquiv k

def classOf (f : D.EndRepresentatives π) : EndAlgebra C π ρ h := D.classOf π f
theorem classOf_add (f g : D.EndRepresentatives π) :
    classOf C π ρ h (FreeCoordinates.add π f g) = classOf C π ρ h f + classOf C π ρ h g := by
  apply (imageAlgEquiv C π ρ h).injective
  rw [map_add]
  apply Subtype.ext
  exact C.reduce_add π ρ f g
theorem classOf_mul (f g : D.EndRepresentatives π) :
    classOf C π ρ h (FreeCoordinates.mul π ρ h f g) = classOf C π ρ h f * classOf C π ρ h g := by
  apply (imageAlgEquiv C π ρ h).injective
  rw [map_mul]
  apply Subtype.ext
  exact C.reduce_mul π ρ h f g
theorem classOf_scale (r : R) (f : D.EndRepresentatives π) :
    classOf C π ρ h (FreeCoordinates.scale π r f) = ρ r • classOf C π ρ h f := by
  apply (imageAlgEquiv C π ρ h).injective
  rw [map_smul]
  apply Subtype.ext
  exact C.reduce_scale π ρ r f
theorem classOf_pi_zero (f : D.EndRepresentatives π) :
    classOf C π ρ h (FreeCoordinates.scale π π f) = 0 := by
  rw [classOf_scale, h.residue_pi, zero_smul]

end EndAlgebra
end UniserialComputations.Uniform
