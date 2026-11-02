import UniformObjects

noncomputable section
namespace UniserialComputations.Uniform
universe u v
variable (D : ObjectFamily) {R : Type u} [CommRing R] (π : R)

namespace ObjectFamily.Hom
def zero (i j : Fin D.vertices) : D.Hom π i j where
  ambient := 0
  source := 0
  ambient_descent := by intros; simp
  source_descent := by intros; simp
  commutes := by intros; simp

def add {i j} (f g : D.Hom π i j) : D.Hom π i j where
  ambient := f.ambient + g.ambient
  source := f.source + g.source
  ambient_descent := by intros; simp [mul_add, f.ambient_descent, g.ambient_descent]
  source_descent := by intros; simp [mul_add, f.source_descent, g.source_descent]
  commutes := by
    intro r c
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.add_apply]
    linear_combination f.commutes r c + g.commutes r c

def scale {i j} (x : R) (f : D.Hom π i j) : D.Hom π i j where
  ambient := x • f.ambient
  source := x • f.source
  ambient_descent := by
    intro r c
    simp only [Matrix.smul_apply, smul_eq_mul]
    linear_combination x * f.ambient_descent r c
  source_descent := by
    intro r c
    simp only [Matrix.smul_apply, smul_eq_mul]
    linear_combination x * f.source_descent r c
  commutes := by
    intro r c
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
    linear_combination x * f.commutes r c

def sum {α : Type*} [Fintype α] {i j} (f : α → D.Hom π i j) : D.Hom π i j where
  ambient := ∑ a, (f a).ambient
  source := ∑ a, (f a).source
  ambient_descent := by
    intro r c
    simp only [Matrix.sum_apply, Finset.mul_sum]
    exact Finset.sum_eq_zero (fun a _ => (f a).ambient_descent r c)
  source_descent := by
    intro r c
    simp only [Matrix.sum_apply, Finset.mul_sum]
    exact Finset.sum_eq_zero (fun a _ => (f a).source_descent r c)
  commutes := by
    intro r c
    simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.sum_apply,
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_eq_zero (fun a _ => (f a).commutes r c)

variable {k : Type v} [Field k] {ρ : R →+* k}
  (h : RingParameters D.length R k π ρ)

def identity (i : Fin D.vertices) : D.Hom π i i where
  ambient := 1
  source := 1
  ambient_descent := by
    intro r c
    by_cases e : r = c
    · subst c
      simp only [Matrix.one_apply_eq, mul_one, ← pow_add,
        Nat.sub_add_cancel (D.ambientBound i r), h.nilpotent]
    · simp [Matrix.one_apply_ne e]
  source_descent := by
    intro r c
    by_cases e : r = c
    · subst c
      simp only [Matrix.one_apply_eq, mul_one, ← pow_add,
        Nat.sub_add_cancel (D.sourceBound i r), h.nilpotent]
    · simp [Matrix.one_apply_ne e]
  commutes := by intros; simp

include h in
lemma weighted_sum {α : Type*} [Fintype α] (l : α → Nat)
    (bounds : ∀ a, l a ≤ D.length) (p : R) (f g : α → R)
    (hf : ∀ a, p * π ^ l a * f a = 0)
    (hg : ∀ a, π ^ (D.length-l a) * g a = 0) :
    p * ∑ a, f a * g a = 0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro a _
  obtain ⟨t, ht⟩ := (h.annihilator (l a) (bounds a) (g a)).mp (hg a)
  rw [ht]
  linear_combination t * hf a

def comp {i j l} (f : D.Hom π i j) (g : D.Hom π j l) : D.Hom π i l where
  ambient := f.ambient * g.ambient
  source := f.source * g.source
  ambient_descent := by
    intro r c
    have H := weighted_sum D π h (D.ambientLength j) (D.ambientBound j)
      (π ^ (D.length-D.ambientLength i r)) (fun a => f.ambient r a)
      (fun a => π ^ D.ambientLength l c * g.ambient a c)
      (f.ambient_descent r) (fun a => by simpa [mul_assoc] using g.ambient_descent a c)
    convert H using 1
    simp only [Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  source_descent := by
    intro r c
    have H := weighted_sum D π h (D.sourceLength j) (D.sourceBound j)
      (π ^ (D.length-D.sourceLength i r)) (fun a => f.source r a)
      (fun a => π ^ D.sourceLength l c * g.source a c)
      (f.source_descent r) (fun a => by simpa [mul_assoc] using g.source_descent a c)
    convert H using 1
    simp only [Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  commutes := by
    intro r c
    have H : (f.ambient * g.ambient) * D.embedding π l -
        D.embedding π i * (f.source * g.source) =
        f.ambient * (g.ambient * D.embedding π l - D.embedding π j * g.source) +
        (f.ambient * D.embedding π j - D.embedding π i * f.source) * g.source := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      abel
    change π ^ (D.length-D.ambientLength i r) *
      (((f.ambient * g.ambient) * D.embedding π l -
        D.embedding π i * (f.source * g.source)) r c) = 0
    rw [H, Matrix.add_apply, mul_add]
    have H₁ := weighted_sum D π h (D.ambientLength j) (D.ambientBound j)
      (π ^ (D.length-D.ambientLength i r)) (fun a => f.ambient r a)
      (fun a => (g.ambient * D.embedding π l - D.embedding π j * g.source) a c)
      (f.ambient_descent r) (fun a => g.commutes a c)
    change _ + _ = 0
    rw [show π ^ (D.length-D.ambientLength i r) *
      (f.ambient * (g.ambient * D.embedding π l - D.embedding π j * g.source)) r c = 0 from H₁,
      zero_add]
    simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc]
    apply Finset.sum_eq_zero
    intro a _
    rw [show π ^ (D.length-D.ambientLength i r) *
      (f.ambient * D.embedding π j - D.embedding π i * f.source) r a = 0 from f.commutes r a,
      zero_mul]

end ObjectFamily.Hom
end UniserialComputations.Uniform
