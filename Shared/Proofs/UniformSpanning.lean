import UniformPaths
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section
namespace UniserialComputations.Uniform.QuiverData
variable {v : Nat} (Q : QuiverData v) (k : Type*) [Field k]

lemma walkEnd_append (s : Fin v) (p t : List (Fin Q.arrows)) :
    Q.walkEnd s (p++t) = (Q.walkEnd s p).bind (fun u => Q.walkEnd u t) := by
  induction p generalizing s with
  | nil => rfl
  | cons b p ih => simp only [List.cons_append,walkEnd]; split_ifs <;> simp [ih]

lemma vertex_walk (i s t : Fin v) (p : List (Fin Q.arrows)) (h : Q.walkEnd s p=some t) :
    Q.e k i * Q.walk k s p = if i=t then Q.walk k s p else 0 := by
  induction p using List.reverseRecOn generalizing t with
  | nil =>
    have ht : s=t := Option.some.inj h
    subst t
    by_cases hi : i=s
    · subst i; simpa [walk,word] using Q.vv k s s
    · simpa [walk,word,hi] using Q.vv k i s
  | append_singleton p b ih =>
    rw [walkEnd_append] at h
    cases hp : Q.walkEnd s p with
    | none => simp [hp] at h
    | some u =>
      simp only [hp,Option.bind_some,walkEnd] at h
      split_ifs at h with hb
      · have ht : Q.target b=t := Option.some.inj h
        subst t
        rw [walk_snoc,← mul_assoc,va]
        split_ifs <;> simp

lemma arrow_incompatible (b : Fin Q.arrows) (s t : Fin v) (p : List (Fin Q.arrows))
    (hp : Q.walkEnd s p=some t) (h : Q.source b≠t) : Q.a k b * Q.walk k s p=0 := by
  have hv := Q.vertex_walk k t s t p hp
  rw [if_pos rfl] at hv
  rw [← hv,← mul_assoc,av,if_neg (Ne.symm h),zero_mul]

def normalSpan {d : Nat} (normal : Fin d → Q.Presented k) : Submodule k (Q.Presented k) :=
  Submodule.span k (Set.range normal)

variable {Q k} {d : Nat} (normal : Fin d → Q.Presented k)

lemma normal_mem (c : Fin d) : normal c ∈ normalSpan Q k normal :=
  Submodule.subset_span ⟨c,rfl⟩

lemma left_stable (z : Q.Presented k)
    (h : ∀ c, z * normal c ∈ normalSpan Q k normal) :
    ∀ m ∈ normalSpan Q k normal, z*m ∈ normalSpan Q k normal := by
  intro m hm
  induction hm using Submodule.span_induction with
  | mem x hx => obtain ⟨c,rfl⟩ := hx; exact h c
  | zero => simpa using (normalSpan Q k normal).zero_mem
  | add x y hx hy ihx ihy => simpa [mul_add] using (normalSpan Q k normal).add_mem ihx ihy
  | smul r x hx ih => simpa [mul_smul_comm] using (normalSpan Q k normal).smul_mem r ih

theorem span_top
    (one_mem : (1 : Q.Presented k) ∈ normalSpan Q k normal)
    (vertex_span : ∀ i c, Q.e k i * normal c ∈ normalSpan Q k normal)
    (arrow_span : ∀ b c, Q.a k b * normal c ∈ normalSpan Q k normal) :
    normalSpan Q k normal = ⊤ := by
  let fromFree : Q.Free k →ₐ[k] Q.Presented k :=
    (Q.q k).comp (RingQuot.mkAlgHom k (Q.PathRelations k))
  have fromFree_surjective : Function.Surjective fromFree :=
    (RingQuot.mkAlgHom_surjective k (Q.Relations k)).comp
      (RingQuot.mkAlgHom_surjective k (Q.PathRelations k))
  have stable : ∀ w : Q.Free k, ∀ m ∈ normalSpan Q k normal,
      fromFree w*m ∈ normalSpan Q k normal := by
    intro w
    induction w using FreeAlgebra.induction with
    | grade0 r =>
      intro m hm
      simpa [Algebra.smul_def] using (normalSpan Q k normal).smul_mem r hm
    | grade1 g =>
      cases g with
      | inl i => exact left_stable normal (Q.e k i) (vertex_span i)
      | inr b => exact left_stable normal (Q.a k b) (arrow_span b)
    | add x y hx hy =>
      intro m hm
      simpa [map_add,add_mul] using (normalSpan Q k normal).add_mem (hx m hm) (hy m hm)
    | mul x y hx hy =>
      intro m hm
      simpa [map_mul,mul_assoc] using hx _ (hy m hm)
  apply top_unique
  intro y _
  obtain ⟨w,rfl⟩ := fromFree_surjective y
  simpa using stable w 1 one_mem

def normalLinear : (Fin d → k) →ₗ[k] Q.Presented k where
  toFun x := ∑ c, x c • normal c
  map_add' x y := by simp [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' r x := by simp [Pi.smul_apply,Finset.smul_sum,smul_smul]

theorem finite_of_span_top (htop : normalSpan Q k normal = ⊤) :
    Module.Finite k (Q.Presented k) ∧ Module.finrank k (Q.Presented k) ≤ d := by
  have hs : Function.Surjective (normalLinear normal) := by
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← htop]
    apply Submodule.span_le.mpr
    rintro _ ⟨c,rfl⟩
    refine ⟨Pi.single c 1, ?_⟩
    simp [normalLinear,Pi.single_apply]
  constructor
  · exact Module.Finite.of_surjective (normalLinear normal) hs
  · have H := LinearMap.finrank_le_finrank_of_surjective hs
    simpa using H

end UniserialComputations.Uniform.QuiverData
