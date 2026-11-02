import N6Total
import N6BlockAlgebra
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
variable (k : Type*) [CommRing k]
def unitBlock (i : Fin 47) : Block k := fun r c => if r=c ∧ r.val<freeRank i then 1 else 0
lemma slot_eq_iff {i j : Fin 47} {r c : Fin 2} (hr : r.val<freeRank i) (hc : c.val<freeRank j) :
    (⟨i,⟨r.val,hr⟩⟩ : Slot)=⟨j,⟨c.val,hc⟩⟩ ↔ i=j ∧ r=c := by
  constructor
  · intro h
    refine ⟨congrArg Sigma.fst h,?_⟩
    apply Fin.ext
    exact congrArg (fun s : Slot => s.2.val) h
  · rintro ⟨rfl,rfl⟩
    rfl
theorem block_one (i j : Fin 47) : block k (1 : TotalMatrix k) i j=if i=j then unitBlock k i else 0 := by
  by_cases hij : i=j
  · subst j
    rw [if_pos rfl]
    ext r c
    by_cases hrc : r=c
    · subst c
      by_cases hr : r.val<freeRank i <;> simp [block,unitBlock,hr,Matrix.one_apply]
    · by_cases hr : r.val<freeRank i
      · by_cases hc : c.val<freeRank i
        · have hn : (⟨i,⟨r.val,hr⟩⟩ : Slot)≠⟨i,⟨c.val,hc⟩⟩ := by
            intro h; exact hrc ((slot_eq_iff hr hc).mp h).2
          simp [block,unitBlock,hr,hc,hrc,Matrix.one_apply,hn]
        · simp [block,unitBlock,hr,hc,hrc]
      · simp [block,unitBlock,hr,hrc]
  · rw [if_neg hij]
    ext r c
    by_cases hr : r.val<freeRank i
    · by_cases hc : c.val<freeRank j
      · have hn : (⟨i,⟨r.val,hr⟩⟩ : Slot)≠⟨j,⟨c.val,hc⟩⟩ := by
          intro h; exact hij ((slot_eq_iff hr hc).mp h).1
        simp [block,hr,hc,Matrix.one_apply,hn]
      · simp [block,hr,hc]
    · simp [block,hr]
theorem unit_normal_int : ∀ i : Fin 47, Normal ℤ (homKind i i) (unitBlock ℤ i) := by decide
theorem unit_normal (i : Fin 47) : Normal k (homKind i i) (unitBlock k i) := by
  have h := normal_cast k _ _ (unit_normal_int i)
  have he : (fun r c => (unitBlock ℤ i r c : k))=unitBlock k i := by
    ext r c
    unfold unitBlock
    split_ifs <;> norm_num
  rw [he] at h
  exact h
theorem block_one_normal (i j : Fin 47) : Normal k (homKind i j) (block k (1 : TotalMatrix k) i j) := by
  rw [block_one]
  split_ifs with h
  · subst j; exact unit_normal k i
  · exact normal_zero k _
end UniserialComputations.N6
