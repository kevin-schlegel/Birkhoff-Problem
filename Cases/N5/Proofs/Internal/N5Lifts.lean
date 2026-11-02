import N5Hom
noncomputable section
namespace UniserialComputations.N5.Raw
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h5 : π^5=0) (ann : ∀ r, π^4*r=0 ↔ ρ r=0)
include h5 in
lemma high_power (d : Nat) (hd : 5≤d) : π^d=0 := by
  obtain ⟨c,rfl⟩ := Nat.exists_eq_add_of_le hd
  rw [pow_add,h5,zero_mul]
include h5 in
def lift_0_0_0 : HomData π 0 0 where
  v := ![1,0,0,0,0,0,0,0,0,0,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_1_0_0 : HomData π 1 0 where
  v := ![1,0,0,0,0,0,0,0,0,0,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_1_1_0 : HomData π 1 1 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_2_0_0 : HomData π 2 0 where
  v := ![1,0,0,0,0,0,0,0,0,0,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_2_1_0 : HomData π 2 1 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_2_2_0 : HomData π 2 2 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_2_6_0 : HomData π 2 6 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_2_9_0 : HomData π 2 9 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_2_13_0 : HomData π 2 13 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_2_17_0 : HomData π 2 17 where
  v := ![1,0,0,0,0,0,0,0,0,0,1,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_3_0_0 : HomData π 3 0 where
  v := ![1,0,0,0,0,0,0,0,0,0,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_3_1_0 : HomData π 3 1 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_3_2_0 : HomData π 3 2 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_3_3_0 : HomData π 3 3 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_3_6_0 : HomData π 3 6 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_3_7_0 : HomData π 3 7 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_3_9_0 : HomData π 3 9 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_3_10_0 : HomData π 3 10 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_3_11_0 : HomData π 3 11 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_3_13_0 : HomData π 3 13 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_3_14_0 : HomData π 3 14 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_3_16_0 : HomData π 3 16 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_3_17_0 : HomData π 3 17 where
  v := ![1,0,0,0,0,0,0,0,0,0,1,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_4_0_0 : HomData π 4 0 where
  v := ![1,0,0,0,0,0,0,0,0,0,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_4_1_0 : HomData π 4 1 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_4_2_0 : HomData π 4 2 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_4_3_0 : HomData π 4 3 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_4_4_0 : HomData π 4 4 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_4_6_0 : HomData π 4 6 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_4_7_0 : HomData π 4 7 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_4_8_0 : HomData π 4 8 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_4_9_0 : HomData π 4 9 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_4_10_0 : HomData π 4 10 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_4_11_0 : HomData π 4 11 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_4_12_0 : HomData π 4 12 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_4_13_0 : HomData π 4 13 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_4_14_0 : HomData π 4 14 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_4_15_0 : HomData π 4 15 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_4_16_0 : HomData π 4 16 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_4_17_0 : HomData π 4 17 where
  v := ![1,0,0,0,0,0,0,0,0,0,1,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_4_17_1 : HomData π 4 17 where
  v := ![0,1,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_5_0_0 : HomData π 5 0 where
  v := ![1,0,0,0,0,0,0,0,0,0,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_5_1_0 : HomData π 5 1 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_5_2_0 : HomData π 5 2 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_5_3_0 : HomData π 5 3 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_5_4_0 : HomData π 5 4 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_5_5_0 : HomData π 5 5 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_5_6_0 : HomData π 5 6 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_5_7_0 : HomData π 5 7 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_5_8_0 : HomData π 5 8 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_5_9_0 : HomData π 5 9 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_5_10_0 : HomData π 5 10 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_5_11_0 : HomData π 5 11 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_5_12_0 : HomData π 5 12 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_5_13_0 : HomData π 5 13 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_5_14_0 : HomData π 5 14 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_5_15_0 : HomData π 5 15 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_5_16_0 : HomData π 5 16 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_5_17_0 : HomData π 5 17 where
  v := ![1,0,0,0,0,0,0,0,0,0,1,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_5_17_1 : HomData π 5 17 where
  v := ![0,1,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_6_0_0 : HomData π 6 0 where
  v := ![1,0,0,0,0,0,0,0,0,0,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_6_1_0 : HomData π 6 1 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_6_6_0 : HomData π 6 6 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_7_0_0 : HomData π 7 0 where
  v := ![1,0,0,0,0,0,0,0,0,0,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_7_1_0 : HomData π 7 1 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_7_2_0 : HomData π 7 2 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_7_6_0 : HomData π 7 6 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_7_7_0 : HomData π 7 7 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_7_9_0 : HomData π 7 9 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_7_10_0 : HomData π 7 10 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_7_13_0 : HomData π 7 13 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_7_16_0 : HomData π 7 16 where
  v := ![1,0,0,0,0,1,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_7_17_0 : HomData π 7 17 where
  v := ![1,0,0,0,0,0,0,0,0,0,1,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_8_0_0 : HomData π 8 0 where
  v := ![1,0,0,0,0,0,0,0,0,0,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_8_1_0 : HomData π 8 1 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_8_2_0 : HomData π 8 2 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_8_3_0 : HomData π 8 3 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_8_6_0 : HomData π 8 6 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_8_7_0 : HomData π 8 7 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_8_8_0 : HomData π 8 8 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_8_9_0 : HomData π 8 9 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_8_10_0 : HomData π 8 10 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_8_11_0 : HomData π 8 11 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_8_12_0 : HomData π 8 12 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_8_13_0 : HomData π 8 13 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_8_14_0 : HomData π 8 14 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_8_15_0 : HomData π 8 15 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_8_16_0 : HomData π 8 16 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_8_17_0 : HomData π 8 17 where
  v := ![1,0,0,0,0,0,0,0,0,0,1,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_8_17_1 : HomData π 8 17 where
  v := ![0,1,0,0,0,1,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_9_0_0 : HomData π 9 0 where
  v := ![1,0,0,0,0,0,0,0,0,0,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_9_1_0 : HomData π 9 1 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_9_6_0 : HomData π 9 6 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_9_9_0 : HomData π 9 9 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_10_0_0 : HomData π 10 0 where
  v := ![1,0,0,0,0,0,0,0,0,0,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_10_1_0 : HomData π 10 1 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_10_6_0 : HomData π 10 6 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_10_9_0 : HomData π 10 9 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_10_10_0 : HomData π 10 10 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_10_17_0 : HomData π 10 17 where
  v := ![1,π,0,0,0,1,0,0,0,1,1,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_11_0_0 : HomData π 11 0 where
  v := ![1,0,0,0,0,0,0,0,0,0,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_11_1_0 : HomData π 11 1 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_11_2_0 : HomData π 11 2 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_11_6_0 : HomData π 11 6 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_11_7_0 : HomData π 11 7 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_11_9_0 : HomData π 11 9 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_11_10_0 : HomData π 11 10 where
  v := ![1,0,0,0,π,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_11_11_0 : HomData π 11 11 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_11_13_0 : HomData π 11 13 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_11_14_0 : HomData π 11 14 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_11_16_0 : HomData π 11 16 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_11_17_0 : HomData π 11 17 where
  v := ![1,0,0,0,0,0,0,0,0,0,1,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_12_0_0 : HomData π 12 0 where
  v := ![1,0,0,0,0,0,0,0,0,0,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_12_1_0 : HomData π 12 1 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_12_2_0 : HomData π 12 2 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_12_6_0 : HomData π 12 6 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_12_7_0 : HomData π 12 7 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_12_9_0 : HomData π 12 9 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_12_10_0 : HomData π 12 10 where
  v := ![1,0,0,0,π,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_12_11_0 : HomData π 12 11 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_12_12_0 : HomData π 12 12 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_12_13_0 : HomData π 12 13 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_12_14_0 : HomData π 12 14 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_12_15_0 : HomData π 12 15 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_12_16_0 : HomData π 12 16 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_12_17_0 : HomData π 12 17 where
  v := ![1,0,0,0,0,0,0,0,0,0,1,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_13_0_0 : HomData π 13 0 where
  v := ![1,0,0,0,0,0,0,0,0,0,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_13_1_0 : HomData π 13 1 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_13_6_0 : HomData π 13 6 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_13_9_0 : HomData π 13 9 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_13_13_0 : HomData π 13 13 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_13_17_0 : HomData π 13 17 where
  v := ![1,0,0,0,-1,1,0,0,0,0,1,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_14_0_0 : HomData π 14 0 where
  v := ![1,0,0,0,0,0,0,0,0,0,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_14_1_0 : HomData π 14 1 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_14_6_0 : HomData π 14 6 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_14_9_0 : HomData π 14 9 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_14_10_0 : HomData π 14 10 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_14_13_0 : HomData π 14 13 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_14_14_0 : HomData π 14 14 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_14_16_0 : HomData π 14 16 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_14_17_0 : HomData π 14 17 where
  v := ![1,0,0,0,-1,1,0,0,0,0,1,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_15_0_0 : HomData π 15 0 where
  v := ![1,0,0,0,0,0,0,0,0,0,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_15_1_0 : HomData π 15 1 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_15_6_0 : HomData π 15 6 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_15_9_0 : HomData π 15 9 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_15_10_0 : HomData π 15 10 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_15_13_0 : HomData π 15 13 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_15_14_0 : HomData π 15 14 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_15_15_0 : HomData π 15 15 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_15_16_0 : HomData π 15 16 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_15_17_0 : HomData π 15 17 where
  v := ![1,0,0,0,-1,1,0,0,0,0,1,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_16_0_0 : HomData π 16 0 where
  v := ![1,0,0,0,0,0,0,0,0,0,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_16_1_0 : HomData π 16 1 where
  v := ![1,0,0,0,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_16_6_0 : HomData π 16 6 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_16_9_0 : HomData π 16 9 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_16_10_0 : HomData π 16 10 where
  v := ![1,0,0,0,1,0,0,1,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_16_13_0 : HomData π 16 13 where
  v := ![1,0,0,0,1,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_16_16_0 : HomData π 16 16 where
  v := ![1,0,0,0,1,0,0,0,1,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_16_17_0 : HomData π 16 17 where
  v := ![1,0,0,0,-1,1,0,0,0,0,1,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_17_0_0 : HomData π 17 0 where
  v := ![1,0,0,0,0,0,0,0,0,0,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_17_0_1 : HomData π 17 0 where
  v := ![0,0,0,1,0,0,0,0,0,0,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_17_1_0 : HomData π 17 1 where
  v := ![1,0,0,0,0,0,0,0,0,0,0,1,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_17_1_1 : HomData π 17 1 where
  v := ![0,0,0,1,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_17_2_0 : HomData π 17 2 where
  v := ![0,0,0,1,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_17_3_0 : HomData π 17 3 where
  v := ![-π,0,0,1,0,0,0,0,0,1,0,-1,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_17_6_0 : HomData π 17 6 where
  v := ![0,0,0,1,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_17_6_1 : HomData π 17 6 where
  v := ![1,0,0,0,0,0,0,1,0,0,0,1,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_17_7_0 : HomData π 17 7 where
  v := ![0,0,0,1,0,0,0,1,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_17_9_0 : HomData π 17 9 where
  v := ![0,0,0,1,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_17_9_1 : HomData π 17 9 where
  v := ![1,0,0,0,0,0,0,1,0,0,0,1,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_17_10_0 : HomData π 17 10 where
  v := ![0,0,0,1,0,0,0,π,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_17_11_0 : HomData π 17 11 where
  v := ![0,0,0,1,0,0,0,1,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_17_12_0 : HomData π 17 12 where
  v := ![0,0,0,1,0,0,0,1,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_17_13_0 : HomData π 17 13 where
  v := ![0,0,0,1,0,0,0,0,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_17_14_0 : HomData π 17 14 where
  v := ![0,0,0,1,0,0,0,1,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_17_15_0 : HomData π 17 15 where
  v := ![0,0,0,1,0,0,0,1,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_17_16_0 : HomData π 17 16 where
  v := ![0,0,0,1,0,0,0,1,0,1,0,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_17_17_0 : HomData π 17 17 where
  v := ![0,0,0,1,0,0,0,0,0,0,1,0,0]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
include h5 in
def lift_17_17_1 : HomData π 17 17 where
  v := ![1,0,0,0,1,0,0,0,1,1,0,0,1]
  commutes := by
    have p6 : π^6=0 := high_power π h5 6 (by decide)
    have p7 : π^7=0 := high_power π h5 7 (by decide)
    have p8 : π^8=0 := high_power π h5 8 (by decide)
    have p9 : π^9=0 := high_power π h5 9 (by decide)
    have p10 : π^10=0 := high_power π h5 10 (by decide)
    have p11 : π^11=0 := high_power π h5 11 (by decide)
    have p12 : π^12=0 := high_power π h5 12 (by decide)
    have p13 : π^13=0 := high_power π h5 13 (by decide)
    have p14 : π^14=0 := high_power π h5 14 (by decide)
    have p15 : π^15=0 := high_power π h5 15 (by decide)
    have p16 : π^16=0 := high_power π h5 16 (by decide)
    have p17 : π^17=0 := high_power π h5 17 (by decide)
    have p18 : π^18=0 := high_power π h5 18 (by decide)
    have p19 : π^19=0 := high_power π h5 19 (by decide)
    have p20 : π^20=0 := high_power π h5 20 (by decide)
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [h5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
end UniserialComputations.N5.Raw
