import N6ImageCheck0
import N6ImageCheck1
import N6ImageCheck2
import N6ImageCheck3
import N6ImageCheck4
import N6ImageCheck5
import N6ImageCheck6
import N6ImageCheck7
import N6ImageCheck8
import N6ImageCheck9
import N6ImageCheck10
import N6ImageCheck11
import N6ImageCheck12
import N6ImageCheck13
import N6ImageCheck14
import N6ImageCheck15
import N6ImageCheck16
import N6ImageCheck17
import N6ImageCheck18
import N6ImageCheck19
import N6ImageCheck20
import N6ImageCheck21
import N6ImageCheck22
import N6ImageCheck23
import N6ImageCheck24
import N6ImageCheck25
import N6ImageCheck26
import N6ImageCheck27
import N6ImageCheck28
import N6ImageCheck29
import N6ImageCheck30
import N6ImageCheck31
import N6ImageCheck32
import N6ImageCheck33
import N6ImageCheck34
import N6ImageCheck35
import N6ImageCheck36
import N6ImageCheck37
import N6ImageCheck38
import N6ImageCheck39
import N6ImageCheck40
import N6ImageCheck41
import N6ImageCheck42
import N6ImageCheck43
import N6ImageCheck44
import N6ImageCheck45
import N6ImageCheck46
import N6ImageStep0
import N6ImageStep1
import N6ImageStep2
import N6ImageStep3
import N6ImageStep4
import N6ImageStep5
import N6ImageStep6
import N6ImageStep7
import N6ImageStep8
import N6ImageStep9
import N6ImageStep10
import N6ImageStep11
import N6ImageStep12
import N6ImageStep13
import N6ImageStep14
import N6ImageStep15
import N6ImageStep16
import N6ImageStep17
import N6ImageStep18
import N6ImageStep19
import N6ImageStep20
import N6ImageStep21
import N6ImageStep22
import N6ImageStep23
import N6ImageStep24
import N6ImageStep25
import N6ImageStep26
import N6ImageStep27
import N6ImageStep28
import N6ImageStep29
import N6ImageStep30
import N6ImageStep31
import N6ImageStep32
import N6ImageStep33
import N6ImageStep34
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
variable (k : Type*) [Field k]
lemma basis_paths_certificate (i j : Fin 47) (b : Fin 3) :
    ((basisPaths i j b).map (fun u => u.1 • normalBlock u.2)).sum=basisBlock ℤ (homKind i j) b ∧
    (basisPaths i j b).all (fun u => normalTarget u.2 == i && normalSource u.2 == j)=true := by
  fin_cases i
  · exact basis_paths_0 j b
  · exact basis_paths_1 j b
  · exact basis_paths_2 j b
  · exact basis_paths_3 j b
  · exact basis_paths_4 j b
  · exact basis_paths_5 j b
  · exact basis_paths_6 j b
  · exact basis_paths_7 j b
  · exact basis_paths_8 j b
  · exact basis_paths_9 j b
  · exact basis_paths_10 j b
  · exact basis_paths_11 j b
  · exact basis_paths_12 j b
  · exact basis_paths_13 j b
  · exact basis_paths_14 j b
  · exact basis_paths_15 j b
  · exact basis_paths_16 j b
  · exact basis_paths_17 j b
  · exact basis_paths_18 j b
  · exact basis_paths_19 j b
  · exact basis_paths_20 j b
  · exact basis_paths_21 j b
  · exact basis_paths_22 j b
  · exact basis_paths_23 j b
  · exact basis_paths_24 j b
  · exact basis_paths_25 j b
  · exact basis_paths_26 j b
  · exact basis_paths_27 j b
  · exact basis_paths_28 j b
  · exact basis_paths_29 j b
  · exact basis_paths_30 j b
  · exact basis_paths_31 j b
  · exact basis_paths_32 j b
  · exact basis_paths_33 j b
  · exact basis_paths_34 j b
  · exact basis_paths_35 j b
  · exact basis_paths_36 j b
  · exact basis_paths_37 j b
  · exact basis_paths_38 j b
  · exact basis_paths_39 j b
  · exact basis_paths_40 j b
  · exact basis_paths_41 j b
  · exact basis_paths_42 j b
  · exact basis_paths_43 j b
  · exact basis_paths_44 j b
  · exact basis_paths_45 j b
  · exact basis_paths_46 j b
lemma normal_step (c : Fin 1708) : if c.val<47 then normalPath c=[] ∧ normalBlock c=unitBlock ℤ (normalSource c)
  else (normalPrevious c).val<c.val ∧ normalSource (normalPrevious c)=normalSource c ∧
    normalPath c=normalPath (normalPrevious c)++[normalLast c] ∧
    normalBlock c=arrowMatrix ℤ (normalLast c)*normalBlock (normalPrevious c) := by
  have hb : c.val/50<35 := by omega
  interval_cases hq : c.val/50
  · let x : Fin 50 := ⟨c.val-0,by omega⟩
    have hx : (⟨x.val+0,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_0 x
  · let x : Fin 50 := ⟨c.val-50,by omega⟩
    have hx : (⟨x.val+50,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_1 x
  · let x : Fin 50 := ⟨c.val-100,by omega⟩
    have hx : (⟨x.val+100,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_2 x
  · let x : Fin 50 := ⟨c.val-150,by omega⟩
    have hx : (⟨x.val+150,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_3 x
  · let x : Fin 50 := ⟨c.val-200,by omega⟩
    have hx : (⟨x.val+200,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_4 x
  · let x : Fin 50 := ⟨c.val-250,by omega⟩
    have hx : (⟨x.val+250,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_5 x
  · let x : Fin 50 := ⟨c.val-300,by omega⟩
    have hx : (⟨x.val+300,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_6 x
  · let x : Fin 50 := ⟨c.val-350,by omega⟩
    have hx : (⟨x.val+350,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_7 x
  · let x : Fin 50 := ⟨c.val-400,by omega⟩
    have hx : (⟨x.val+400,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_8 x
  · let x : Fin 50 := ⟨c.val-450,by omega⟩
    have hx : (⟨x.val+450,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_9 x
  · let x : Fin 50 := ⟨c.val-500,by omega⟩
    have hx : (⟨x.val+500,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_10 x
  · let x : Fin 50 := ⟨c.val-550,by omega⟩
    have hx : (⟨x.val+550,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_11 x
  · let x : Fin 50 := ⟨c.val-600,by omega⟩
    have hx : (⟨x.val+600,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_12 x
  · let x : Fin 50 := ⟨c.val-650,by omega⟩
    have hx : (⟨x.val+650,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_13 x
  · let x : Fin 50 := ⟨c.val-700,by omega⟩
    have hx : (⟨x.val+700,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_14 x
  · let x : Fin 50 := ⟨c.val-750,by omega⟩
    have hx : (⟨x.val+750,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_15 x
  · let x : Fin 50 := ⟨c.val-800,by omega⟩
    have hx : (⟨x.val+800,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_16 x
  · let x : Fin 50 := ⟨c.val-850,by omega⟩
    have hx : (⟨x.val+850,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_17 x
  · let x : Fin 50 := ⟨c.val-900,by omega⟩
    have hx : (⟨x.val+900,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_18 x
  · let x : Fin 50 := ⟨c.val-950,by omega⟩
    have hx : (⟨x.val+950,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_19 x
  · let x : Fin 50 := ⟨c.val-1000,by omega⟩
    have hx : (⟨x.val+1000,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_20 x
  · let x : Fin 50 := ⟨c.val-1050,by omega⟩
    have hx : (⟨x.val+1050,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_21 x
  · let x : Fin 50 := ⟨c.val-1100,by omega⟩
    have hx : (⟨x.val+1100,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_22 x
  · let x : Fin 50 := ⟨c.val-1150,by omega⟩
    have hx : (⟨x.val+1150,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_23 x
  · let x : Fin 50 := ⟨c.val-1200,by omega⟩
    have hx : (⟨x.val+1200,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_24 x
  · let x : Fin 50 := ⟨c.val-1250,by omega⟩
    have hx : (⟨x.val+1250,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_25 x
  · let x : Fin 50 := ⟨c.val-1300,by omega⟩
    have hx : (⟨x.val+1300,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_26 x
  · let x : Fin 50 := ⟨c.val-1350,by omega⟩
    have hx : (⟨x.val+1350,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_27 x
  · let x : Fin 50 := ⟨c.val-1400,by omega⟩
    have hx : (⟨x.val+1400,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_28 x
  · let x : Fin 50 := ⟨c.val-1450,by omega⟩
    have hx : (⟨x.val+1450,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_29 x
  · let x : Fin 50 := ⟨c.val-1500,by omega⟩
    have hx : (⟨x.val+1500,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_30 x
  · let x : Fin 50 := ⟨c.val-1550,by omega⟩
    have hx : (⟨x.val+1550,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_31 x
  · let x : Fin 50 := ⟨c.val-1600,by omega⟩
    have hx : (⟨x.val+1600,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_32 x
  · let x : Fin 50 := ⟨c.val-1650,by omega⟩
    have hx : (⟨x.val+1650,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_33 x
  · let x : Fin 8 := ⟨c.val-1700,by omega⟩
    have hx : (⟨x.val+1700,by omega⟩ : Fin 1708)=c := by apply Fin.ext; dsimp [x] <;> omega
    rw [←hx]
    exact normal_step_34 x
lemma normalBlock_isWalk (c : Fin 1708) : localWalk ℤ (normalSource c) (normalPath c)=normalBlock c := by
  have aux : ∀ n : Nat, ∀ c : Fin 1708, c.val=n → localWalk ℤ (normalSource c) (normalPath c)=normalBlock c := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro c hc
      have hs := normal_step c
      split_ifs at hs with hsmall
      · rw [hs.1,hs.2]
        simp [localWalk,wordMatrix]
      · rw [hs.2.2.1,localWalk_snoc,← hs.2.1]
        rw [ih (normalPrevious c).val (by omega) (normalPrevious c) rfl]
        exact hs.2.2.2.symm
  exact aux c.val c rfl

def castBlock : Block ℤ →+* Block k := (Int.castRingHom k).mapMatrix
lemma castBlock_arrow (b : Fin 75) : castBlock k (arrowMatrix ℤ b)=arrowMatrix k b := by
  fin_cases b <;> ext r c <;> fin_cases r <;> fin_cases c <;> norm_num [castBlock,arrowMatrix,RingHom.mapMatrix_apply,Matrix.map_apply]
lemma castBlock_unit (s : Fin 47) : castBlock k (unitBlock ℤ s)=unitBlock k s := by
  ext r c
  simp only [castBlock,RingHom.mapMatrix_apply,Matrix.map_apply,unitBlock]
  split_ifs <;> norm_num
lemma castBlock_basis (t : Fin 14) (b : Fin 3) : castBlock k (basisBlock ℤ t b)=basisBlock k t b := by
  ext r c
  simp [castBlock,RingHom.mapMatrix_apply,Matrix.map_apply,basisBlock]
lemma castBlock_walk (s : Fin 47) (p : List (Fin 75)) : castBlock k (localWalk ℤ s p)=localWalk k s p := by
  simp only [localWalk,wordMatrix,map_mul,map_list_prod,List.map_map,Function.comp_def,castBlock_arrow,castBlock_unit]
lemma normal_image (c : Fin 1708) : (evaluate k (normalRep k c)).val=insert k (normalTarget c) (normalSource c) (castBlock k (normalBlock c)) := by
  rw [normalRep,evaluate_walk k _ _ _ (normal_endpoints c),← castBlock_walk,normalBlock_isWalk]
end UniserialComputations.N6.Presentation
