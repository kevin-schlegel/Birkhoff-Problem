import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift10_0 (b : Fin 3) : PolyHom 10 0 :=
  ![PolyHom.zero 10 0,PolyHom.zero 10 0,PolyHom.zero 10 0] b
theorem polyLiftFree10_0 : ∀ b : Fin 3, (polyLift10_0 b).freeBlock=basisInt (homKind 10 0) b := by decide
def polyLift10_1 (b : Fin 3) : PolyHom 10 1 :=
  ![PolyHom.zero 10 1,PolyHom.zero 10 1,PolyHom.zero 10 1] b
theorem polyLiftFree10_1 : ∀ b : Fin 3, (polyLift10_1 b).freeBlock=basisInt (homKind 10 1) b := by decide
def polyLift10_2 (b : Fin 3) : PolyHom 10 2 :=
  ![PolyHom.zero 10 2,PolyHom.zero 10 2,PolyHom.zero 10 2] b
theorem polyLiftFree10_2 : ∀ b : Fin 3, (polyLift10_2 b).freeBlock=basisInt (homKind 10 2) b := by decide
def polyLift10_3 (b : Fin 3) : PolyHom 10 3 :=
  ![PolyHom.zero 10 3,PolyHom.zero 10 3,PolyHom.zero 10 3] b
theorem polyLiftFree10_3 : ∀ b : Fin 3, (polyLift10_3 b).freeBlock=basisInt (homKind 10 3) b := by decide
def polyLift10_4 (b : Fin 3) : PolyHom 10 4 :=
  ![PolyHom.zero 10 4,PolyHom.zero 10 4,PolyHom.zero 10 4] b
theorem polyLiftFree10_4 : ∀ b : Fin 3, (polyLift10_4 b).freeBlock=basisInt (homKind 10 4) b := by decide
def polyLift10_5 (b : Fin 3) : PolyHom 10 5 :=
  ![PolyHom.zero 10 5,PolyHom.zero 10 5,PolyHom.zero 10 5] b
theorem polyLiftFree10_5 : ∀ b : Fin 3, (polyLift10_5 b).freeBlock=basisInt (homKind 10 5) b := by decide
def polyLift10_6 (b : Fin 3) : PolyHom 10 6 :=
  ![PolyHom.zero 10 6,PolyHom.zero 10 6,PolyHom.zero 10 6] b
theorem polyLiftFree10_6 : ∀ b : Fin 3, (polyLift10_6 b).freeBlock=basisInt (homKind 10 6) b := by decide
def polyLift10_7 (b : Fin 3) : PolyHom 10 7 :=
  ![PolyHom.zero 10 7,PolyHom.zero 10 7,PolyHom.zero 10 7] b
theorem polyLiftFree10_7 : ∀ b : Fin 3, (polyLift10_7 b).freeBlock=basisInt (homKind 10 7) b := by decide
def polyLift10_8 (b : Fin 3) : PolyHom 10 8 :=
  ![PolyHom.zero 10 8,PolyHom.zero 10 8,PolyHom.zero 10 8] b
theorem polyLiftFree10_8 : ∀ b : Fin 3, (polyLift10_8 b).freeBlock=basisInt (homKind 10 8) b := by decide
def polyLift10_9 (b : Fin 3) : PolyHom 10 9 :=
  ![PolyHom.zero 10 9,PolyHom.zero 10 9,PolyHom.zero 10 9] b
theorem polyLiftFree10_9 : ∀ b : Fin 3, (polyLift10_9 b).freeBlock=basisInt (homKind 10 9) b := by decide
def polyRep10_10_0 : PolyHom 10 10 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift10_10 (b : Fin 3) : PolyHom 10 10 :=
  ![polyRep10_10_0,PolyHom.zero 10 10,PolyHom.zero 10 10] b
theorem polyLiftFree10_10 : ∀ b : Fin 3, (polyLift10_10 b).freeBlock=basisInt (homKind 10 10) b := by decide
def polyLift10_11 (b : Fin 3) : PolyHom 10 11 :=
  ![PolyHom.zero 10 11,PolyHom.zero 10 11,PolyHom.zero 10 11] b
theorem polyLiftFree10_11 : ∀ b : Fin 3, (polyLift10_11 b).freeBlock=basisInt (homKind 10 11) b := by decide
def polyLift10_12 (b : Fin 3) : PolyHom 10 12 :=
  ![PolyHom.zero 10 12,PolyHom.zero 10 12,PolyHom.zero 10 12] b
theorem polyLiftFree10_12 : ∀ b : Fin 3, (polyLift10_12 b).freeBlock=basisInt (homKind 10 12) b := by decide
def polyLift10_13 (b : Fin 3) : PolyHom 10 13 :=
  ![PolyHom.zero 10 13,PolyHom.zero 10 13,PolyHom.zero 10 13] b
theorem polyLiftFree10_13 : ∀ b : Fin 3, (polyLift10_13 b).freeBlock=basisInt (homKind 10 13) b := by decide
def polyLift10_14 (b : Fin 3) : PolyHom 10 14 :=
  ![PolyHom.zero 10 14,PolyHom.zero 10 14,PolyHom.zero 10 14] b
theorem polyLiftFree10_14 : ∀ b : Fin 3, (polyLift10_14 b).freeBlock=basisInt (homKind 10 14) b := by decide
def polyLift10_15 (b : Fin 3) : PolyHom 10 15 :=
  ![PolyHom.zero 10 15,PolyHom.zero 10 15,PolyHom.zero 10 15] b
theorem polyLiftFree10_15 : ∀ b : Fin 3, (polyLift10_15 b).freeBlock=basisInt (homKind 10 15) b := by decide
def polyLift10_16 (b : Fin 3) : PolyHom 10 16 :=
  ![PolyHom.zero 10 16,PolyHom.zero 10 16,PolyHom.zero 10 16] b
theorem polyLiftFree10_16 : ∀ b : Fin 3, (polyLift10_16 b).freeBlock=basisInt (homKind 10 16) b := by decide
def polyLift10_17 (b : Fin 3) : PolyHom 10 17 :=
  ![PolyHom.zero 10 17,PolyHom.zero 10 17,PolyHom.zero 10 17] b
theorem polyLiftFree10_17 : ∀ b : Fin 3, (polyLift10_17 b).freeBlock=basisInt (homKind 10 17) b := by decide
def polyLift10_18 (b : Fin 3) : PolyHom 10 18 :=
  ![PolyHom.zero 10 18,PolyHom.zero 10 18,PolyHom.zero 10 18] b
theorem polyLiftFree10_18 : ∀ b : Fin 3, (polyLift10_18 b).freeBlock=basisInt (homKind 10 18) b := by decide
def polyLift10_19 (b : Fin 3) : PolyHom 10 19 :=
  ![PolyHom.zero 10 19,PolyHom.zero 10 19,PolyHom.zero 10 19] b
theorem polyLiftFree10_19 : ∀ b : Fin 3, (polyLift10_19 b).freeBlock=basisInt (homKind 10 19) b := by decide
def polyLift10_20 (b : Fin 3) : PolyHom 10 20 :=
  ![PolyHom.zero 10 20,PolyHom.zero 10 20,PolyHom.zero 10 20] b
theorem polyLiftFree10_20 : ∀ b : Fin 3, (polyLift10_20 b).freeBlock=basisInt (homKind 10 20) b := by decide
def polyLift10_21 (b : Fin 3) : PolyHom 10 21 :=
  ![PolyHom.zero 10 21,PolyHom.zero 10 21,PolyHom.zero 10 21] b
theorem polyLiftFree10_21 : ∀ b : Fin 3, (polyLift10_21 b).freeBlock=basisInt (homKind 10 21) b := by decide
def polyLift10_22 (b : Fin 3) : PolyHom 10 22 :=
  ![PolyHom.zero 10 22,PolyHom.zero 10 22,PolyHom.zero 10 22] b
theorem polyLiftFree10_22 : ∀ b : Fin 3, (polyLift10_22 b).freeBlock=basisInt (homKind 10 22) b := by decide
def polyLift10_23 (b : Fin 3) : PolyHom 10 23 :=
  ![PolyHom.zero 10 23,PolyHom.zero 10 23,PolyHom.zero 10 23] b
theorem polyLiftFree10_23 : ∀ b : Fin 3, (polyLift10_23 b).freeBlock=basisInt (homKind 10 23) b := by decide
def polyLift10_24 (b : Fin 3) : PolyHom 10 24 :=
  ![PolyHom.zero 10 24,PolyHom.zero 10 24,PolyHom.zero 10 24] b
theorem polyLiftFree10_24 : ∀ b : Fin 3, (polyLift10_24 b).freeBlock=basisInt (homKind 10 24) b := by decide
def polyLift10_25 (b : Fin 3) : PolyHom 10 25 :=
  ![PolyHom.zero 10 25,PolyHom.zero 10 25,PolyHom.zero 10 25] b
theorem polyLiftFree10_25 : ∀ b : Fin 3, (polyLift10_25 b).freeBlock=basisInt (homKind 10 25) b := by decide
def polyLift10_26 (b : Fin 3) : PolyHom 10 26 :=
  ![PolyHom.zero 10 26,PolyHom.zero 10 26,PolyHom.zero 10 26] b
theorem polyLiftFree10_26 : ∀ b : Fin 3, (polyLift10_26 b).freeBlock=basisInt (homKind 10 26) b := by decide
def polyLift10_27 (b : Fin 3) : PolyHom 10 27 :=
  ![PolyHom.zero 10 27,PolyHom.zero 10 27,PolyHom.zero 10 27] b
theorem polyLiftFree10_27 : ∀ b : Fin 3, (polyLift10_27 b).freeBlock=basisInt (homKind 10 27) b := by decide
def polyLift10_28 (b : Fin 3) : PolyHom 10 28 :=
  ![PolyHom.zero 10 28,PolyHom.zero 10 28,PolyHom.zero 10 28] b
theorem polyLiftFree10_28 : ∀ b : Fin 3, (polyLift10_28 b).freeBlock=basisInt (homKind 10 28) b := by decide
def polyLift10_29 (b : Fin 3) : PolyHom 10 29 :=
  ![PolyHom.zero 10 29,PolyHom.zero 10 29,PolyHom.zero 10 29] b
theorem polyLiftFree10_29 : ∀ b : Fin 3, (polyLift10_29 b).freeBlock=basisInt (homKind 10 29) b := by decide
def polyLift10_30 (b : Fin 3) : PolyHom 10 30 :=
  ![PolyHom.zero 10 30,PolyHom.zero 10 30,PolyHom.zero 10 30] b
theorem polyLiftFree10_30 : ∀ b : Fin 3, (polyLift10_30 b).freeBlock=basisInt (homKind 10 30) b := by decide
def polyLift10_31 (b : Fin 3) : PolyHom 10 31 :=
  ![PolyHom.zero 10 31,PolyHom.zero 10 31,PolyHom.zero 10 31] b
theorem polyLiftFree10_31 : ∀ b : Fin 3, (polyLift10_31 b).freeBlock=basisInt (homKind 10 31) b := by decide
def polyLift10_32 (b : Fin 3) : PolyHom 10 32 :=
  ![PolyHom.zero 10 32,PolyHom.zero 10 32,PolyHom.zero 10 32] b
theorem polyLiftFree10_32 : ∀ b : Fin 3, (polyLift10_32 b).freeBlock=basisInt (homKind 10 32) b := by decide
def polyLift10_33 (b : Fin 3) : PolyHom 10 33 :=
  ![PolyHom.zero 10 33,PolyHom.zero 10 33,PolyHom.zero 10 33] b
theorem polyLiftFree10_33 : ∀ b : Fin 3, (polyLift10_33 b).freeBlock=basisInt (homKind 10 33) b := by decide
def polyLift10_34 (b : Fin 3) : PolyHom 10 34 :=
  ![PolyHom.zero 10 34,PolyHom.zero 10 34,PolyHom.zero 10 34] b
theorem polyLiftFree10_34 : ∀ b : Fin 3, (polyLift10_34 b).freeBlock=basisInt (homKind 10 34) b := by decide
def polyLift10_35 (b : Fin 3) : PolyHom 10 35 :=
  ![PolyHom.zero 10 35,PolyHom.zero 10 35,PolyHom.zero 10 35] b
theorem polyLiftFree10_35 : ∀ b : Fin 3, (polyLift10_35 b).freeBlock=basisInt (homKind 10 35) b := by decide
def polyLift10_36 (b : Fin 3) : PolyHom 10 36 :=
  ![PolyHom.zero 10 36,PolyHom.zero 10 36,PolyHom.zero 10 36] b
theorem polyLiftFree10_36 : ∀ b : Fin 3, (polyLift10_36 b).freeBlock=basisInt (homKind 10 36) b := by decide
def polyLift10_37 (b : Fin 3) : PolyHom 10 37 :=
  ![PolyHom.zero 10 37,PolyHom.zero 10 37,PolyHom.zero 10 37] b
theorem polyLiftFree10_37 : ∀ b : Fin 3, (polyLift10_37 b).freeBlock=basisInt (homKind 10 37) b := by decide
def polyLift10_38 (b : Fin 3) : PolyHom 10 38 :=
  ![PolyHom.zero 10 38,PolyHom.zero 10 38,PolyHom.zero 10 38] b
theorem polyLiftFree10_38 : ∀ b : Fin 3, (polyLift10_38 b).freeBlock=basisInt (homKind 10 38) b := by decide
def polyLift10_39 (b : Fin 3) : PolyHom 10 39 :=
  ![PolyHom.zero 10 39,PolyHom.zero 10 39,PolyHom.zero 10 39] b
theorem polyLiftFree10_39 : ∀ b : Fin 3, (polyLift10_39 b).freeBlock=basisInt (homKind 10 39) b := by decide
def polyLift10_40 (b : Fin 3) : PolyHom 10 40 :=
  ![PolyHom.zero 10 40,PolyHom.zero 10 40,PolyHom.zero 10 40] b
theorem polyLiftFree10_40 : ∀ b : Fin 3, (polyLift10_40 b).freeBlock=basisInt (homKind 10 40) b := by decide
def polyLift10_41 (b : Fin 3) : PolyHom 10 41 :=
  ![PolyHom.zero 10 41,PolyHom.zero 10 41,PolyHom.zero 10 41] b
theorem polyLiftFree10_41 : ∀ b : Fin 3, (polyLift10_41 b).freeBlock=basisInt (homKind 10 41) b := by decide
def polyLift10_42 (b : Fin 3) : PolyHom 10 42 :=
  ![PolyHom.zero 10 42,PolyHom.zero 10 42,PolyHom.zero 10 42] b
theorem polyLiftFree10_42 : ∀ b : Fin 3, (polyLift10_42 b).freeBlock=basisInt (homKind 10 42) b := by decide
def polyLift10_43 (b : Fin 3) : PolyHom 10 43 :=
  ![PolyHom.zero 10 43,PolyHom.zero 10 43,PolyHom.zero 10 43] b
theorem polyLiftFree10_43 : ∀ b : Fin 3, (polyLift10_43 b).freeBlock=basisInt (homKind 10 43) b := by decide
def polyLift10_44 (b : Fin 3) : PolyHom 10 44 :=
  ![PolyHom.zero 10 44,PolyHom.zero 10 44,PolyHom.zero 10 44] b
theorem polyLiftFree10_44 : ∀ b : Fin 3, (polyLift10_44 b).freeBlock=basisInt (homKind 10 44) b := by decide
def polyRep10_45_0 : PolyHom 10 45 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift10_45 (b : Fin 3) : PolyHom 10 45 :=
  ![polyRep10_45_0,PolyHom.zero 10 45,PolyHom.zero 10 45] b
theorem polyLiftFree10_45 : ∀ b : Fin 3, (polyLift10_45 b).freeBlock=basisInt (homKind 10 45) b := by decide
def polyLift10_46 (b : Fin 3) : PolyHom 10 46 :=
  ![PolyHom.zero 10 46,PolyHom.zero 10 46,PolyHom.zero 10 46] b
theorem polyLiftFree10_46 : ∀ b : Fin 3, (polyLift10_46 b).freeBlock=basisInt (homKind 10 46) b := by decide
def polyLiftRow10 (j : Fin 47) (b : Fin 3) : PolyHom 10 j :=
  match j with
  | ⟨0,_⟩ => polyLift10_0 b
  | ⟨1,_⟩ => polyLift10_1 b
  | ⟨2,_⟩ => polyLift10_2 b
  | ⟨3,_⟩ => polyLift10_3 b
  | ⟨4,_⟩ => polyLift10_4 b
  | ⟨5,_⟩ => polyLift10_5 b
  | ⟨6,_⟩ => polyLift10_6 b
  | ⟨7,_⟩ => polyLift10_7 b
  | ⟨8,_⟩ => polyLift10_8 b
  | ⟨9,_⟩ => polyLift10_9 b
  | ⟨10,_⟩ => polyLift10_10 b
  | ⟨11,_⟩ => polyLift10_11 b
  | ⟨12,_⟩ => polyLift10_12 b
  | ⟨13,_⟩ => polyLift10_13 b
  | ⟨14,_⟩ => polyLift10_14 b
  | ⟨15,_⟩ => polyLift10_15 b
  | ⟨16,_⟩ => polyLift10_16 b
  | ⟨17,_⟩ => polyLift10_17 b
  | ⟨18,_⟩ => polyLift10_18 b
  | ⟨19,_⟩ => polyLift10_19 b
  | ⟨20,_⟩ => polyLift10_20 b
  | ⟨21,_⟩ => polyLift10_21 b
  | ⟨22,_⟩ => polyLift10_22 b
  | ⟨23,_⟩ => polyLift10_23 b
  | ⟨24,_⟩ => polyLift10_24 b
  | ⟨25,_⟩ => polyLift10_25 b
  | ⟨26,_⟩ => polyLift10_26 b
  | ⟨27,_⟩ => polyLift10_27 b
  | ⟨28,_⟩ => polyLift10_28 b
  | ⟨29,_⟩ => polyLift10_29 b
  | ⟨30,_⟩ => polyLift10_30 b
  | ⟨31,_⟩ => polyLift10_31 b
  | ⟨32,_⟩ => polyLift10_32 b
  | ⟨33,_⟩ => polyLift10_33 b
  | ⟨34,_⟩ => polyLift10_34 b
  | ⟨35,_⟩ => polyLift10_35 b
  | ⟨36,_⟩ => polyLift10_36 b
  | ⟨37,_⟩ => polyLift10_37 b
  | ⟨38,_⟩ => polyLift10_38 b
  | ⟨39,_⟩ => polyLift10_39 b
  | ⟨40,_⟩ => polyLift10_40 b
  | ⟨41,_⟩ => polyLift10_41 b
  | ⟨42,_⟩ => polyLift10_42 b
  | ⟨43,_⟩ => polyLift10_43 b
  | ⟨44,_⟩ => polyLift10_44 b
  | ⟨45,_⟩ => polyLift10_45 b
  | ⟨46,_⟩ => polyLift10_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree10 (j : Fin 47) (b : Fin 3) : (polyLiftRow10 j b).freeBlock=basisInt (homKind 10 j) b := by
  fin_cases j
  · exact polyLiftFree10_0 b
  · exact polyLiftFree10_1 b
  · exact polyLiftFree10_2 b
  · exact polyLiftFree10_3 b
  · exact polyLiftFree10_4 b
  · exact polyLiftFree10_5 b
  · exact polyLiftFree10_6 b
  · exact polyLiftFree10_7 b
  · exact polyLiftFree10_8 b
  · exact polyLiftFree10_9 b
  · exact polyLiftFree10_10 b
  · exact polyLiftFree10_11 b
  · exact polyLiftFree10_12 b
  · exact polyLiftFree10_13 b
  · exact polyLiftFree10_14 b
  · exact polyLiftFree10_15 b
  · exact polyLiftFree10_16 b
  · exact polyLiftFree10_17 b
  · exact polyLiftFree10_18 b
  · exact polyLiftFree10_19 b
  · exact polyLiftFree10_20 b
  · exact polyLiftFree10_21 b
  · exact polyLiftFree10_22 b
  · exact polyLiftFree10_23 b
  · exact polyLiftFree10_24 b
  · exact polyLiftFree10_25 b
  · exact polyLiftFree10_26 b
  · exact polyLiftFree10_27 b
  · exact polyLiftFree10_28 b
  · exact polyLiftFree10_29 b
  · exact polyLiftFree10_30 b
  · exact polyLiftFree10_31 b
  · exact polyLiftFree10_32 b
  · exact polyLiftFree10_33 b
  · exact polyLiftFree10_34 b
  · exact polyLiftFree10_35 b
  · exact polyLiftFree10_36 b
  · exact polyLiftFree10_37 b
  · exact polyLiftFree10_38 b
  · exact polyLiftFree10_39 b
  · exact polyLiftFree10_40 b
  · exact polyLiftFree10_41 b
  · exact polyLiftFree10_42 b
  · exact polyLiftFree10_43 b
  · exact polyLiftFree10_44 b
  · exact polyLiftFree10_45 b
  · exact polyLiftFree10_46 b
end UniserialComputations.N6
