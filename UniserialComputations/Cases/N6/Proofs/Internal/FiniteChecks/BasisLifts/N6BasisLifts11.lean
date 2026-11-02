import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift11_0 (b : Fin 3) : PolyHom 11 0 :=
  ![PolyHom.zero 11 0,PolyHom.zero 11 0,PolyHom.zero 11 0] b
theorem polyLiftFree11_0 : ∀ b : Fin 3, (polyLift11_0 b).freeBlock=basisInt (homKind 11 0) b := by decide
def polyLift11_1 (b : Fin 3) : PolyHom 11 1 :=
  ![PolyHom.zero 11 1,PolyHom.zero 11 1,PolyHom.zero 11 1] b
theorem polyLiftFree11_1 : ∀ b : Fin 3, (polyLift11_1 b).freeBlock=basisInt (homKind 11 1) b := by decide
def polyLift11_2 (b : Fin 3) : PolyHom 11 2 :=
  ![PolyHom.zero 11 2,PolyHom.zero 11 2,PolyHom.zero 11 2] b
theorem polyLiftFree11_2 : ∀ b : Fin 3, (polyLift11_2 b).freeBlock=basisInt (homKind 11 2) b := by decide
def polyLift11_3 (b : Fin 3) : PolyHom 11 3 :=
  ![PolyHom.zero 11 3,PolyHom.zero 11 3,PolyHom.zero 11 3] b
theorem polyLiftFree11_3 : ∀ b : Fin 3, (polyLift11_3 b).freeBlock=basisInt (homKind 11 3) b := by decide
def polyLift11_4 (b : Fin 3) : PolyHom 11 4 :=
  ![PolyHom.zero 11 4,PolyHom.zero 11 4,PolyHom.zero 11 4] b
theorem polyLiftFree11_4 : ∀ b : Fin 3, (polyLift11_4 b).freeBlock=basisInt (homKind 11 4) b := by decide
def polyLift11_5 (b : Fin 3) : PolyHom 11 5 :=
  ![PolyHom.zero 11 5,PolyHom.zero 11 5,PolyHom.zero 11 5] b
theorem polyLiftFree11_5 : ∀ b : Fin 3, (polyLift11_5 b).freeBlock=basisInt (homKind 11 5) b := by decide
def polyLift11_6 (b : Fin 3) : PolyHom 11 6 :=
  ![PolyHom.zero 11 6,PolyHom.zero 11 6,PolyHom.zero 11 6] b
theorem polyLiftFree11_6 : ∀ b : Fin 3, (polyLift11_6 b).freeBlock=basisInt (homKind 11 6) b := by decide
def polyLift11_7 (b : Fin 3) : PolyHom 11 7 :=
  ![PolyHom.zero 11 7,PolyHom.zero 11 7,PolyHom.zero 11 7] b
theorem polyLiftFree11_7 : ∀ b : Fin 3, (polyLift11_7 b).freeBlock=basisInt (homKind 11 7) b := by decide
def polyLift11_8 (b : Fin 3) : PolyHom 11 8 :=
  ![PolyHom.zero 11 8,PolyHom.zero 11 8,PolyHom.zero 11 8] b
theorem polyLiftFree11_8 : ∀ b : Fin 3, (polyLift11_8 b).freeBlock=basisInt (homKind 11 8) b := by decide
def polyLift11_9 (b : Fin 3) : PolyHom 11 9 :=
  ![PolyHom.zero 11 9,PolyHom.zero 11 9,PolyHom.zero 11 9] b
theorem polyLiftFree11_9 : ∀ b : Fin 3, (polyLift11_9 b).freeBlock=basisInt (homKind 11 9) b := by decide
def polyRep11_10_0 : PolyHom 11 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift11_10 (b : Fin 3) : PolyHom 11 10 :=
  ![polyRep11_10_0,PolyHom.zero 11 10,PolyHom.zero 11 10] b
theorem polyLiftFree11_10 : ∀ b : Fin 3, (polyLift11_10 b).freeBlock=basisInt (homKind 11 10) b := by decide
def polyRep11_11_0 : PolyHom 11 11 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift11_11 (b : Fin 3) : PolyHom 11 11 :=
  ![polyRep11_11_0,PolyHom.zero 11 11,PolyHom.zero 11 11] b
theorem polyLiftFree11_11 : ∀ b : Fin 3, (polyLift11_11 b).freeBlock=basisInt (homKind 11 11) b := by decide
def polyLift11_12 (b : Fin 3) : PolyHom 11 12 :=
  ![PolyHom.zero 11 12,PolyHom.zero 11 12,PolyHom.zero 11 12] b
theorem polyLiftFree11_12 : ∀ b : Fin 3, (polyLift11_12 b).freeBlock=basisInt (homKind 11 12) b := by decide
def polyLift11_13 (b : Fin 3) : PolyHom 11 13 :=
  ![PolyHom.zero 11 13,PolyHom.zero 11 13,PolyHom.zero 11 13] b
theorem polyLiftFree11_13 : ∀ b : Fin 3, (polyLift11_13 b).freeBlock=basisInt (homKind 11 13) b := by decide
def polyLift11_14 (b : Fin 3) : PolyHom 11 14 :=
  ![PolyHom.zero 11 14,PolyHom.zero 11 14,PolyHom.zero 11 14] b
theorem polyLiftFree11_14 : ∀ b : Fin 3, (polyLift11_14 b).freeBlock=basisInt (homKind 11 14) b := by decide
def polyLift11_15 (b : Fin 3) : PolyHom 11 15 :=
  ![PolyHom.zero 11 15,PolyHom.zero 11 15,PolyHom.zero 11 15] b
theorem polyLiftFree11_15 : ∀ b : Fin 3, (polyLift11_15 b).freeBlock=basisInt (homKind 11 15) b := by decide
def polyLift11_16 (b : Fin 3) : PolyHom 11 16 :=
  ![PolyHom.zero 11 16,PolyHom.zero 11 16,PolyHom.zero 11 16] b
theorem polyLiftFree11_16 : ∀ b : Fin 3, (polyLift11_16 b).freeBlock=basisInt (homKind 11 16) b := by decide
def polyLift11_17 (b : Fin 3) : PolyHom 11 17 :=
  ![PolyHom.zero 11 17,PolyHom.zero 11 17,PolyHom.zero 11 17] b
theorem polyLiftFree11_17 : ∀ b : Fin 3, (polyLift11_17 b).freeBlock=basisInt (homKind 11 17) b := by decide
def polyLift11_18 (b : Fin 3) : PolyHom 11 18 :=
  ![PolyHom.zero 11 18,PolyHom.zero 11 18,PolyHom.zero 11 18] b
theorem polyLiftFree11_18 : ∀ b : Fin 3, (polyLift11_18 b).freeBlock=basisInt (homKind 11 18) b := by decide
def polyLift11_19 (b : Fin 3) : PolyHom 11 19 :=
  ![PolyHom.zero 11 19,PolyHom.zero 11 19,PolyHom.zero 11 19] b
theorem polyLiftFree11_19 : ∀ b : Fin 3, (polyLift11_19 b).freeBlock=basisInt (homKind 11 19) b := by decide
def polyLift11_20 (b : Fin 3) : PolyHom 11 20 :=
  ![PolyHom.zero 11 20,PolyHom.zero 11 20,PolyHom.zero 11 20] b
theorem polyLiftFree11_20 : ∀ b : Fin 3, (polyLift11_20 b).freeBlock=basisInt (homKind 11 20) b := by decide
def polyLift11_21 (b : Fin 3) : PolyHom 11 21 :=
  ![PolyHom.zero 11 21,PolyHom.zero 11 21,PolyHom.zero 11 21] b
theorem polyLiftFree11_21 : ∀ b : Fin 3, (polyLift11_21 b).freeBlock=basisInt (homKind 11 21) b := by decide
def polyLift11_22 (b : Fin 3) : PolyHom 11 22 :=
  ![PolyHom.zero 11 22,PolyHom.zero 11 22,PolyHom.zero 11 22] b
theorem polyLiftFree11_22 : ∀ b : Fin 3, (polyLift11_22 b).freeBlock=basisInt (homKind 11 22) b := by decide
def polyLift11_23 (b : Fin 3) : PolyHom 11 23 :=
  ![PolyHom.zero 11 23,PolyHom.zero 11 23,PolyHom.zero 11 23] b
theorem polyLiftFree11_23 : ∀ b : Fin 3, (polyLift11_23 b).freeBlock=basisInt (homKind 11 23) b := by decide
def polyLift11_24 (b : Fin 3) : PolyHom 11 24 :=
  ![PolyHom.zero 11 24,PolyHom.zero 11 24,PolyHom.zero 11 24] b
theorem polyLiftFree11_24 : ∀ b : Fin 3, (polyLift11_24 b).freeBlock=basisInt (homKind 11 24) b := by decide
def polyLift11_25 (b : Fin 3) : PolyHom 11 25 :=
  ![PolyHom.zero 11 25,PolyHom.zero 11 25,PolyHom.zero 11 25] b
theorem polyLiftFree11_25 : ∀ b : Fin 3, (polyLift11_25 b).freeBlock=basisInt (homKind 11 25) b := by decide
def polyLift11_26 (b : Fin 3) : PolyHom 11 26 :=
  ![PolyHom.zero 11 26,PolyHom.zero 11 26,PolyHom.zero 11 26] b
theorem polyLiftFree11_26 : ∀ b : Fin 3, (polyLift11_26 b).freeBlock=basisInt (homKind 11 26) b := by decide
def polyLift11_27 (b : Fin 3) : PolyHom 11 27 :=
  ![PolyHom.zero 11 27,PolyHom.zero 11 27,PolyHom.zero 11 27] b
theorem polyLiftFree11_27 : ∀ b : Fin 3, (polyLift11_27 b).freeBlock=basisInt (homKind 11 27) b := by decide
def polyLift11_28 (b : Fin 3) : PolyHom 11 28 :=
  ![PolyHom.zero 11 28,PolyHom.zero 11 28,PolyHom.zero 11 28] b
theorem polyLiftFree11_28 : ∀ b : Fin 3, (polyLift11_28 b).freeBlock=basisInt (homKind 11 28) b := by decide
def polyLift11_29 (b : Fin 3) : PolyHom 11 29 :=
  ![PolyHom.zero 11 29,PolyHom.zero 11 29,PolyHom.zero 11 29] b
theorem polyLiftFree11_29 : ∀ b : Fin 3, (polyLift11_29 b).freeBlock=basisInt (homKind 11 29) b := by decide
def polyLift11_30 (b : Fin 3) : PolyHom 11 30 :=
  ![PolyHom.zero 11 30,PolyHom.zero 11 30,PolyHom.zero 11 30] b
theorem polyLiftFree11_30 : ∀ b : Fin 3, (polyLift11_30 b).freeBlock=basisInt (homKind 11 30) b := by decide
def polyLift11_31 (b : Fin 3) : PolyHom 11 31 :=
  ![PolyHom.zero 11 31,PolyHom.zero 11 31,PolyHom.zero 11 31] b
theorem polyLiftFree11_31 : ∀ b : Fin 3, (polyLift11_31 b).freeBlock=basisInt (homKind 11 31) b := by decide
def polyLift11_32 (b : Fin 3) : PolyHom 11 32 :=
  ![PolyHom.zero 11 32,PolyHom.zero 11 32,PolyHom.zero 11 32] b
theorem polyLiftFree11_32 : ∀ b : Fin 3, (polyLift11_32 b).freeBlock=basisInt (homKind 11 32) b := by decide
def polyLift11_33 (b : Fin 3) : PolyHom 11 33 :=
  ![PolyHom.zero 11 33,PolyHom.zero 11 33,PolyHom.zero 11 33] b
theorem polyLiftFree11_33 : ∀ b : Fin 3, (polyLift11_33 b).freeBlock=basisInt (homKind 11 33) b := by decide
def polyLift11_34 (b : Fin 3) : PolyHom 11 34 :=
  ![PolyHom.zero 11 34,PolyHom.zero 11 34,PolyHom.zero 11 34] b
theorem polyLiftFree11_34 : ∀ b : Fin 3, (polyLift11_34 b).freeBlock=basisInt (homKind 11 34) b := by decide
def polyLift11_35 (b : Fin 3) : PolyHom 11 35 :=
  ![PolyHom.zero 11 35,PolyHom.zero 11 35,PolyHom.zero 11 35] b
theorem polyLiftFree11_35 : ∀ b : Fin 3, (polyLift11_35 b).freeBlock=basisInt (homKind 11 35) b := by decide
def polyLift11_36 (b : Fin 3) : PolyHom 11 36 :=
  ![PolyHom.zero 11 36,PolyHom.zero 11 36,PolyHom.zero 11 36] b
theorem polyLiftFree11_36 : ∀ b : Fin 3, (polyLift11_36 b).freeBlock=basisInt (homKind 11 36) b := by decide
def polyLift11_37 (b : Fin 3) : PolyHom 11 37 :=
  ![PolyHom.zero 11 37,PolyHom.zero 11 37,PolyHom.zero 11 37] b
theorem polyLiftFree11_37 : ∀ b : Fin 3, (polyLift11_37 b).freeBlock=basisInt (homKind 11 37) b := by decide
def polyLift11_38 (b : Fin 3) : PolyHom 11 38 :=
  ![PolyHom.zero 11 38,PolyHom.zero 11 38,PolyHom.zero 11 38] b
theorem polyLiftFree11_38 : ∀ b : Fin 3, (polyLift11_38 b).freeBlock=basisInt (homKind 11 38) b := by decide
def polyLift11_39 (b : Fin 3) : PolyHom 11 39 :=
  ![PolyHom.zero 11 39,PolyHom.zero 11 39,PolyHom.zero 11 39] b
theorem polyLiftFree11_39 : ∀ b : Fin 3, (polyLift11_39 b).freeBlock=basisInt (homKind 11 39) b := by decide
def polyLift11_40 (b : Fin 3) : PolyHom 11 40 :=
  ![PolyHom.zero 11 40,PolyHom.zero 11 40,PolyHom.zero 11 40] b
theorem polyLiftFree11_40 : ∀ b : Fin 3, (polyLift11_40 b).freeBlock=basisInt (homKind 11 40) b := by decide
def polyLift11_41 (b : Fin 3) : PolyHom 11 41 :=
  ![PolyHom.zero 11 41,PolyHom.zero 11 41,PolyHom.zero 11 41] b
theorem polyLiftFree11_41 : ∀ b : Fin 3, (polyLift11_41 b).freeBlock=basisInt (homKind 11 41) b := by decide
def polyLift11_42 (b : Fin 3) : PolyHom 11 42 :=
  ![PolyHom.zero 11 42,PolyHom.zero 11 42,PolyHom.zero 11 42] b
theorem polyLiftFree11_42 : ∀ b : Fin 3, (polyLift11_42 b).freeBlock=basisInt (homKind 11 42) b := by decide
def polyLift11_43 (b : Fin 3) : PolyHom 11 43 :=
  ![PolyHom.zero 11 43,PolyHom.zero 11 43,PolyHom.zero 11 43] b
theorem polyLiftFree11_43 : ∀ b : Fin 3, (polyLift11_43 b).freeBlock=basisInt (homKind 11 43) b := by decide
def polyLift11_44 (b : Fin 3) : PolyHom 11 44 :=
  ![PolyHom.zero 11 44,PolyHom.zero 11 44,PolyHom.zero 11 44] b
theorem polyLiftFree11_44 : ∀ b : Fin 3, (polyLift11_44 b).freeBlock=basisInt (homKind 11 44) b := by decide
def polyRep11_45_0 : PolyHom 11 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift11_45 (b : Fin 3) : PolyHom 11 45 :=
  ![polyRep11_45_0,PolyHom.zero 11 45,PolyHom.zero 11 45] b
theorem polyLiftFree11_45 : ∀ b : Fin 3, (polyLift11_45 b).freeBlock=basisInt (homKind 11 45) b := by decide
def polyLift11_46 (b : Fin 3) : PolyHom 11 46 :=
  ![PolyHom.zero 11 46,PolyHom.zero 11 46,PolyHom.zero 11 46] b
theorem polyLiftFree11_46 : ∀ b : Fin 3, (polyLift11_46 b).freeBlock=basisInt (homKind 11 46) b := by decide
def polyLiftRow11 (j : Fin 47) (b : Fin 3) : PolyHom 11 j :=
  match j with
  | ⟨0,_⟩ => polyLift11_0 b
  | ⟨1,_⟩ => polyLift11_1 b
  | ⟨2,_⟩ => polyLift11_2 b
  | ⟨3,_⟩ => polyLift11_3 b
  | ⟨4,_⟩ => polyLift11_4 b
  | ⟨5,_⟩ => polyLift11_5 b
  | ⟨6,_⟩ => polyLift11_6 b
  | ⟨7,_⟩ => polyLift11_7 b
  | ⟨8,_⟩ => polyLift11_8 b
  | ⟨9,_⟩ => polyLift11_9 b
  | ⟨10,_⟩ => polyLift11_10 b
  | ⟨11,_⟩ => polyLift11_11 b
  | ⟨12,_⟩ => polyLift11_12 b
  | ⟨13,_⟩ => polyLift11_13 b
  | ⟨14,_⟩ => polyLift11_14 b
  | ⟨15,_⟩ => polyLift11_15 b
  | ⟨16,_⟩ => polyLift11_16 b
  | ⟨17,_⟩ => polyLift11_17 b
  | ⟨18,_⟩ => polyLift11_18 b
  | ⟨19,_⟩ => polyLift11_19 b
  | ⟨20,_⟩ => polyLift11_20 b
  | ⟨21,_⟩ => polyLift11_21 b
  | ⟨22,_⟩ => polyLift11_22 b
  | ⟨23,_⟩ => polyLift11_23 b
  | ⟨24,_⟩ => polyLift11_24 b
  | ⟨25,_⟩ => polyLift11_25 b
  | ⟨26,_⟩ => polyLift11_26 b
  | ⟨27,_⟩ => polyLift11_27 b
  | ⟨28,_⟩ => polyLift11_28 b
  | ⟨29,_⟩ => polyLift11_29 b
  | ⟨30,_⟩ => polyLift11_30 b
  | ⟨31,_⟩ => polyLift11_31 b
  | ⟨32,_⟩ => polyLift11_32 b
  | ⟨33,_⟩ => polyLift11_33 b
  | ⟨34,_⟩ => polyLift11_34 b
  | ⟨35,_⟩ => polyLift11_35 b
  | ⟨36,_⟩ => polyLift11_36 b
  | ⟨37,_⟩ => polyLift11_37 b
  | ⟨38,_⟩ => polyLift11_38 b
  | ⟨39,_⟩ => polyLift11_39 b
  | ⟨40,_⟩ => polyLift11_40 b
  | ⟨41,_⟩ => polyLift11_41 b
  | ⟨42,_⟩ => polyLift11_42 b
  | ⟨43,_⟩ => polyLift11_43 b
  | ⟨44,_⟩ => polyLift11_44 b
  | ⟨45,_⟩ => polyLift11_45 b
  | ⟨46,_⟩ => polyLift11_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree11 (j : Fin 47) (b : Fin 3) : (polyLiftRow11 j b).freeBlock=basisInt (homKind 11 j) b := by
  fin_cases j
  · exact polyLiftFree11_0 b
  · exact polyLiftFree11_1 b
  · exact polyLiftFree11_2 b
  · exact polyLiftFree11_3 b
  · exact polyLiftFree11_4 b
  · exact polyLiftFree11_5 b
  · exact polyLiftFree11_6 b
  · exact polyLiftFree11_7 b
  · exact polyLiftFree11_8 b
  · exact polyLiftFree11_9 b
  · exact polyLiftFree11_10 b
  · exact polyLiftFree11_11 b
  · exact polyLiftFree11_12 b
  · exact polyLiftFree11_13 b
  · exact polyLiftFree11_14 b
  · exact polyLiftFree11_15 b
  · exact polyLiftFree11_16 b
  · exact polyLiftFree11_17 b
  · exact polyLiftFree11_18 b
  · exact polyLiftFree11_19 b
  · exact polyLiftFree11_20 b
  · exact polyLiftFree11_21 b
  · exact polyLiftFree11_22 b
  · exact polyLiftFree11_23 b
  · exact polyLiftFree11_24 b
  · exact polyLiftFree11_25 b
  · exact polyLiftFree11_26 b
  · exact polyLiftFree11_27 b
  · exact polyLiftFree11_28 b
  · exact polyLiftFree11_29 b
  · exact polyLiftFree11_30 b
  · exact polyLiftFree11_31 b
  · exact polyLiftFree11_32 b
  · exact polyLiftFree11_33 b
  · exact polyLiftFree11_34 b
  · exact polyLiftFree11_35 b
  · exact polyLiftFree11_36 b
  · exact polyLiftFree11_37 b
  · exact polyLiftFree11_38 b
  · exact polyLiftFree11_39 b
  · exact polyLiftFree11_40 b
  · exact polyLiftFree11_41 b
  · exact polyLiftFree11_42 b
  · exact polyLiftFree11_43 b
  · exact polyLiftFree11_44 b
  · exact polyLiftFree11_45 b
  · exact polyLiftFree11_46 b
end UniserialComputations.N6
