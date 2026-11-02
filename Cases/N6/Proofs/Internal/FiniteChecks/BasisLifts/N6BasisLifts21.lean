import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift21_0 (b : Fin 3) : PolyHom 21 0 :=
  ![PolyHom.zero 21 0,PolyHom.zero 21 0,PolyHom.zero 21 0] b
theorem polyLiftFree21_0 : ∀ b : Fin 3, (polyLift21_0 b).freeBlock=basisInt (homKind 21 0) b := by decide
def polyLift21_1 (b : Fin 3) : PolyHom 21 1 :=
  ![PolyHom.zero 21 1,PolyHom.zero 21 1,PolyHom.zero 21 1] b
theorem polyLiftFree21_1 : ∀ b : Fin 3, (polyLift21_1 b).freeBlock=basisInt (homKind 21 1) b := by decide
def polyLift21_2 (b : Fin 3) : PolyHom 21 2 :=
  ![PolyHom.zero 21 2,PolyHom.zero 21 2,PolyHom.zero 21 2] b
theorem polyLiftFree21_2 : ∀ b : Fin 3, (polyLift21_2 b).freeBlock=basisInt (homKind 21 2) b := by decide
def polyLift21_3 (b : Fin 3) : PolyHom 21 3 :=
  ![PolyHom.zero 21 3,PolyHom.zero 21 3,PolyHom.zero 21 3] b
theorem polyLiftFree21_3 : ∀ b : Fin 3, (polyLift21_3 b).freeBlock=basisInt (homKind 21 3) b := by decide
def polyLift21_4 (b : Fin 3) : PolyHom 21 4 :=
  ![PolyHom.zero 21 4,PolyHom.zero 21 4,PolyHom.zero 21 4] b
theorem polyLiftFree21_4 : ∀ b : Fin 3, (polyLift21_4 b).freeBlock=basisInt (homKind 21 4) b := by decide
def polyLift21_5 (b : Fin 3) : PolyHom 21 5 :=
  ![PolyHom.zero 21 5,PolyHom.zero 21 5,PolyHom.zero 21 5] b
theorem polyLiftFree21_5 : ∀ b : Fin 3, (polyLift21_5 b).freeBlock=basisInt (homKind 21 5) b := by decide
def polyLift21_6 (b : Fin 3) : PolyHom 21 6 :=
  ![PolyHom.zero 21 6,PolyHom.zero 21 6,PolyHom.zero 21 6] b
theorem polyLiftFree21_6 : ∀ b : Fin 3, (polyLift21_6 b).freeBlock=basisInt (homKind 21 6) b := by decide
def polyLift21_7 (b : Fin 3) : PolyHom 21 7 :=
  ![PolyHom.zero 21 7,PolyHom.zero 21 7,PolyHom.zero 21 7] b
theorem polyLiftFree21_7 : ∀ b : Fin 3, (polyLift21_7 b).freeBlock=basisInt (homKind 21 7) b := by decide
def polyLift21_8 (b : Fin 3) : PolyHom 21 8 :=
  ![PolyHom.zero 21 8,PolyHom.zero 21 8,PolyHom.zero 21 8] b
theorem polyLiftFree21_8 : ∀ b : Fin 3, (polyLift21_8 b).freeBlock=basisInt (homKind 21 8) b := by decide
def polyLift21_9 (b : Fin 3) : PolyHom 21 9 :=
  ![PolyHom.zero 21 9,PolyHom.zero 21 9,PolyHom.zero 21 9] b
theorem polyLiftFree21_9 : ∀ b : Fin 3, (polyLift21_9 b).freeBlock=basisInt (homKind 21 9) b := by decide
def polyRep21_10_0 : PolyHom 21 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift21_10 (b : Fin 3) : PolyHom 21 10 :=
  ![polyRep21_10_0,PolyHom.zero 21 10,PolyHom.zero 21 10] b
theorem polyLiftFree21_10 : ∀ b : Fin 3, (polyLift21_10 b).freeBlock=basisInt (homKind 21 10) b := by decide
def polyRep21_11_0 : PolyHom 21 11 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift21_11 (b : Fin 3) : PolyHom 21 11 :=
  ![polyRep21_11_0,PolyHom.zero 21 11,PolyHom.zero 21 11] b
theorem polyLiftFree21_11 : ∀ b : Fin 3, (polyLift21_11 b).freeBlock=basisInt (homKind 21 11) b := by decide
def polyLift21_12 (b : Fin 3) : PolyHom 21 12 :=
  ![PolyHom.zero 21 12,PolyHom.zero 21 12,PolyHom.zero 21 12] b
theorem polyLiftFree21_12 : ∀ b : Fin 3, (polyLift21_12 b).freeBlock=basisInt (homKind 21 12) b := by decide
def polyLift21_13 (b : Fin 3) : PolyHom 21 13 :=
  ![PolyHom.zero 21 13,PolyHom.zero 21 13,PolyHom.zero 21 13] b
theorem polyLiftFree21_13 : ∀ b : Fin 3, (polyLift21_13 b).freeBlock=basisInt (homKind 21 13) b := by decide
def polyLift21_14 (b : Fin 3) : PolyHom 21 14 :=
  ![PolyHom.zero 21 14,PolyHom.zero 21 14,PolyHom.zero 21 14] b
theorem polyLiftFree21_14 : ∀ b : Fin 3, (polyLift21_14 b).freeBlock=basisInt (homKind 21 14) b := by decide
def polyLift21_15 (b : Fin 3) : PolyHom 21 15 :=
  ![PolyHom.zero 21 15,PolyHom.zero 21 15,PolyHom.zero 21 15] b
theorem polyLiftFree21_15 : ∀ b : Fin 3, (polyLift21_15 b).freeBlock=basisInt (homKind 21 15) b := by decide
def polyLift21_16 (b : Fin 3) : PolyHom 21 16 :=
  ![PolyHom.zero 21 16,PolyHom.zero 21 16,PolyHom.zero 21 16] b
theorem polyLiftFree21_16 : ∀ b : Fin 3, (polyLift21_16 b).freeBlock=basisInt (homKind 21 16) b := by decide
def polyLift21_17 (b : Fin 3) : PolyHom 21 17 :=
  ![PolyHom.zero 21 17,PolyHom.zero 21 17,PolyHom.zero 21 17] b
theorem polyLiftFree21_17 : ∀ b : Fin 3, (polyLift21_17 b).freeBlock=basisInt (homKind 21 17) b := by decide
def polyLift21_18 (b : Fin 3) : PolyHom 21 18 :=
  ![PolyHom.zero 21 18,PolyHom.zero 21 18,PolyHom.zero 21 18] b
theorem polyLiftFree21_18 : ∀ b : Fin 3, (polyLift21_18 b).freeBlock=basisInt (homKind 21 18) b := by decide
def polyLift21_19 (b : Fin 3) : PolyHom 21 19 :=
  ![PolyHom.zero 21 19,PolyHom.zero 21 19,PolyHom.zero 21 19] b
theorem polyLiftFree21_19 : ∀ b : Fin 3, (polyLift21_19 b).freeBlock=basisInt (homKind 21 19) b := by decide
def polyLift21_20 (b : Fin 3) : PolyHom 21 20 :=
  ![PolyHom.zero 21 20,PolyHom.zero 21 20,PolyHom.zero 21 20] b
theorem polyLiftFree21_20 : ∀ b : Fin 3, (polyLift21_20 b).freeBlock=basisInt (homKind 21 20) b := by decide
def polyRep21_21_0 : PolyHom 21 21 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift21_21 (b : Fin 3) : PolyHom 21 21 :=
  ![polyRep21_21_0,PolyHom.zero 21 21,PolyHom.zero 21 21] b
theorem polyLiftFree21_21 : ∀ b : Fin 3, (polyLift21_21 b).freeBlock=basisInt (homKind 21 21) b := by decide
def polyLift21_22 (b : Fin 3) : PolyHom 21 22 :=
  ![PolyHom.zero 21 22,PolyHom.zero 21 22,PolyHom.zero 21 22] b
theorem polyLiftFree21_22 : ∀ b : Fin 3, (polyLift21_22 b).freeBlock=basisInt (homKind 21 22) b := by decide
def polyLift21_23 (b : Fin 3) : PolyHom 21 23 :=
  ![PolyHom.zero 21 23,PolyHom.zero 21 23,PolyHom.zero 21 23] b
theorem polyLiftFree21_23 : ∀ b : Fin 3, (polyLift21_23 b).freeBlock=basisInt (homKind 21 23) b := by decide
def polyLift21_24 (b : Fin 3) : PolyHom 21 24 :=
  ![PolyHom.zero 21 24,PolyHom.zero 21 24,PolyHom.zero 21 24] b
theorem polyLiftFree21_24 : ∀ b : Fin 3, (polyLift21_24 b).freeBlock=basisInt (homKind 21 24) b := by decide
def polyLift21_25 (b : Fin 3) : PolyHom 21 25 :=
  ![PolyHom.zero 21 25,PolyHom.zero 21 25,PolyHom.zero 21 25] b
theorem polyLiftFree21_25 : ∀ b : Fin 3, (polyLift21_25 b).freeBlock=basisInt (homKind 21 25) b := by decide
def polyLift21_26 (b : Fin 3) : PolyHom 21 26 :=
  ![PolyHom.zero 21 26,PolyHom.zero 21 26,PolyHom.zero 21 26] b
theorem polyLiftFree21_26 : ∀ b : Fin 3, (polyLift21_26 b).freeBlock=basisInt (homKind 21 26) b := by decide
def polyLift21_27 (b : Fin 3) : PolyHom 21 27 :=
  ![PolyHom.zero 21 27,PolyHom.zero 21 27,PolyHom.zero 21 27] b
theorem polyLiftFree21_27 : ∀ b : Fin 3, (polyLift21_27 b).freeBlock=basisInt (homKind 21 27) b := by decide
def polyLift21_28 (b : Fin 3) : PolyHom 21 28 :=
  ![PolyHom.zero 21 28,PolyHom.zero 21 28,PolyHom.zero 21 28] b
theorem polyLiftFree21_28 : ∀ b : Fin 3, (polyLift21_28 b).freeBlock=basisInt (homKind 21 28) b := by decide
def polyLift21_29 (b : Fin 3) : PolyHom 21 29 :=
  ![PolyHom.zero 21 29,PolyHom.zero 21 29,PolyHom.zero 21 29] b
theorem polyLiftFree21_29 : ∀ b : Fin 3, (polyLift21_29 b).freeBlock=basisInt (homKind 21 29) b := by decide
def polyLift21_30 (b : Fin 3) : PolyHom 21 30 :=
  ![PolyHom.zero 21 30,PolyHom.zero 21 30,PolyHom.zero 21 30] b
theorem polyLiftFree21_30 : ∀ b : Fin 3, (polyLift21_30 b).freeBlock=basisInt (homKind 21 30) b := by decide
def polyLift21_31 (b : Fin 3) : PolyHom 21 31 :=
  ![PolyHom.zero 21 31,PolyHom.zero 21 31,PolyHom.zero 21 31] b
theorem polyLiftFree21_31 : ∀ b : Fin 3, (polyLift21_31 b).freeBlock=basisInt (homKind 21 31) b := by decide
def polyLift21_32 (b : Fin 3) : PolyHom 21 32 :=
  ![PolyHom.zero 21 32,PolyHom.zero 21 32,PolyHom.zero 21 32] b
theorem polyLiftFree21_32 : ∀ b : Fin 3, (polyLift21_32 b).freeBlock=basisInt (homKind 21 32) b := by decide
def polyLift21_33 (b : Fin 3) : PolyHom 21 33 :=
  ![PolyHom.zero 21 33,PolyHom.zero 21 33,PolyHom.zero 21 33] b
theorem polyLiftFree21_33 : ∀ b : Fin 3, (polyLift21_33 b).freeBlock=basisInt (homKind 21 33) b := by decide
def polyLift21_34 (b : Fin 3) : PolyHom 21 34 :=
  ![PolyHom.zero 21 34,PolyHom.zero 21 34,PolyHom.zero 21 34] b
theorem polyLiftFree21_34 : ∀ b : Fin 3, (polyLift21_34 b).freeBlock=basisInt (homKind 21 34) b := by decide
def polyLift21_35 (b : Fin 3) : PolyHom 21 35 :=
  ![PolyHom.zero 21 35,PolyHom.zero 21 35,PolyHom.zero 21 35] b
theorem polyLiftFree21_35 : ∀ b : Fin 3, (polyLift21_35 b).freeBlock=basisInt (homKind 21 35) b := by decide
def polyLift21_36 (b : Fin 3) : PolyHom 21 36 :=
  ![PolyHom.zero 21 36,PolyHom.zero 21 36,PolyHom.zero 21 36] b
theorem polyLiftFree21_36 : ∀ b : Fin 3, (polyLift21_36 b).freeBlock=basisInt (homKind 21 36) b := by decide
def polyLift21_37 (b : Fin 3) : PolyHom 21 37 :=
  ![PolyHom.zero 21 37,PolyHom.zero 21 37,PolyHom.zero 21 37] b
theorem polyLiftFree21_37 : ∀ b : Fin 3, (polyLift21_37 b).freeBlock=basisInt (homKind 21 37) b := by decide
def polyLift21_38 (b : Fin 3) : PolyHom 21 38 :=
  ![PolyHom.zero 21 38,PolyHom.zero 21 38,PolyHom.zero 21 38] b
theorem polyLiftFree21_38 : ∀ b : Fin 3, (polyLift21_38 b).freeBlock=basisInt (homKind 21 38) b := by decide
def polyLift21_39 (b : Fin 3) : PolyHom 21 39 :=
  ![PolyHom.zero 21 39,PolyHom.zero 21 39,PolyHom.zero 21 39] b
theorem polyLiftFree21_39 : ∀ b : Fin 3, (polyLift21_39 b).freeBlock=basisInt (homKind 21 39) b := by decide
def polyLift21_40 (b : Fin 3) : PolyHom 21 40 :=
  ![PolyHom.zero 21 40,PolyHom.zero 21 40,PolyHom.zero 21 40] b
theorem polyLiftFree21_40 : ∀ b : Fin 3, (polyLift21_40 b).freeBlock=basisInt (homKind 21 40) b := by decide
def polyLift21_41 (b : Fin 3) : PolyHom 21 41 :=
  ![PolyHom.zero 21 41,PolyHom.zero 21 41,PolyHom.zero 21 41] b
theorem polyLiftFree21_41 : ∀ b : Fin 3, (polyLift21_41 b).freeBlock=basisInt (homKind 21 41) b := by decide
def polyLift21_42 (b : Fin 3) : PolyHom 21 42 :=
  ![PolyHom.zero 21 42,PolyHom.zero 21 42,PolyHom.zero 21 42] b
theorem polyLiftFree21_42 : ∀ b : Fin 3, (polyLift21_42 b).freeBlock=basisInt (homKind 21 42) b := by decide
def polyLift21_43 (b : Fin 3) : PolyHom 21 43 :=
  ![PolyHom.zero 21 43,PolyHom.zero 21 43,PolyHom.zero 21 43] b
theorem polyLiftFree21_43 : ∀ b : Fin 3, (polyLift21_43 b).freeBlock=basisInt (homKind 21 43) b := by decide
def polyLift21_44 (b : Fin 3) : PolyHom 21 44 :=
  ![PolyHom.zero 21 44,PolyHom.zero 21 44,PolyHom.zero 21 44] b
theorem polyLiftFree21_44 : ∀ b : Fin 3, (polyLift21_44 b).freeBlock=basisInt (homKind 21 44) b := by decide
def polyRep21_45_0 : PolyHom 21 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift21_45 (b : Fin 3) : PolyHom 21 45 :=
  ![polyRep21_45_0,PolyHom.zero 21 45,PolyHom.zero 21 45] b
theorem polyLiftFree21_45 : ∀ b : Fin 3, (polyLift21_45 b).freeBlock=basisInt (homKind 21 45) b := by decide
def polyLift21_46 (b : Fin 3) : PolyHom 21 46 :=
  ![PolyHom.zero 21 46,PolyHom.zero 21 46,PolyHom.zero 21 46] b
theorem polyLiftFree21_46 : ∀ b : Fin 3, (polyLift21_46 b).freeBlock=basisInt (homKind 21 46) b := by decide
def polyLiftRow21 (j : Fin 47) (b : Fin 3) : PolyHom 21 j :=
  match j with
  | ⟨0,_⟩ => polyLift21_0 b
  | ⟨1,_⟩ => polyLift21_1 b
  | ⟨2,_⟩ => polyLift21_2 b
  | ⟨3,_⟩ => polyLift21_3 b
  | ⟨4,_⟩ => polyLift21_4 b
  | ⟨5,_⟩ => polyLift21_5 b
  | ⟨6,_⟩ => polyLift21_6 b
  | ⟨7,_⟩ => polyLift21_7 b
  | ⟨8,_⟩ => polyLift21_8 b
  | ⟨9,_⟩ => polyLift21_9 b
  | ⟨10,_⟩ => polyLift21_10 b
  | ⟨11,_⟩ => polyLift21_11 b
  | ⟨12,_⟩ => polyLift21_12 b
  | ⟨13,_⟩ => polyLift21_13 b
  | ⟨14,_⟩ => polyLift21_14 b
  | ⟨15,_⟩ => polyLift21_15 b
  | ⟨16,_⟩ => polyLift21_16 b
  | ⟨17,_⟩ => polyLift21_17 b
  | ⟨18,_⟩ => polyLift21_18 b
  | ⟨19,_⟩ => polyLift21_19 b
  | ⟨20,_⟩ => polyLift21_20 b
  | ⟨21,_⟩ => polyLift21_21 b
  | ⟨22,_⟩ => polyLift21_22 b
  | ⟨23,_⟩ => polyLift21_23 b
  | ⟨24,_⟩ => polyLift21_24 b
  | ⟨25,_⟩ => polyLift21_25 b
  | ⟨26,_⟩ => polyLift21_26 b
  | ⟨27,_⟩ => polyLift21_27 b
  | ⟨28,_⟩ => polyLift21_28 b
  | ⟨29,_⟩ => polyLift21_29 b
  | ⟨30,_⟩ => polyLift21_30 b
  | ⟨31,_⟩ => polyLift21_31 b
  | ⟨32,_⟩ => polyLift21_32 b
  | ⟨33,_⟩ => polyLift21_33 b
  | ⟨34,_⟩ => polyLift21_34 b
  | ⟨35,_⟩ => polyLift21_35 b
  | ⟨36,_⟩ => polyLift21_36 b
  | ⟨37,_⟩ => polyLift21_37 b
  | ⟨38,_⟩ => polyLift21_38 b
  | ⟨39,_⟩ => polyLift21_39 b
  | ⟨40,_⟩ => polyLift21_40 b
  | ⟨41,_⟩ => polyLift21_41 b
  | ⟨42,_⟩ => polyLift21_42 b
  | ⟨43,_⟩ => polyLift21_43 b
  | ⟨44,_⟩ => polyLift21_44 b
  | ⟨45,_⟩ => polyLift21_45 b
  | ⟨46,_⟩ => polyLift21_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree21 (j : Fin 47) (b : Fin 3) : (polyLiftRow21 j b).freeBlock=basisInt (homKind 21 j) b := by
  fin_cases j
  · exact polyLiftFree21_0 b
  · exact polyLiftFree21_1 b
  · exact polyLiftFree21_2 b
  · exact polyLiftFree21_3 b
  · exact polyLiftFree21_4 b
  · exact polyLiftFree21_5 b
  · exact polyLiftFree21_6 b
  · exact polyLiftFree21_7 b
  · exact polyLiftFree21_8 b
  · exact polyLiftFree21_9 b
  · exact polyLiftFree21_10 b
  · exact polyLiftFree21_11 b
  · exact polyLiftFree21_12 b
  · exact polyLiftFree21_13 b
  · exact polyLiftFree21_14 b
  · exact polyLiftFree21_15 b
  · exact polyLiftFree21_16 b
  · exact polyLiftFree21_17 b
  · exact polyLiftFree21_18 b
  · exact polyLiftFree21_19 b
  · exact polyLiftFree21_20 b
  · exact polyLiftFree21_21 b
  · exact polyLiftFree21_22 b
  · exact polyLiftFree21_23 b
  · exact polyLiftFree21_24 b
  · exact polyLiftFree21_25 b
  · exact polyLiftFree21_26 b
  · exact polyLiftFree21_27 b
  · exact polyLiftFree21_28 b
  · exact polyLiftFree21_29 b
  · exact polyLiftFree21_30 b
  · exact polyLiftFree21_31 b
  · exact polyLiftFree21_32 b
  · exact polyLiftFree21_33 b
  · exact polyLiftFree21_34 b
  · exact polyLiftFree21_35 b
  · exact polyLiftFree21_36 b
  · exact polyLiftFree21_37 b
  · exact polyLiftFree21_38 b
  · exact polyLiftFree21_39 b
  · exact polyLiftFree21_40 b
  · exact polyLiftFree21_41 b
  · exact polyLiftFree21_42 b
  · exact polyLiftFree21_43 b
  · exact polyLiftFree21_44 b
  · exact polyLiftFree21_45 b
  · exact polyLiftFree21_46 b
end UniserialComputations.N6
