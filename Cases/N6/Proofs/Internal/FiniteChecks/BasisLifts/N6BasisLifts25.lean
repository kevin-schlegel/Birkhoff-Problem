import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift25_0 (b : Fin 3) : PolyHom 25 0 :=
  ![PolyHom.zero 25 0,PolyHom.zero 25 0,PolyHom.zero 25 0] b
theorem polyLiftFree25_0 : ∀ b : Fin 3, (polyLift25_0 b).freeBlock=basisInt (homKind 25 0) b := by decide
def polyLift25_1 (b : Fin 3) : PolyHom 25 1 :=
  ![PolyHom.zero 25 1,PolyHom.zero 25 1,PolyHom.zero 25 1] b
theorem polyLiftFree25_1 : ∀ b : Fin 3, (polyLift25_1 b).freeBlock=basisInt (homKind 25 1) b := by decide
def polyLift25_2 (b : Fin 3) : PolyHom 25 2 :=
  ![PolyHom.zero 25 2,PolyHom.zero 25 2,PolyHom.zero 25 2] b
theorem polyLiftFree25_2 : ∀ b : Fin 3, (polyLift25_2 b).freeBlock=basisInt (homKind 25 2) b := by decide
def polyLift25_3 (b : Fin 3) : PolyHom 25 3 :=
  ![PolyHom.zero 25 3,PolyHom.zero 25 3,PolyHom.zero 25 3] b
theorem polyLiftFree25_3 : ∀ b : Fin 3, (polyLift25_3 b).freeBlock=basisInt (homKind 25 3) b := by decide
def polyLift25_4 (b : Fin 3) : PolyHom 25 4 :=
  ![PolyHom.zero 25 4,PolyHom.zero 25 4,PolyHom.zero 25 4] b
theorem polyLiftFree25_4 : ∀ b : Fin 3, (polyLift25_4 b).freeBlock=basisInt (homKind 25 4) b := by decide
def polyLift25_5 (b : Fin 3) : PolyHom 25 5 :=
  ![PolyHom.zero 25 5,PolyHom.zero 25 5,PolyHom.zero 25 5] b
theorem polyLiftFree25_5 : ∀ b : Fin 3, (polyLift25_5 b).freeBlock=basisInt (homKind 25 5) b := by decide
def polyLift25_6 (b : Fin 3) : PolyHom 25 6 :=
  ![PolyHom.zero 25 6,PolyHom.zero 25 6,PolyHom.zero 25 6] b
theorem polyLiftFree25_6 : ∀ b : Fin 3, (polyLift25_6 b).freeBlock=basisInt (homKind 25 6) b := by decide
def polyLift25_7 (b : Fin 3) : PolyHom 25 7 :=
  ![PolyHom.zero 25 7,PolyHom.zero 25 7,PolyHom.zero 25 7] b
theorem polyLiftFree25_7 : ∀ b : Fin 3, (polyLift25_7 b).freeBlock=basisInt (homKind 25 7) b := by decide
def polyLift25_8 (b : Fin 3) : PolyHom 25 8 :=
  ![PolyHom.zero 25 8,PolyHom.zero 25 8,PolyHom.zero 25 8] b
theorem polyLiftFree25_8 : ∀ b : Fin 3, (polyLift25_8 b).freeBlock=basisInt (homKind 25 8) b := by decide
def polyLift25_9 (b : Fin 3) : PolyHom 25 9 :=
  ![PolyHom.zero 25 9,PolyHom.zero 25 9,PolyHom.zero 25 9] b
theorem polyLiftFree25_9 : ∀ b : Fin 3, (polyLift25_9 b).freeBlock=basisInt (homKind 25 9) b := by decide
def polyRep25_10_0 : PolyHom 25 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift25_10 (b : Fin 3) : PolyHom 25 10 :=
  ![polyRep25_10_0,PolyHom.zero 25 10,PolyHom.zero 25 10] b
theorem polyLiftFree25_10 : ∀ b : Fin 3, (polyLift25_10 b).freeBlock=basisInt (homKind 25 10) b := by decide
def polyRep25_11_0 : PolyHom 25 11 where
  M := !![(mono6 (1) 2),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift25_11 (b : Fin 3) : PolyHom 25 11 :=
  ![polyRep25_11_0,PolyHom.zero 25 11,PolyHom.zero 25 11] b
theorem polyLiftFree25_11 : ∀ b : Fin 3, (polyLift25_11 b).freeBlock=basisInt (homKind 25 11) b := by decide
def polyLift25_12 (b : Fin 3) : PolyHom 25 12 :=
  ![PolyHom.zero 25 12,PolyHom.zero 25 12,PolyHom.zero 25 12] b
theorem polyLiftFree25_12 : ∀ b : Fin 3, (polyLift25_12 b).freeBlock=basisInt (homKind 25 12) b := by decide
def polyLift25_13 (b : Fin 3) : PolyHom 25 13 :=
  ![PolyHom.zero 25 13,PolyHom.zero 25 13,PolyHom.zero 25 13] b
theorem polyLiftFree25_13 : ∀ b : Fin 3, (polyLift25_13 b).freeBlock=basisInt (homKind 25 13) b := by decide
def polyLift25_14 (b : Fin 3) : PolyHom 25 14 :=
  ![PolyHom.zero 25 14,PolyHom.zero 25 14,PolyHom.zero 25 14] b
theorem polyLiftFree25_14 : ∀ b : Fin 3, (polyLift25_14 b).freeBlock=basisInt (homKind 25 14) b := by decide
def polyLift25_15 (b : Fin 3) : PolyHom 25 15 :=
  ![PolyHom.zero 25 15,PolyHom.zero 25 15,PolyHom.zero 25 15] b
theorem polyLiftFree25_15 : ∀ b : Fin 3, (polyLift25_15 b).freeBlock=basisInt (homKind 25 15) b := by decide
def polyLift25_16 (b : Fin 3) : PolyHom 25 16 :=
  ![PolyHom.zero 25 16,PolyHom.zero 25 16,PolyHom.zero 25 16] b
theorem polyLiftFree25_16 : ∀ b : Fin 3, (polyLift25_16 b).freeBlock=basisInt (homKind 25 16) b := by decide
def polyLift25_17 (b : Fin 3) : PolyHom 25 17 :=
  ![PolyHom.zero 25 17,PolyHom.zero 25 17,PolyHom.zero 25 17] b
theorem polyLiftFree25_17 : ∀ b : Fin 3, (polyLift25_17 b).freeBlock=basisInt (homKind 25 17) b := by decide
def polyLift25_18 (b : Fin 3) : PolyHom 25 18 :=
  ![PolyHom.zero 25 18,PolyHom.zero 25 18,PolyHom.zero 25 18] b
theorem polyLiftFree25_18 : ∀ b : Fin 3, (polyLift25_18 b).freeBlock=basisInt (homKind 25 18) b := by decide
def polyLift25_19 (b : Fin 3) : PolyHom 25 19 :=
  ![PolyHom.zero 25 19,PolyHom.zero 25 19,PolyHom.zero 25 19] b
theorem polyLiftFree25_19 : ∀ b : Fin 3, (polyLift25_19 b).freeBlock=basisInt (homKind 25 19) b := by decide
def polyLift25_20 (b : Fin 3) : PolyHom 25 20 :=
  ![PolyHom.zero 25 20,PolyHom.zero 25 20,PolyHom.zero 25 20] b
theorem polyLiftFree25_20 : ∀ b : Fin 3, (polyLift25_20 b).freeBlock=basisInt (homKind 25 20) b := by decide
def polyRep25_21_0 : PolyHom 25 21 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift25_21 (b : Fin 3) : PolyHom 25 21 :=
  ![polyRep25_21_0,PolyHom.zero 25 21,PolyHom.zero 25 21] b
theorem polyLiftFree25_21 : ∀ b : Fin 3, (polyLift25_21 b).freeBlock=basisInt (homKind 25 21) b := by decide
def polyLift25_22 (b : Fin 3) : PolyHom 25 22 :=
  ![PolyHom.zero 25 22,PolyHom.zero 25 22,PolyHom.zero 25 22] b
theorem polyLiftFree25_22 : ∀ b : Fin 3, (polyLift25_22 b).freeBlock=basisInt (homKind 25 22) b := by decide
def polyLift25_23 (b : Fin 3) : PolyHom 25 23 :=
  ![PolyHom.zero 25 23,PolyHom.zero 25 23,PolyHom.zero 25 23] b
theorem polyLiftFree25_23 : ∀ b : Fin 3, (polyLift25_23 b).freeBlock=basisInt (homKind 25 23) b := by decide
def polyRep25_24_0 : PolyHom 25 24 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift25_24 (b : Fin 3) : PolyHom 25 24 :=
  ![polyRep25_24_0,PolyHom.zero 25 24,PolyHom.zero 25 24] b
theorem polyLiftFree25_24 : ∀ b : Fin 3, (polyLift25_24 b).freeBlock=basisInt (homKind 25 24) b := by decide
def polyRep25_25_0 : PolyHom 25 25 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift25_25 (b : Fin 3) : PolyHom 25 25 :=
  ![polyRep25_25_0,PolyHom.zero 25 25,PolyHom.zero 25 25] b
theorem polyLiftFree25_25 : ∀ b : Fin 3, (polyLift25_25 b).freeBlock=basisInt (homKind 25 25) b := by decide
def polyLift25_26 (b : Fin 3) : PolyHom 25 26 :=
  ![PolyHom.zero 25 26,PolyHom.zero 25 26,PolyHom.zero 25 26] b
theorem polyLiftFree25_26 : ∀ b : Fin 3, (polyLift25_26 b).freeBlock=basisInt (homKind 25 26) b := by decide
def polyLift25_27 (b : Fin 3) : PolyHom 25 27 :=
  ![PolyHom.zero 25 27,PolyHom.zero 25 27,PolyHom.zero 25 27] b
theorem polyLiftFree25_27 : ∀ b : Fin 3, (polyLift25_27 b).freeBlock=basisInt (homKind 25 27) b := by decide
def polyLift25_28 (b : Fin 3) : PolyHom 25 28 :=
  ![PolyHom.zero 25 28,PolyHom.zero 25 28,PolyHom.zero 25 28] b
theorem polyLiftFree25_28 : ∀ b : Fin 3, (polyLift25_28 b).freeBlock=basisInt (homKind 25 28) b := by decide
def polyLift25_29 (b : Fin 3) : PolyHom 25 29 :=
  ![PolyHom.zero 25 29,PolyHom.zero 25 29,PolyHom.zero 25 29] b
theorem polyLiftFree25_29 : ∀ b : Fin 3, (polyLift25_29 b).freeBlock=basisInt (homKind 25 29) b := by decide
def polyLift25_30 (b : Fin 3) : PolyHom 25 30 :=
  ![PolyHom.zero 25 30,PolyHom.zero 25 30,PolyHom.zero 25 30] b
theorem polyLiftFree25_30 : ∀ b : Fin 3, (polyLift25_30 b).freeBlock=basisInt (homKind 25 30) b := by decide
def polyLift25_31 (b : Fin 3) : PolyHom 25 31 :=
  ![PolyHom.zero 25 31,PolyHom.zero 25 31,PolyHom.zero 25 31] b
theorem polyLiftFree25_31 : ∀ b : Fin 3, (polyLift25_31 b).freeBlock=basisInt (homKind 25 31) b := by decide
def polyLift25_32 (b : Fin 3) : PolyHom 25 32 :=
  ![PolyHom.zero 25 32,PolyHom.zero 25 32,PolyHom.zero 25 32] b
theorem polyLiftFree25_32 : ∀ b : Fin 3, (polyLift25_32 b).freeBlock=basisInt (homKind 25 32) b := by decide
def polyLift25_33 (b : Fin 3) : PolyHom 25 33 :=
  ![PolyHom.zero 25 33,PolyHom.zero 25 33,PolyHom.zero 25 33] b
theorem polyLiftFree25_33 : ∀ b : Fin 3, (polyLift25_33 b).freeBlock=basisInt (homKind 25 33) b := by decide
def polyLift25_34 (b : Fin 3) : PolyHom 25 34 :=
  ![PolyHom.zero 25 34,PolyHom.zero 25 34,PolyHom.zero 25 34] b
theorem polyLiftFree25_34 : ∀ b : Fin 3, (polyLift25_34 b).freeBlock=basisInt (homKind 25 34) b := by decide
def polyLift25_35 (b : Fin 3) : PolyHom 25 35 :=
  ![PolyHom.zero 25 35,PolyHom.zero 25 35,PolyHom.zero 25 35] b
theorem polyLiftFree25_35 : ∀ b : Fin 3, (polyLift25_35 b).freeBlock=basisInt (homKind 25 35) b := by decide
def polyLift25_36 (b : Fin 3) : PolyHom 25 36 :=
  ![PolyHom.zero 25 36,PolyHom.zero 25 36,PolyHom.zero 25 36] b
theorem polyLiftFree25_36 : ∀ b : Fin 3, (polyLift25_36 b).freeBlock=basisInt (homKind 25 36) b := by decide
def polyLift25_37 (b : Fin 3) : PolyHom 25 37 :=
  ![PolyHom.zero 25 37,PolyHom.zero 25 37,PolyHom.zero 25 37] b
theorem polyLiftFree25_37 : ∀ b : Fin 3, (polyLift25_37 b).freeBlock=basisInt (homKind 25 37) b := by decide
def polyLift25_38 (b : Fin 3) : PolyHom 25 38 :=
  ![PolyHom.zero 25 38,PolyHom.zero 25 38,PolyHom.zero 25 38] b
theorem polyLiftFree25_38 : ∀ b : Fin 3, (polyLift25_38 b).freeBlock=basisInt (homKind 25 38) b := by decide
def polyLift25_39 (b : Fin 3) : PolyHom 25 39 :=
  ![PolyHom.zero 25 39,PolyHom.zero 25 39,PolyHom.zero 25 39] b
theorem polyLiftFree25_39 : ∀ b : Fin 3, (polyLift25_39 b).freeBlock=basisInt (homKind 25 39) b := by decide
def polyLift25_40 (b : Fin 3) : PolyHom 25 40 :=
  ![PolyHom.zero 25 40,PolyHom.zero 25 40,PolyHom.zero 25 40] b
theorem polyLiftFree25_40 : ∀ b : Fin 3, (polyLift25_40 b).freeBlock=basisInt (homKind 25 40) b := by decide
def polyLift25_41 (b : Fin 3) : PolyHom 25 41 :=
  ![PolyHom.zero 25 41,PolyHom.zero 25 41,PolyHom.zero 25 41] b
theorem polyLiftFree25_41 : ∀ b : Fin 3, (polyLift25_41 b).freeBlock=basisInt (homKind 25 41) b := by decide
def polyRep25_42_0 : PolyHom 25 42 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift25_42 (b : Fin 3) : PolyHom 25 42 :=
  ![polyRep25_42_0,PolyHom.zero 25 42,PolyHom.zero 25 42] b
theorem polyLiftFree25_42 : ∀ b : Fin 3, (polyLift25_42 b).freeBlock=basisInt (homKind 25 42) b := by decide
def polyLift25_43 (b : Fin 3) : PolyHom 25 43 :=
  ![PolyHom.zero 25 43,PolyHom.zero 25 43,PolyHom.zero 25 43] b
theorem polyLiftFree25_43 : ∀ b : Fin 3, (polyLift25_43 b).freeBlock=basisInt (homKind 25 43) b := by decide
def polyRep25_44_0 : PolyHom 25 44 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift25_44 (b : Fin 3) : PolyHom 25 44 :=
  ![polyRep25_44_0,PolyHom.zero 25 44,PolyHom.zero 25 44] b
theorem polyLiftFree25_44 : ∀ b : Fin 3, (polyLift25_44 b).freeBlock=basisInt (homKind 25 44) b := by decide
def polyRep25_45_0 : PolyHom 25 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift25_45 (b : Fin 3) : PolyHom 25 45 :=
  ![polyRep25_45_0,PolyHom.zero 25 45,PolyHom.zero 25 45] b
theorem polyLiftFree25_45 : ∀ b : Fin 3, (polyLift25_45 b).freeBlock=basisInt (homKind 25 45) b := by decide
def polyLift25_46 (b : Fin 3) : PolyHom 25 46 :=
  ![PolyHom.zero 25 46,PolyHom.zero 25 46,PolyHom.zero 25 46] b
theorem polyLiftFree25_46 : ∀ b : Fin 3, (polyLift25_46 b).freeBlock=basisInt (homKind 25 46) b := by decide
def polyLiftRow25 (j : Fin 47) (b : Fin 3) : PolyHom 25 j :=
  match j with
  | ⟨0,_⟩ => polyLift25_0 b
  | ⟨1,_⟩ => polyLift25_1 b
  | ⟨2,_⟩ => polyLift25_2 b
  | ⟨3,_⟩ => polyLift25_3 b
  | ⟨4,_⟩ => polyLift25_4 b
  | ⟨5,_⟩ => polyLift25_5 b
  | ⟨6,_⟩ => polyLift25_6 b
  | ⟨7,_⟩ => polyLift25_7 b
  | ⟨8,_⟩ => polyLift25_8 b
  | ⟨9,_⟩ => polyLift25_9 b
  | ⟨10,_⟩ => polyLift25_10 b
  | ⟨11,_⟩ => polyLift25_11 b
  | ⟨12,_⟩ => polyLift25_12 b
  | ⟨13,_⟩ => polyLift25_13 b
  | ⟨14,_⟩ => polyLift25_14 b
  | ⟨15,_⟩ => polyLift25_15 b
  | ⟨16,_⟩ => polyLift25_16 b
  | ⟨17,_⟩ => polyLift25_17 b
  | ⟨18,_⟩ => polyLift25_18 b
  | ⟨19,_⟩ => polyLift25_19 b
  | ⟨20,_⟩ => polyLift25_20 b
  | ⟨21,_⟩ => polyLift25_21 b
  | ⟨22,_⟩ => polyLift25_22 b
  | ⟨23,_⟩ => polyLift25_23 b
  | ⟨24,_⟩ => polyLift25_24 b
  | ⟨25,_⟩ => polyLift25_25 b
  | ⟨26,_⟩ => polyLift25_26 b
  | ⟨27,_⟩ => polyLift25_27 b
  | ⟨28,_⟩ => polyLift25_28 b
  | ⟨29,_⟩ => polyLift25_29 b
  | ⟨30,_⟩ => polyLift25_30 b
  | ⟨31,_⟩ => polyLift25_31 b
  | ⟨32,_⟩ => polyLift25_32 b
  | ⟨33,_⟩ => polyLift25_33 b
  | ⟨34,_⟩ => polyLift25_34 b
  | ⟨35,_⟩ => polyLift25_35 b
  | ⟨36,_⟩ => polyLift25_36 b
  | ⟨37,_⟩ => polyLift25_37 b
  | ⟨38,_⟩ => polyLift25_38 b
  | ⟨39,_⟩ => polyLift25_39 b
  | ⟨40,_⟩ => polyLift25_40 b
  | ⟨41,_⟩ => polyLift25_41 b
  | ⟨42,_⟩ => polyLift25_42 b
  | ⟨43,_⟩ => polyLift25_43 b
  | ⟨44,_⟩ => polyLift25_44 b
  | ⟨45,_⟩ => polyLift25_45 b
  | ⟨46,_⟩ => polyLift25_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree25 (j : Fin 47) (b : Fin 3) : (polyLiftRow25 j b).freeBlock=basisInt (homKind 25 j) b := by
  fin_cases j
  · exact polyLiftFree25_0 b
  · exact polyLiftFree25_1 b
  · exact polyLiftFree25_2 b
  · exact polyLiftFree25_3 b
  · exact polyLiftFree25_4 b
  · exact polyLiftFree25_5 b
  · exact polyLiftFree25_6 b
  · exact polyLiftFree25_7 b
  · exact polyLiftFree25_8 b
  · exact polyLiftFree25_9 b
  · exact polyLiftFree25_10 b
  · exact polyLiftFree25_11 b
  · exact polyLiftFree25_12 b
  · exact polyLiftFree25_13 b
  · exact polyLiftFree25_14 b
  · exact polyLiftFree25_15 b
  · exact polyLiftFree25_16 b
  · exact polyLiftFree25_17 b
  · exact polyLiftFree25_18 b
  · exact polyLiftFree25_19 b
  · exact polyLiftFree25_20 b
  · exact polyLiftFree25_21 b
  · exact polyLiftFree25_22 b
  · exact polyLiftFree25_23 b
  · exact polyLiftFree25_24 b
  · exact polyLiftFree25_25 b
  · exact polyLiftFree25_26 b
  · exact polyLiftFree25_27 b
  · exact polyLiftFree25_28 b
  · exact polyLiftFree25_29 b
  · exact polyLiftFree25_30 b
  · exact polyLiftFree25_31 b
  · exact polyLiftFree25_32 b
  · exact polyLiftFree25_33 b
  · exact polyLiftFree25_34 b
  · exact polyLiftFree25_35 b
  · exact polyLiftFree25_36 b
  · exact polyLiftFree25_37 b
  · exact polyLiftFree25_38 b
  · exact polyLiftFree25_39 b
  · exact polyLiftFree25_40 b
  · exact polyLiftFree25_41 b
  · exact polyLiftFree25_42 b
  · exact polyLiftFree25_43 b
  · exact polyLiftFree25_44 b
  · exact polyLiftFree25_45 b
  · exact polyLiftFree25_46 b
end UniserialComputations.N6
