import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift33_0 (b : Fin 3) : PolyHom 33 0 :=
  ![PolyHom.zero 33 0,PolyHom.zero 33 0,PolyHom.zero 33 0] b
theorem polyLiftFree33_0 : ∀ b : Fin 3, (polyLift33_0 b).freeBlock=basisInt (homKind 33 0) b := by decide
def polyLift33_1 (b : Fin 3) : PolyHom 33 1 :=
  ![PolyHom.zero 33 1,PolyHom.zero 33 1,PolyHom.zero 33 1] b
theorem polyLiftFree33_1 : ∀ b : Fin 3, (polyLift33_1 b).freeBlock=basisInt (homKind 33 1) b := by decide
def polyLift33_2 (b : Fin 3) : PolyHom 33 2 :=
  ![PolyHom.zero 33 2,PolyHom.zero 33 2,PolyHom.zero 33 2] b
theorem polyLiftFree33_2 : ∀ b : Fin 3, (polyLift33_2 b).freeBlock=basisInt (homKind 33 2) b := by decide
def polyLift33_3 (b : Fin 3) : PolyHom 33 3 :=
  ![PolyHom.zero 33 3,PolyHom.zero 33 3,PolyHom.zero 33 3] b
theorem polyLiftFree33_3 : ∀ b : Fin 3, (polyLift33_3 b).freeBlock=basisInt (homKind 33 3) b := by decide
def polyLift33_4 (b : Fin 3) : PolyHom 33 4 :=
  ![PolyHom.zero 33 4,PolyHom.zero 33 4,PolyHom.zero 33 4] b
theorem polyLiftFree33_4 : ∀ b : Fin 3, (polyLift33_4 b).freeBlock=basisInt (homKind 33 4) b := by decide
def polyLift33_5 (b : Fin 3) : PolyHom 33 5 :=
  ![PolyHom.zero 33 5,PolyHom.zero 33 5,PolyHom.zero 33 5] b
theorem polyLiftFree33_5 : ∀ b : Fin 3, (polyLift33_5 b).freeBlock=basisInt (homKind 33 5) b := by decide
def polyLift33_6 (b : Fin 3) : PolyHom 33 6 :=
  ![PolyHom.zero 33 6,PolyHom.zero 33 6,PolyHom.zero 33 6] b
theorem polyLiftFree33_6 : ∀ b : Fin 3, (polyLift33_6 b).freeBlock=basisInt (homKind 33 6) b := by decide
def polyLift33_7 (b : Fin 3) : PolyHom 33 7 :=
  ![PolyHom.zero 33 7,PolyHom.zero 33 7,PolyHom.zero 33 7] b
theorem polyLiftFree33_7 : ∀ b : Fin 3, (polyLift33_7 b).freeBlock=basisInt (homKind 33 7) b := by decide
def polyLift33_8 (b : Fin 3) : PolyHom 33 8 :=
  ![PolyHom.zero 33 8,PolyHom.zero 33 8,PolyHom.zero 33 8] b
theorem polyLiftFree33_8 : ∀ b : Fin 3, (polyLift33_8 b).freeBlock=basisInt (homKind 33 8) b := by decide
def polyLift33_9 (b : Fin 3) : PolyHom 33 9 :=
  ![PolyHom.zero 33 9,PolyHom.zero 33 9,PolyHom.zero 33 9] b
theorem polyLiftFree33_9 : ∀ b : Fin 3, (polyLift33_9 b).freeBlock=basisInt (homKind 33 9) b := by decide
def polyRep33_10_0 : PolyHom 33 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift33_10 (b : Fin 3) : PolyHom 33 10 :=
  ![polyRep33_10_0,PolyHom.zero 33 10,PolyHom.zero 33 10] b
theorem polyLiftFree33_10 : ∀ b : Fin 3, (polyLift33_10 b).freeBlock=basisInt (homKind 33 10) b := by decide
def polyRep33_11_0 : PolyHom 33 11 where
  M := !![(mono6 (1) 3),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift33_11 (b : Fin 3) : PolyHom 33 11 :=
  ![polyRep33_11_0,PolyHom.zero 33 11,PolyHom.zero 33 11] b
theorem polyLiftFree33_11 : ∀ b : Fin 3, (polyLift33_11 b).freeBlock=basisInt (homKind 33 11) b := by decide
def polyLift33_12 (b : Fin 3) : PolyHom 33 12 :=
  ![PolyHom.zero 33 12,PolyHom.zero 33 12,PolyHom.zero 33 12] b
theorem polyLiftFree33_12 : ∀ b : Fin 3, (polyLift33_12 b).freeBlock=basisInt (homKind 33 12) b := by decide
def polyLift33_13 (b : Fin 3) : PolyHom 33 13 :=
  ![PolyHom.zero 33 13,PolyHom.zero 33 13,PolyHom.zero 33 13] b
theorem polyLiftFree33_13 : ∀ b : Fin 3, (polyLift33_13 b).freeBlock=basisInt (homKind 33 13) b := by decide
def polyLift33_14 (b : Fin 3) : PolyHom 33 14 :=
  ![PolyHom.zero 33 14,PolyHom.zero 33 14,PolyHom.zero 33 14] b
theorem polyLiftFree33_14 : ∀ b : Fin 3, (polyLift33_14 b).freeBlock=basisInt (homKind 33 14) b := by decide
def polyLift33_15 (b : Fin 3) : PolyHom 33 15 :=
  ![PolyHom.zero 33 15,PolyHom.zero 33 15,PolyHom.zero 33 15] b
theorem polyLiftFree33_15 : ∀ b : Fin 3, (polyLift33_15 b).freeBlock=basisInt (homKind 33 15) b := by decide
def polyLift33_16 (b : Fin 3) : PolyHom 33 16 :=
  ![PolyHom.zero 33 16,PolyHom.zero 33 16,PolyHom.zero 33 16] b
theorem polyLiftFree33_16 : ∀ b : Fin 3, (polyLift33_16 b).freeBlock=basisInt (homKind 33 16) b := by decide
def polyLift33_17 (b : Fin 3) : PolyHom 33 17 :=
  ![PolyHom.zero 33 17,PolyHom.zero 33 17,PolyHom.zero 33 17] b
theorem polyLiftFree33_17 : ∀ b : Fin 3, (polyLift33_17 b).freeBlock=basisInt (homKind 33 17) b := by decide
def polyLift33_18 (b : Fin 3) : PolyHom 33 18 :=
  ![PolyHom.zero 33 18,PolyHom.zero 33 18,PolyHom.zero 33 18] b
theorem polyLiftFree33_18 : ∀ b : Fin 3, (polyLift33_18 b).freeBlock=basisInt (homKind 33 18) b := by decide
def polyLift33_19 (b : Fin 3) : PolyHom 33 19 :=
  ![PolyHom.zero 33 19,PolyHom.zero 33 19,PolyHom.zero 33 19] b
theorem polyLiftFree33_19 : ∀ b : Fin 3, (polyLift33_19 b).freeBlock=basisInt (homKind 33 19) b := by decide
def polyLift33_20 (b : Fin 3) : PolyHom 33 20 :=
  ![PolyHom.zero 33 20,PolyHom.zero 33 20,PolyHom.zero 33 20] b
theorem polyLiftFree33_20 : ∀ b : Fin 3, (polyLift33_20 b).freeBlock=basisInt (homKind 33 20) b := by decide
def polyRep33_21_0 : PolyHom 33 21 where
  M := !![(mono6 (1) 2),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift33_21 (b : Fin 3) : PolyHom 33 21 :=
  ![polyRep33_21_0,PolyHom.zero 33 21,PolyHom.zero 33 21] b
theorem polyLiftFree33_21 : ∀ b : Fin 3, (polyLift33_21 b).freeBlock=basisInt (homKind 33 21) b := by decide
def polyLift33_22 (b : Fin 3) : PolyHom 33 22 :=
  ![PolyHom.zero 33 22,PolyHom.zero 33 22,PolyHom.zero 33 22] b
theorem polyLiftFree33_22 : ∀ b : Fin 3, (polyLift33_22 b).freeBlock=basisInt (homKind 33 22) b := by decide
def polyLift33_23 (b : Fin 3) : PolyHom 33 23 :=
  ![PolyHom.zero 33 23,PolyHom.zero 33 23,PolyHom.zero 33 23] b
theorem polyLiftFree33_23 : ∀ b : Fin 3, (polyLift33_23 b).freeBlock=basisInt (homKind 33 23) b := by decide
def polyRep33_24_0 : PolyHom 33 24 where
  M := !![(mono6 (1) 2),0,(mono6 (1) 1),0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift33_24 (b : Fin 3) : PolyHom 33 24 :=
  ![polyRep33_24_0,PolyHom.zero 33 24,PolyHom.zero 33 24] b
theorem polyLiftFree33_24 : ∀ b : Fin 3, (polyLift33_24 b).freeBlock=basisInt (homKind 33 24) b := by decide
def polyRep33_25_0 : PolyHom 33 25 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift33_25 (b : Fin 3) : PolyHom 33 25 :=
  ![polyRep33_25_0,PolyHom.zero 33 25,PolyHom.zero 33 25] b
theorem polyLiftFree33_25 : ∀ b : Fin 3, (polyLift33_25 b).freeBlock=basisInt (homKind 33 25) b := by decide
def polyLift33_26 (b : Fin 3) : PolyHom 33 26 :=
  ![PolyHom.zero 33 26,PolyHom.zero 33 26,PolyHom.zero 33 26] b
theorem polyLiftFree33_26 : ∀ b : Fin 3, (polyLift33_26 b).freeBlock=basisInt (homKind 33 26) b := by decide
def polyLift33_27 (b : Fin 3) : PolyHom 33 27 :=
  ![PolyHom.zero 33 27,PolyHom.zero 33 27,PolyHom.zero 33 27] b
theorem polyLiftFree33_27 : ∀ b : Fin 3, (polyLift33_27 b).freeBlock=basisInt (homKind 33 27) b := by decide
def polyLift33_28 (b : Fin 3) : PolyHom 33 28 :=
  ![PolyHom.zero 33 28,PolyHom.zero 33 28,PolyHom.zero 33 28] b
theorem polyLiftFree33_28 : ∀ b : Fin 3, (polyLift33_28 b).freeBlock=basisInt (homKind 33 28) b := by decide
def polyLift33_29 (b : Fin 3) : PolyHom 33 29 :=
  ![PolyHom.zero 33 29,PolyHom.zero 33 29,PolyHom.zero 33 29] b
theorem polyLiftFree33_29 : ∀ b : Fin 3, (polyLift33_29 b).freeBlock=basisInt (homKind 33 29) b := by decide
def polyRep33_30_0 : PolyHom 33 30 where
  M := !![(mono6 (1) 2),0,(mono6 (1) 0),0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift33_30 (b : Fin 3) : PolyHom 33 30 :=
  ![polyRep33_30_0,PolyHom.zero 33 30,PolyHom.zero 33 30] b
theorem polyLiftFree33_30 : ∀ b : Fin 3, (polyLift33_30 b).freeBlock=basisInt (homKind 33 30) b := by decide
def polyRep33_31_0 : PolyHom 33 31 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift33_31 (b : Fin 3) : PolyHom 33 31 :=
  ![polyRep33_31_0,PolyHom.zero 33 31,PolyHom.zero 33 31] b
theorem polyLiftFree33_31 : ∀ b : Fin 3, (polyLift33_31 b).freeBlock=basisInt (homKind 33 31) b := by decide
def polyLift33_32 (b : Fin 3) : PolyHom 33 32 :=
  ![PolyHom.zero 33 32,PolyHom.zero 33 32,PolyHom.zero 33 32] b
theorem polyLiftFree33_32 : ∀ b : Fin 3, (polyLift33_32 b).freeBlock=basisInt (homKind 33 32) b := by decide
def polyRep33_33_0 : PolyHom 33 33 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift33_33 (b : Fin 3) : PolyHom 33 33 :=
  ![polyRep33_33_0,PolyHom.zero 33 33,PolyHom.zero 33 33] b
theorem polyLiftFree33_33 : ∀ b : Fin 3, (polyLift33_33 b).freeBlock=basisInt (homKind 33 33) b := by decide
def polyLift33_34 (b : Fin 3) : PolyHom 33 34 :=
  ![PolyHom.zero 33 34,PolyHom.zero 33 34,PolyHom.zero 33 34] b
theorem polyLiftFree33_34 : ∀ b : Fin 3, (polyLift33_34 b).freeBlock=basisInt (homKind 33 34) b := by decide
def polyLift33_35 (b : Fin 3) : PolyHom 33 35 :=
  ![PolyHom.zero 33 35,PolyHom.zero 33 35,PolyHom.zero 33 35] b
theorem polyLiftFree33_35 : ∀ b : Fin 3, (polyLift33_35 b).freeBlock=basisInt (homKind 33 35) b := by decide
def polyLift33_36 (b : Fin 3) : PolyHom 33 36 :=
  ![PolyHom.zero 33 36,PolyHom.zero 33 36,PolyHom.zero 33 36] b
theorem polyLiftFree33_36 : ∀ b : Fin 3, (polyLift33_36 b).freeBlock=basisInt (homKind 33 36) b := by decide
def polyRep33_37_0 : PolyHom 33 37 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift33_37 (b : Fin 3) : PolyHom 33 37 :=
  ![polyRep33_37_0,PolyHom.zero 33 37,PolyHom.zero 33 37] b
theorem polyLiftFree33_37 : ∀ b : Fin 3, (polyLift33_37 b).freeBlock=basisInt (homKind 33 37) b := by decide
def polyLift33_38 (b : Fin 3) : PolyHom 33 38 :=
  ![PolyHom.zero 33 38,PolyHom.zero 33 38,PolyHom.zero 33 38] b
theorem polyLiftFree33_38 : ∀ b : Fin 3, (polyLift33_38 b).freeBlock=basisInt (homKind 33 38) b := by decide
def polyLift33_39 (b : Fin 3) : PolyHom 33 39 :=
  ![PolyHom.zero 33 39,PolyHom.zero 33 39,PolyHom.zero 33 39] b
theorem polyLiftFree33_39 : ∀ b : Fin 3, (polyLift33_39 b).freeBlock=basisInt (homKind 33 39) b := by decide
def polyRep33_40_0 : PolyHom 33 40 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift33_40 (b : Fin 3) : PolyHom 33 40 :=
  ![polyRep33_40_0,PolyHom.zero 33 40,PolyHom.zero 33 40] b
theorem polyLiftFree33_40 : ∀ b : Fin 3, (polyLift33_40 b).freeBlock=basisInt (homKind 33 40) b := by decide
def polyLift33_41 (b : Fin 3) : PolyHom 33 41 :=
  ![PolyHom.zero 33 41,PolyHom.zero 33 41,PolyHom.zero 33 41] b
theorem polyLiftFree33_41 : ∀ b : Fin 3, (polyLift33_41 b).freeBlock=basisInt (homKind 33 41) b := by decide
def polyRep33_42_0 : PolyHom 33 42 where
  M := !![0,(mono6 (1) 2),0,(mono6 (-1) 0);0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift33_42 (b : Fin 3) : PolyHom 33 42 :=
  ![polyRep33_42_0,PolyHom.zero 33 42,PolyHom.zero 33 42] b
theorem polyLiftFree33_42 : ∀ b : Fin 3, (polyLift33_42 b).freeBlock=basisInt (homKind 33 42) b := by decide
def polyLift33_43 (b : Fin 3) : PolyHom 33 43 :=
  ![PolyHom.zero 33 43,PolyHom.zero 33 43,PolyHom.zero 33 43] b
theorem polyLiftFree33_43 : ∀ b : Fin 3, (polyLift33_43 b).freeBlock=basisInt (homKind 33 43) b := by decide
def polyRep33_44_0 : PolyHom 33 44 where
  M := !![(mono6 (1) 1),(mono6 (1) 2),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift33_44 (b : Fin 3) : PolyHom 33 44 :=
  ![polyRep33_44_0,PolyHom.zero 33 44,PolyHom.zero 33 44] b
theorem polyLiftFree33_44 : ∀ b : Fin 3, (polyLift33_44 b).freeBlock=basisInt (homKind 33 44) b := by decide
def polyRep33_45_0 : PolyHom 33 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift33_45 (b : Fin 3) : PolyHom 33 45 :=
  ![polyRep33_45_0,PolyHom.zero 33 45,PolyHom.zero 33 45] b
theorem polyLiftFree33_45 : ∀ b : Fin 3, (polyLift33_45 b).freeBlock=basisInt (homKind 33 45) b := by decide
def polyLift33_46 (b : Fin 3) : PolyHom 33 46 :=
  ![PolyHom.zero 33 46,PolyHom.zero 33 46,PolyHom.zero 33 46] b
theorem polyLiftFree33_46 : ∀ b : Fin 3, (polyLift33_46 b).freeBlock=basisInt (homKind 33 46) b := by decide
def polyLiftRow33 (j : Fin 47) (b : Fin 3) : PolyHom 33 j :=
  match j with
  | ⟨0,_⟩ => polyLift33_0 b
  | ⟨1,_⟩ => polyLift33_1 b
  | ⟨2,_⟩ => polyLift33_2 b
  | ⟨3,_⟩ => polyLift33_3 b
  | ⟨4,_⟩ => polyLift33_4 b
  | ⟨5,_⟩ => polyLift33_5 b
  | ⟨6,_⟩ => polyLift33_6 b
  | ⟨7,_⟩ => polyLift33_7 b
  | ⟨8,_⟩ => polyLift33_8 b
  | ⟨9,_⟩ => polyLift33_9 b
  | ⟨10,_⟩ => polyLift33_10 b
  | ⟨11,_⟩ => polyLift33_11 b
  | ⟨12,_⟩ => polyLift33_12 b
  | ⟨13,_⟩ => polyLift33_13 b
  | ⟨14,_⟩ => polyLift33_14 b
  | ⟨15,_⟩ => polyLift33_15 b
  | ⟨16,_⟩ => polyLift33_16 b
  | ⟨17,_⟩ => polyLift33_17 b
  | ⟨18,_⟩ => polyLift33_18 b
  | ⟨19,_⟩ => polyLift33_19 b
  | ⟨20,_⟩ => polyLift33_20 b
  | ⟨21,_⟩ => polyLift33_21 b
  | ⟨22,_⟩ => polyLift33_22 b
  | ⟨23,_⟩ => polyLift33_23 b
  | ⟨24,_⟩ => polyLift33_24 b
  | ⟨25,_⟩ => polyLift33_25 b
  | ⟨26,_⟩ => polyLift33_26 b
  | ⟨27,_⟩ => polyLift33_27 b
  | ⟨28,_⟩ => polyLift33_28 b
  | ⟨29,_⟩ => polyLift33_29 b
  | ⟨30,_⟩ => polyLift33_30 b
  | ⟨31,_⟩ => polyLift33_31 b
  | ⟨32,_⟩ => polyLift33_32 b
  | ⟨33,_⟩ => polyLift33_33 b
  | ⟨34,_⟩ => polyLift33_34 b
  | ⟨35,_⟩ => polyLift33_35 b
  | ⟨36,_⟩ => polyLift33_36 b
  | ⟨37,_⟩ => polyLift33_37 b
  | ⟨38,_⟩ => polyLift33_38 b
  | ⟨39,_⟩ => polyLift33_39 b
  | ⟨40,_⟩ => polyLift33_40 b
  | ⟨41,_⟩ => polyLift33_41 b
  | ⟨42,_⟩ => polyLift33_42 b
  | ⟨43,_⟩ => polyLift33_43 b
  | ⟨44,_⟩ => polyLift33_44 b
  | ⟨45,_⟩ => polyLift33_45 b
  | ⟨46,_⟩ => polyLift33_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree33 (j : Fin 47) (b : Fin 3) : (polyLiftRow33 j b).freeBlock=basisInt (homKind 33 j) b := by
  fin_cases j
  · exact polyLiftFree33_0 b
  · exact polyLiftFree33_1 b
  · exact polyLiftFree33_2 b
  · exact polyLiftFree33_3 b
  · exact polyLiftFree33_4 b
  · exact polyLiftFree33_5 b
  · exact polyLiftFree33_6 b
  · exact polyLiftFree33_7 b
  · exact polyLiftFree33_8 b
  · exact polyLiftFree33_9 b
  · exact polyLiftFree33_10 b
  · exact polyLiftFree33_11 b
  · exact polyLiftFree33_12 b
  · exact polyLiftFree33_13 b
  · exact polyLiftFree33_14 b
  · exact polyLiftFree33_15 b
  · exact polyLiftFree33_16 b
  · exact polyLiftFree33_17 b
  · exact polyLiftFree33_18 b
  · exact polyLiftFree33_19 b
  · exact polyLiftFree33_20 b
  · exact polyLiftFree33_21 b
  · exact polyLiftFree33_22 b
  · exact polyLiftFree33_23 b
  · exact polyLiftFree33_24 b
  · exact polyLiftFree33_25 b
  · exact polyLiftFree33_26 b
  · exact polyLiftFree33_27 b
  · exact polyLiftFree33_28 b
  · exact polyLiftFree33_29 b
  · exact polyLiftFree33_30 b
  · exact polyLiftFree33_31 b
  · exact polyLiftFree33_32 b
  · exact polyLiftFree33_33 b
  · exact polyLiftFree33_34 b
  · exact polyLiftFree33_35 b
  · exact polyLiftFree33_36 b
  · exact polyLiftFree33_37 b
  · exact polyLiftFree33_38 b
  · exact polyLiftFree33_39 b
  · exact polyLiftFree33_40 b
  · exact polyLiftFree33_41 b
  · exact polyLiftFree33_42 b
  · exact polyLiftFree33_43 b
  · exact polyLiftFree33_44 b
  · exact polyLiftFree33_45 b
  · exact polyLiftFree33_46 b
end UniserialComputations.N6
