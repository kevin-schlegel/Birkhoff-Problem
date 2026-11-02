import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift27_0 (b : Fin 3) : PolyHom 27 0 :=
  ![PolyHom.zero 27 0,PolyHom.zero 27 0,PolyHom.zero 27 0] b
theorem polyLiftFree27_0 : ∀ b : Fin 3, (polyLift27_0 b).freeBlock=basisInt (homKind 27 0) b := by decide
def polyLift27_1 (b : Fin 3) : PolyHom 27 1 :=
  ![PolyHom.zero 27 1,PolyHom.zero 27 1,PolyHom.zero 27 1] b
theorem polyLiftFree27_1 : ∀ b : Fin 3, (polyLift27_1 b).freeBlock=basisInt (homKind 27 1) b := by decide
def polyLift27_2 (b : Fin 3) : PolyHom 27 2 :=
  ![PolyHom.zero 27 2,PolyHom.zero 27 2,PolyHom.zero 27 2] b
theorem polyLiftFree27_2 : ∀ b : Fin 3, (polyLift27_2 b).freeBlock=basisInt (homKind 27 2) b := by decide
def polyLift27_3 (b : Fin 3) : PolyHom 27 3 :=
  ![PolyHom.zero 27 3,PolyHom.zero 27 3,PolyHom.zero 27 3] b
theorem polyLiftFree27_3 : ∀ b : Fin 3, (polyLift27_3 b).freeBlock=basisInt (homKind 27 3) b := by decide
def polyLift27_4 (b : Fin 3) : PolyHom 27 4 :=
  ![PolyHom.zero 27 4,PolyHom.zero 27 4,PolyHom.zero 27 4] b
theorem polyLiftFree27_4 : ∀ b : Fin 3, (polyLift27_4 b).freeBlock=basisInt (homKind 27 4) b := by decide
def polyLift27_5 (b : Fin 3) : PolyHom 27 5 :=
  ![PolyHom.zero 27 5,PolyHom.zero 27 5,PolyHom.zero 27 5] b
theorem polyLiftFree27_5 : ∀ b : Fin 3, (polyLift27_5 b).freeBlock=basisInt (homKind 27 5) b := by decide
def polyLift27_6 (b : Fin 3) : PolyHom 27 6 :=
  ![PolyHom.zero 27 6,PolyHom.zero 27 6,PolyHom.zero 27 6] b
theorem polyLiftFree27_6 : ∀ b : Fin 3, (polyLift27_6 b).freeBlock=basisInt (homKind 27 6) b := by decide
def polyLift27_7 (b : Fin 3) : PolyHom 27 7 :=
  ![PolyHom.zero 27 7,PolyHom.zero 27 7,PolyHom.zero 27 7] b
theorem polyLiftFree27_7 : ∀ b : Fin 3, (polyLift27_7 b).freeBlock=basisInt (homKind 27 7) b := by decide
def polyLift27_8 (b : Fin 3) : PolyHom 27 8 :=
  ![PolyHom.zero 27 8,PolyHom.zero 27 8,PolyHom.zero 27 8] b
theorem polyLiftFree27_8 : ∀ b : Fin 3, (polyLift27_8 b).freeBlock=basisInt (homKind 27 8) b := by decide
def polyLift27_9 (b : Fin 3) : PolyHom 27 9 :=
  ![PolyHom.zero 27 9,PolyHom.zero 27 9,PolyHom.zero 27 9] b
theorem polyLiftFree27_9 : ∀ b : Fin 3, (polyLift27_9 b).freeBlock=basisInt (homKind 27 9) b := by decide
def polyRep27_10_0 : PolyHom 27 10 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift27_10 (b : Fin 3) : PolyHom 27 10 :=
  ![polyRep27_10_0,PolyHom.zero 27 10,PolyHom.zero 27 10] b
theorem polyLiftFree27_10 : ∀ b : Fin 3, (polyLift27_10 b).freeBlock=basisInt (homKind 27 10) b := by decide
def polyRep27_11_0 : PolyHom 27 11 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift27_11 (b : Fin 3) : PolyHom 27 11 :=
  ![polyRep27_11_0,PolyHom.zero 27 11,PolyHom.zero 27 11] b
theorem polyLiftFree27_11 : ∀ b : Fin 3, (polyLift27_11 b).freeBlock=basisInt (homKind 27 11) b := by decide
def polyRep27_12_0 : PolyHom 27 12 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift27_12 (b : Fin 3) : PolyHom 27 12 :=
  ![polyRep27_12_0,PolyHom.zero 27 12,PolyHom.zero 27 12] b
theorem polyLiftFree27_12 : ∀ b : Fin 3, (polyLift27_12 b).freeBlock=basisInt (homKind 27 12) b := by decide
def polyLift27_13 (b : Fin 3) : PolyHom 27 13 :=
  ![PolyHom.zero 27 13,PolyHom.zero 27 13,PolyHom.zero 27 13] b
theorem polyLiftFree27_13 : ∀ b : Fin 3, (polyLift27_13 b).freeBlock=basisInt (homKind 27 13) b := by decide
def polyLift27_14 (b : Fin 3) : PolyHom 27 14 :=
  ![PolyHom.zero 27 14,PolyHom.zero 27 14,PolyHom.zero 27 14] b
theorem polyLiftFree27_14 : ∀ b : Fin 3, (polyLift27_14 b).freeBlock=basisInt (homKind 27 14) b := by decide
def polyLift27_15 (b : Fin 3) : PolyHom 27 15 :=
  ![PolyHom.zero 27 15,PolyHom.zero 27 15,PolyHom.zero 27 15] b
theorem polyLiftFree27_15 : ∀ b : Fin 3, (polyLift27_15 b).freeBlock=basisInt (homKind 27 15) b := by decide
def polyLift27_16 (b : Fin 3) : PolyHom 27 16 :=
  ![PolyHom.zero 27 16,PolyHom.zero 27 16,PolyHom.zero 27 16] b
theorem polyLiftFree27_16 : ∀ b : Fin 3, (polyLift27_16 b).freeBlock=basisInt (homKind 27 16) b := by decide
def polyLift27_17 (b : Fin 3) : PolyHom 27 17 :=
  ![PolyHom.zero 27 17,PolyHom.zero 27 17,PolyHom.zero 27 17] b
theorem polyLiftFree27_17 : ∀ b : Fin 3, (polyLift27_17 b).freeBlock=basisInt (homKind 27 17) b := by decide
def polyLift27_18 (b : Fin 3) : PolyHom 27 18 :=
  ![PolyHom.zero 27 18,PolyHom.zero 27 18,PolyHom.zero 27 18] b
theorem polyLiftFree27_18 : ∀ b : Fin 3, (polyLift27_18 b).freeBlock=basisInt (homKind 27 18) b := by decide
def polyLift27_19 (b : Fin 3) : PolyHom 27 19 :=
  ![PolyHom.zero 27 19,PolyHom.zero 27 19,PolyHom.zero 27 19] b
theorem polyLiftFree27_19 : ∀ b : Fin 3, (polyLift27_19 b).freeBlock=basisInt (homKind 27 19) b := by decide
def polyLift27_20 (b : Fin 3) : PolyHom 27 20 :=
  ![PolyHom.zero 27 20,PolyHom.zero 27 20,PolyHom.zero 27 20] b
theorem polyLiftFree27_20 : ∀ b : Fin 3, (polyLift27_20 b).freeBlock=basisInt (homKind 27 20) b := by decide
def polyRep27_21_0 : PolyHom 27 21 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift27_21 (b : Fin 3) : PolyHom 27 21 :=
  ![polyRep27_21_0,PolyHom.zero 27 21,PolyHom.zero 27 21] b
theorem polyLiftFree27_21 : ∀ b : Fin 3, (polyLift27_21 b).freeBlock=basisInt (homKind 27 21) b := by decide
def polyLift27_22 (b : Fin 3) : PolyHom 27 22 :=
  ![PolyHom.zero 27 22,PolyHom.zero 27 22,PolyHom.zero 27 22] b
theorem polyLiftFree27_22 : ∀ b : Fin 3, (polyLift27_22 b).freeBlock=basisInt (homKind 27 22) b := by decide
def polyLift27_23 (b : Fin 3) : PolyHom 27 23 :=
  ![PolyHom.zero 27 23,PolyHom.zero 27 23,PolyHom.zero 27 23] b
theorem polyLiftFree27_23 : ∀ b : Fin 3, (polyLift27_23 b).freeBlock=basisInt (homKind 27 23) b := by decide
def polyRep27_24_0 : PolyHom 27 24 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift27_24 (b : Fin 3) : PolyHom 27 24 :=
  ![polyRep27_24_0,PolyHom.zero 27 24,PolyHom.zero 27 24] b
theorem polyLiftFree27_24 : ∀ b : Fin 3, (polyLift27_24 b).freeBlock=basisInt (homKind 27 24) b := by decide
def polyRep27_25_0 : PolyHom 27 25 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift27_25 (b : Fin 3) : PolyHom 27 25 :=
  ![polyRep27_25_0,PolyHom.zero 27 25,PolyHom.zero 27 25] b
theorem polyLiftFree27_25 : ∀ b : Fin 3, (polyLift27_25 b).freeBlock=basisInt (homKind 27 25) b := by decide
def polyLift27_26 (b : Fin 3) : PolyHom 27 26 :=
  ![PolyHom.zero 27 26,PolyHom.zero 27 26,PolyHom.zero 27 26] b
theorem polyLiftFree27_26 : ∀ b : Fin 3, (polyLift27_26 b).freeBlock=basisInt (homKind 27 26) b := by decide
def polyRep27_27_0 : PolyHom 27 27 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift27_27 (b : Fin 3) : PolyHom 27 27 :=
  ![polyRep27_27_0,PolyHom.zero 27 27,PolyHom.zero 27 27] b
theorem polyLiftFree27_27 : ∀ b : Fin 3, (polyLift27_27 b).freeBlock=basisInt (homKind 27 27) b := by decide
def polyLift27_28 (b : Fin 3) : PolyHom 27 28 :=
  ![PolyHom.zero 27 28,PolyHom.zero 27 28,PolyHom.zero 27 28] b
theorem polyLiftFree27_28 : ∀ b : Fin 3, (polyLift27_28 b).freeBlock=basisInt (homKind 27 28) b := by decide
def polyLift27_29 (b : Fin 3) : PolyHom 27 29 :=
  ![PolyHom.zero 27 29,PolyHom.zero 27 29,PolyHom.zero 27 29] b
theorem polyLiftFree27_29 : ∀ b : Fin 3, (polyLift27_29 b).freeBlock=basisInt (homKind 27 29) b := by decide
def polyRep27_30_0 : PolyHom 27 30 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift27_30 (b : Fin 3) : PolyHom 27 30 :=
  ![polyRep27_30_0,PolyHom.zero 27 30,PolyHom.zero 27 30] b
theorem polyLiftFree27_30 : ∀ b : Fin 3, (polyLift27_30 b).freeBlock=basisInt (homKind 27 30) b := by decide
def polyLift27_31 (b : Fin 3) : PolyHom 27 31 :=
  ![PolyHom.zero 27 31,PolyHom.zero 27 31,PolyHom.zero 27 31] b
theorem polyLiftFree27_31 : ∀ b : Fin 3, (polyLift27_31 b).freeBlock=basisInt (homKind 27 31) b := by decide
def polyLift27_32 (b : Fin 3) : PolyHom 27 32 :=
  ![PolyHom.zero 27 32,PolyHom.zero 27 32,PolyHom.zero 27 32] b
theorem polyLiftFree27_32 : ∀ b : Fin 3, (polyLift27_32 b).freeBlock=basisInt (homKind 27 32) b := by decide
def polyLift27_33 (b : Fin 3) : PolyHom 27 33 :=
  ![PolyHom.zero 27 33,PolyHom.zero 27 33,PolyHom.zero 27 33] b
theorem polyLiftFree27_33 : ∀ b : Fin 3, (polyLift27_33 b).freeBlock=basisInt (homKind 27 33) b := by decide
def polyLift27_34 (b : Fin 3) : PolyHom 27 34 :=
  ![PolyHom.zero 27 34,PolyHom.zero 27 34,PolyHom.zero 27 34] b
theorem polyLiftFree27_34 : ∀ b : Fin 3, (polyLift27_34 b).freeBlock=basisInt (homKind 27 34) b := by decide
def polyLift27_35 (b : Fin 3) : PolyHom 27 35 :=
  ![PolyHom.zero 27 35,PolyHom.zero 27 35,PolyHom.zero 27 35] b
theorem polyLiftFree27_35 : ∀ b : Fin 3, (polyLift27_35 b).freeBlock=basisInt (homKind 27 35) b := by decide
def polyLift27_36 (b : Fin 3) : PolyHom 27 36 :=
  ![PolyHom.zero 27 36,PolyHom.zero 27 36,PolyHom.zero 27 36] b
theorem polyLiftFree27_36 : ∀ b : Fin 3, (polyLift27_36 b).freeBlock=basisInt (homKind 27 36) b := by decide
def polyLift27_37 (b : Fin 3) : PolyHom 27 37 :=
  ![PolyHom.zero 27 37,PolyHom.zero 27 37,PolyHom.zero 27 37] b
theorem polyLiftFree27_37 : ∀ b : Fin 3, (polyLift27_37 b).freeBlock=basisInt (homKind 27 37) b := by decide
def polyLift27_38 (b : Fin 3) : PolyHom 27 38 :=
  ![PolyHom.zero 27 38,PolyHom.zero 27 38,PolyHom.zero 27 38] b
theorem polyLiftFree27_38 : ∀ b : Fin 3, (polyLift27_38 b).freeBlock=basisInt (homKind 27 38) b := by decide
def polyLift27_39 (b : Fin 3) : PolyHom 27 39 :=
  ![PolyHom.zero 27 39,PolyHom.zero 27 39,PolyHom.zero 27 39] b
theorem polyLiftFree27_39 : ∀ b : Fin 3, (polyLift27_39 b).freeBlock=basisInt (homKind 27 39) b := by decide
def polyRep27_40_0 : PolyHom 27 40 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift27_40 (b : Fin 3) : PolyHom 27 40 :=
  ![polyRep27_40_0,PolyHom.zero 27 40,PolyHom.zero 27 40] b
theorem polyLiftFree27_40 : ∀ b : Fin 3, (polyLift27_40 b).freeBlock=basisInt (homKind 27 40) b := by decide
def polyLift27_41 (b : Fin 3) : PolyHom 27 41 :=
  ![PolyHom.zero 27 41,PolyHom.zero 27 41,PolyHom.zero 27 41] b
theorem polyLiftFree27_41 : ∀ b : Fin 3, (polyLift27_41 b).freeBlock=basisInt (homKind 27 41) b := by decide
def polyRep27_42_0 : PolyHom 27 42 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift27_42 (b : Fin 3) : PolyHom 27 42 :=
  ![polyRep27_42_0,PolyHom.zero 27 42,PolyHom.zero 27 42] b
theorem polyLiftFree27_42 : ∀ b : Fin 3, (polyLift27_42 b).freeBlock=basisInt (homKind 27 42) b := by decide
def polyLift27_43 (b : Fin 3) : PolyHom 27 43 :=
  ![PolyHom.zero 27 43,PolyHom.zero 27 43,PolyHom.zero 27 43] b
theorem polyLiftFree27_43 : ∀ b : Fin 3, (polyLift27_43 b).freeBlock=basisInt (homKind 27 43) b := by decide
def polyRep27_44_0 : PolyHom 27 44 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift27_44 (b : Fin 3) : PolyHom 27 44 :=
  ![polyRep27_44_0,PolyHom.zero 27 44,PolyHom.zero 27 44] b
theorem polyLiftFree27_44 : ∀ b : Fin 3, (polyLift27_44 b).freeBlock=basisInt (homKind 27 44) b := by decide
def polyRep27_45_0 : PolyHom 27 45 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift27_45 (b : Fin 3) : PolyHom 27 45 :=
  ![polyRep27_45_0,PolyHom.zero 27 45,PolyHom.zero 27 45] b
theorem polyLiftFree27_45 : ∀ b : Fin 3, (polyLift27_45 b).freeBlock=basisInt (homKind 27 45) b := by decide
def polyLift27_46 (b : Fin 3) : PolyHom 27 46 :=
  ![PolyHom.zero 27 46,PolyHom.zero 27 46,PolyHom.zero 27 46] b
theorem polyLiftFree27_46 : ∀ b : Fin 3, (polyLift27_46 b).freeBlock=basisInt (homKind 27 46) b := by decide
def polyLiftRow27 (j : Fin 47) (b : Fin 3) : PolyHom 27 j :=
  match j with
  | ⟨0,_⟩ => polyLift27_0 b
  | ⟨1,_⟩ => polyLift27_1 b
  | ⟨2,_⟩ => polyLift27_2 b
  | ⟨3,_⟩ => polyLift27_3 b
  | ⟨4,_⟩ => polyLift27_4 b
  | ⟨5,_⟩ => polyLift27_5 b
  | ⟨6,_⟩ => polyLift27_6 b
  | ⟨7,_⟩ => polyLift27_7 b
  | ⟨8,_⟩ => polyLift27_8 b
  | ⟨9,_⟩ => polyLift27_9 b
  | ⟨10,_⟩ => polyLift27_10 b
  | ⟨11,_⟩ => polyLift27_11 b
  | ⟨12,_⟩ => polyLift27_12 b
  | ⟨13,_⟩ => polyLift27_13 b
  | ⟨14,_⟩ => polyLift27_14 b
  | ⟨15,_⟩ => polyLift27_15 b
  | ⟨16,_⟩ => polyLift27_16 b
  | ⟨17,_⟩ => polyLift27_17 b
  | ⟨18,_⟩ => polyLift27_18 b
  | ⟨19,_⟩ => polyLift27_19 b
  | ⟨20,_⟩ => polyLift27_20 b
  | ⟨21,_⟩ => polyLift27_21 b
  | ⟨22,_⟩ => polyLift27_22 b
  | ⟨23,_⟩ => polyLift27_23 b
  | ⟨24,_⟩ => polyLift27_24 b
  | ⟨25,_⟩ => polyLift27_25 b
  | ⟨26,_⟩ => polyLift27_26 b
  | ⟨27,_⟩ => polyLift27_27 b
  | ⟨28,_⟩ => polyLift27_28 b
  | ⟨29,_⟩ => polyLift27_29 b
  | ⟨30,_⟩ => polyLift27_30 b
  | ⟨31,_⟩ => polyLift27_31 b
  | ⟨32,_⟩ => polyLift27_32 b
  | ⟨33,_⟩ => polyLift27_33 b
  | ⟨34,_⟩ => polyLift27_34 b
  | ⟨35,_⟩ => polyLift27_35 b
  | ⟨36,_⟩ => polyLift27_36 b
  | ⟨37,_⟩ => polyLift27_37 b
  | ⟨38,_⟩ => polyLift27_38 b
  | ⟨39,_⟩ => polyLift27_39 b
  | ⟨40,_⟩ => polyLift27_40 b
  | ⟨41,_⟩ => polyLift27_41 b
  | ⟨42,_⟩ => polyLift27_42 b
  | ⟨43,_⟩ => polyLift27_43 b
  | ⟨44,_⟩ => polyLift27_44 b
  | ⟨45,_⟩ => polyLift27_45 b
  | ⟨46,_⟩ => polyLift27_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree27 (j : Fin 47) (b : Fin 3) : (polyLiftRow27 j b).freeBlock=basisInt (homKind 27 j) b := by
  fin_cases j
  · exact polyLiftFree27_0 b
  · exact polyLiftFree27_1 b
  · exact polyLiftFree27_2 b
  · exact polyLiftFree27_3 b
  · exact polyLiftFree27_4 b
  · exact polyLiftFree27_5 b
  · exact polyLiftFree27_6 b
  · exact polyLiftFree27_7 b
  · exact polyLiftFree27_8 b
  · exact polyLiftFree27_9 b
  · exact polyLiftFree27_10 b
  · exact polyLiftFree27_11 b
  · exact polyLiftFree27_12 b
  · exact polyLiftFree27_13 b
  · exact polyLiftFree27_14 b
  · exact polyLiftFree27_15 b
  · exact polyLiftFree27_16 b
  · exact polyLiftFree27_17 b
  · exact polyLiftFree27_18 b
  · exact polyLiftFree27_19 b
  · exact polyLiftFree27_20 b
  · exact polyLiftFree27_21 b
  · exact polyLiftFree27_22 b
  · exact polyLiftFree27_23 b
  · exact polyLiftFree27_24 b
  · exact polyLiftFree27_25 b
  · exact polyLiftFree27_26 b
  · exact polyLiftFree27_27 b
  · exact polyLiftFree27_28 b
  · exact polyLiftFree27_29 b
  · exact polyLiftFree27_30 b
  · exact polyLiftFree27_31 b
  · exact polyLiftFree27_32 b
  · exact polyLiftFree27_33 b
  · exact polyLiftFree27_34 b
  · exact polyLiftFree27_35 b
  · exact polyLiftFree27_36 b
  · exact polyLiftFree27_37 b
  · exact polyLiftFree27_38 b
  · exact polyLiftFree27_39 b
  · exact polyLiftFree27_40 b
  · exact polyLiftFree27_41 b
  · exact polyLiftFree27_42 b
  · exact polyLiftFree27_43 b
  · exact polyLiftFree27_44 b
  · exact polyLiftFree27_45 b
  · exact polyLiftFree27_46 b
end UniserialComputations.N6
