import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift22_0 (b : Fin 3) : PolyHom 22 0 :=
  ![PolyHom.zero 22 0,PolyHom.zero 22 0,PolyHom.zero 22 0] b
theorem polyLiftFree22_0 : ∀ b : Fin 3, (polyLift22_0 b).freeBlock=basisInt (homKind 22 0) b := by decide
def polyLift22_1 (b : Fin 3) : PolyHom 22 1 :=
  ![PolyHom.zero 22 1,PolyHom.zero 22 1,PolyHom.zero 22 1] b
theorem polyLiftFree22_1 : ∀ b : Fin 3, (polyLift22_1 b).freeBlock=basisInt (homKind 22 1) b := by decide
def polyLift22_2 (b : Fin 3) : PolyHom 22 2 :=
  ![PolyHom.zero 22 2,PolyHom.zero 22 2,PolyHom.zero 22 2] b
theorem polyLiftFree22_2 : ∀ b : Fin 3, (polyLift22_2 b).freeBlock=basisInt (homKind 22 2) b := by decide
def polyLift22_3 (b : Fin 3) : PolyHom 22 3 :=
  ![PolyHom.zero 22 3,PolyHom.zero 22 3,PolyHom.zero 22 3] b
theorem polyLiftFree22_3 : ∀ b : Fin 3, (polyLift22_3 b).freeBlock=basisInt (homKind 22 3) b := by decide
def polyLift22_4 (b : Fin 3) : PolyHom 22 4 :=
  ![PolyHom.zero 22 4,PolyHom.zero 22 4,PolyHom.zero 22 4] b
theorem polyLiftFree22_4 : ∀ b : Fin 3, (polyLift22_4 b).freeBlock=basisInt (homKind 22 4) b := by decide
def polyLift22_5 (b : Fin 3) : PolyHom 22 5 :=
  ![PolyHom.zero 22 5,PolyHom.zero 22 5,PolyHom.zero 22 5] b
theorem polyLiftFree22_5 : ∀ b : Fin 3, (polyLift22_5 b).freeBlock=basisInt (homKind 22 5) b := by decide
def polyLift22_6 (b : Fin 3) : PolyHom 22 6 :=
  ![PolyHom.zero 22 6,PolyHom.zero 22 6,PolyHom.zero 22 6] b
theorem polyLiftFree22_6 : ∀ b : Fin 3, (polyLift22_6 b).freeBlock=basisInt (homKind 22 6) b := by decide
def polyLift22_7 (b : Fin 3) : PolyHom 22 7 :=
  ![PolyHom.zero 22 7,PolyHom.zero 22 7,PolyHom.zero 22 7] b
theorem polyLiftFree22_7 : ∀ b : Fin 3, (polyLift22_7 b).freeBlock=basisInt (homKind 22 7) b := by decide
def polyLift22_8 (b : Fin 3) : PolyHom 22 8 :=
  ![PolyHom.zero 22 8,PolyHom.zero 22 8,PolyHom.zero 22 8] b
theorem polyLiftFree22_8 : ∀ b : Fin 3, (polyLift22_8 b).freeBlock=basisInt (homKind 22 8) b := by decide
def polyLift22_9 (b : Fin 3) : PolyHom 22 9 :=
  ![PolyHom.zero 22 9,PolyHom.zero 22 9,PolyHom.zero 22 9] b
theorem polyLiftFree22_9 : ∀ b : Fin 3, (polyLift22_9 b).freeBlock=basisInt (homKind 22 9) b := by decide
def polyRep22_10_0 : PolyHom 22 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift22_10 (b : Fin 3) : PolyHom 22 10 :=
  ![polyRep22_10_0,PolyHom.zero 22 10,PolyHom.zero 22 10] b
theorem polyLiftFree22_10 : ∀ b : Fin 3, (polyLift22_10 b).freeBlock=basisInt (homKind 22 10) b := by decide
def polyRep22_11_0 : PolyHom 22 11 where
  M := !![(mono6 (1) 2),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift22_11 (b : Fin 3) : PolyHom 22 11 :=
  ![polyRep22_11_0,PolyHom.zero 22 11,PolyHom.zero 22 11] b
theorem polyLiftFree22_11 : ∀ b : Fin 3, (polyLift22_11 b).freeBlock=basisInt (homKind 22 11) b := by decide
def polyRep22_12_0 : PolyHom 22 12 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift22_12 (b : Fin 3) : PolyHom 22 12 :=
  ![polyRep22_12_0,PolyHom.zero 22 12,PolyHom.zero 22 12] b
theorem polyLiftFree22_12 : ∀ b : Fin 3, (polyLift22_12 b).freeBlock=basisInt (homKind 22 12) b := by decide
def polyLift22_13 (b : Fin 3) : PolyHom 22 13 :=
  ![PolyHom.zero 22 13,PolyHom.zero 22 13,PolyHom.zero 22 13] b
theorem polyLiftFree22_13 : ∀ b : Fin 3, (polyLift22_13 b).freeBlock=basisInt (homKind 22 13) b := by decide
def polyLift22_14 (b : Fin 3) : PolyHom 22 14 :=
  ![PolyHom.zero 22 14,PolyHom.zero 22 14,PolyHom.zero 22 14] b
theorem polyLiftFree22_14 : ∀ b : Fin 3, (polyLift22_14 b).freeBlock=basisInt (homKind 22 14) b := by decide
def polyLift22_15 (b : Fin 3) : PolyHom 22 15 :=
  ![PolyHom.zero 22 15,PolyHom.zero 22 15,PolyHom.zero 22 15] b
theorem polyLiftFree22_15 : ∀ b : Fin 3, (polyLift22_15 b).freeBlock=basisInt (homKind 22 15) b := by decide
def polyLift22_16 (b : Fin 3) : PolyHom 22 16 :=
  ![PolyHom.zero 22 16,PolyHom.zero 22 16,PolyHom.zero 22 16] b
theorem polyLiftFree22_16 : ∀ b : Fin 3, (polyLift22_16 b).freeBlock=basisInt (homKind 22 16) b := by decide
def polyLift22_17 (b : Fin 3) : PolyHom 22 17 :=
  ![PolyHom.zero 22 17,PolyHom.zero 22 17,PolyHom.zero 22 17] b
theorem polyLiftFree22_17 : ∀ b : Fin 3, (polyLift22_17 b).freeBlock=basisInt (homKind 22 17) b := by decide
def polyLift22_18 (b : Fin 3) : PolyHom 22 18 :=
  ![PolyHom.zero 22 18,PolyHom.zero 22 18,PolyHom.zero 22 18] b
theorem polyLiftFree22_18 : ∀ b : Fin 3, (polyLift22_18 b).freeBlock=basisInt (homKind 22 18) b := by decide
def polyLift22_19 (b : Fin 3) : PolyHom 22 19 :=
  ![PolyHom.zero 22 19,PolyHom.zero 22 19,PolyHom.zero 22 19] b
theorem polyLiftFree22_19 : ∀ b : Fin 3, (polyLift22_19 b).freeBlock=basisInt (homKind 22 19) b := by decide
def polyLift22_20 (b : Fin 3) : PolyHom 22 20 :=
  ![PolyHom.zero 22 20,PolyHom.zero 22 20,PolyHom.zero 22 20] b
theorem polyLiftFree22_20 : ∀ b : Fin 3, (polyLift22_20 b).freeBlock=basisInt (homKind 22 20) b := by decide
def polyRep22_21_0 : PolyHom 22 21 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift22_21 (b : Fin 3) : PolyHom 22 21 :=
  ![polyRep22_21_0,PolyHom.zero 22 21,PolyHom.zero 22 21] b
theorem polyLiftFree22_21 : ∀ b : Fin 3, (polyLift22_21 b).freeBlock=basisInt (homKind 22 21) b := by decide
def polyRep22_22_0 : PolyHom 22 22 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift22_22 (b : Fin 3) : PolyHom 22 22 :=
  ![polyRep22_22_0,PolyHom.zero 22 22,PolyHom.zero 22 22] b
theorem polyLiftFree22_22 : ∀ b : Fin 3, (polyLift22_22 b).freeBlock=basisInt (homKind 22 22) b := by decide
def polyLift22_23 (b : Fin 3) : PolyHom 22 23 :=
  ![PolyHom.zero 22 23,PolyHom.zero 22 23,PolyHom.zero 22 23] b
theorem polyLiftFree22_23 : ∀ b : Fin 3, (polyLift22_23 b).freeBlock=basisInt (homKind 22 23) b := by decide
def polyRep22_24_0 : PolyHom 22 24 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift22_24 (b : Fin 3) : PolyHom 22 24 :=
  ![polyRep22_24_0,PolyHom.zero 22 24,PolyHom.zero 22 24] b
theorem polyLiftFree22_24 : ∀ b : Fin 3, (polyLift22_24 b).freeBlock=basisInt (homKind 22 24) b := by decide
def polyRep22_25_0 : PolyHom 22 25 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift22_25 (b : Fin 3) : PolyHom 22 25 :=
  ![polyRep22_25_0,PolyHom.zero 22 25,PolyHom.zero 22 25] b
theorem polyLiftFree22_25 : ∀ b : Fin 3, (polyLift22_25 b).freeBlock=basisInt (homKind 22 25) b := by decide
def polyLift22_26 (b : Fin 3) : PolyHom 22 26 :=
  ![PolyHom.zero 22 26,PolyHom.zero 22 26,PolyHom.zero 22 26] b
theorem polyLiftFree22_26 : ∀ b : Fin 3, (polyLift22_26 b).freeBlock=basisInt (homKind 22 26) b := by decide
def polyRep22_27_0 : PolyHom 22 27 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift22_27 (b : Fin 3) : PolyHom 22 27 :=
  ![polyRep22_27_0,PolyHom.zero 22 27,PolyHom.zero 22 27] b
theorem polyLiftFree22_27 : ∀ b : Fin 3, (polyLift22_27 b).freeBlock=basisInt (homKind 22 27) b := by decide
def polyLift22_28 (b : Fin 3) : PolyHom 22 28 :=
  ![PolyHom.zero 22 28,PolyHom.zero 22 28,PolyHom.zero 22 28] b
theorem polyLiftFree22_28 : ∀ b : Fin 3, (polyLift22_28 b).freeBlock=basisInt (homKind 22 28) b := by decide
def polyLift22_29 (b : Fin 3) : PolyHom 22 29 :=
  ![PolyHom.zero 22 29,PolyHom.zero 22 29,PolyHom.zero 22 29] b
theorem polyLiftFree22_29 : ∀ b : Fin 3, (polyLift22_29 b).freeBlock=basisInt (homKind 22 29) b := by decide
def polyRep22_30_0 : PolyHom 22 30 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift22_30 (b : Fin 3) : PolyHom 22 30 :=
  ![polyRep22_30_0,PolyHom.zero 22 30,PolyHom.zero 22 30] b
theorem polyLiftFree22_30 : ∀ b : Fin 3, (polyLift22_30 b).freeBlock=basisInt (homKind 22 30) b := by decide
def polyLift22_31 (b : Fin 3) : PolyHom 22 31 :=
  ![PolyHom.zero 22 31,PolyHom.zero 22 31,PolyHom.zero 22 31] b
theorem polyLiftFree22_31 : ∀ b : Fin 3, (polyLift22_31 b).freeBlock=basisInt (homKind 22 31) b := by decide
def polyLift22_32 (b : Fin 3) : PolyHom 22 32 :=
  ![PolyHom.zero 22 32,PolyHom.zero 22 32,PolyHom.zero 22 32] b
theorem polyLiftFree22_32 : ∀ b : Fin 3, (polyLift22_32 b).freeBlock=basisInt (homKind 22 32) b := by decide
def polyLift22_33 (b : Fin 3) : PolyHom 22 33 :=
  ![PolyHom.zero 22 33,PolyHom.zero 22 33,PolyHom.zero 22 33] b
theorem polyLiftFree22_33 : ∀ b : Fin 3, (polyLift22_33 b).freeBlock=basisInt (homKind 22 33) b := by decide
def polyLift22_34 (b : Fin 3) : PolyHom 22 34 :=
  ![PolyHom.zero 22 34,PolyHom.zero 22 34,PolyHom.zero 22 34] b
theorem polyLiftFree22_34 : ∀ b : Fin 3, (polyLift22_34 b).freeBlock=basisInt (homKind 22 34) b := by decide
def polyLift22_35 (b : Fin 3) : PolyHom 22 35 :=
  ![PolyHom.zero 22 35,PolyHom.zero 22 35,PolyHom.zero 22 35] b
theorem polyLiftFree22_35 : ∀ b : Fin 3, (polyLift22_35 b).freeBlock=basisInt (homKind 22 35) b := by decide
def polyLift22_36 (b : Fin 3) : PolyHom 22 36 :=
  ![PolyHom.zero 22 36,PolyHom.zero 22 36,PolyHom.zero 22 36] b
theorem polyLiftFree22_36 : ∀ b : Fin 3, (polyLift22_36 b).freeBlock=basisInt (homKind 22 36) b := by decide
def polyRep22_37_0 : PolyHom 22 37 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift22_37 (b : Fin 3) : PolyHom 22 37 :=
  ![polyRep22_37_0,PolyHom.zero 22 37,PolyHom.zero 22 37] b
theorem polyLiftFree22_37 : ∀ b : Fin 3, (polyLift22_37 b).freeBlock=basisInt (homKind 22 37) b := by decide
def polyRep22_38_0 : PolyHom 22 38 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift22_38 (b : Fin 3) : PolyHom 22 38 :=
  ![polyRep22_38_0,PolyHom.zero 22 38,PolyHom.zero 22 38] b
theorem polyLiftFree22_38 : ∀ b : Fin 3, (polyLift22_38 b).freeBlock=basisInt (homKind 22 38) b := by decide
def polyLift22_39 (b : Fin 3) : PolyHom 22 39 :=
  ![PolyHom.zero 22 39,PolyHom.zero 22 39,PolyHom.zero 22 39] b
theorem polyLiftFree22_39 : ∀ b : Fin 3, (polyLift22_39 b).freeBlock=basisInt (homKind 22 39) b := by decide
def polyRep22_40_0 : PolyHom 22 40 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift22_40 (b : Fin 3) : PolyHom 22 40 :=
  ![polyRep22_40_0,PolyHom.zero 22 40,PolyHom.zero 22 40] b
theorem polyLiftFree22_40 : ∀ b : Fin 3, (polyLift22_40 b).freeBlock=basisInt (homKind 22 40) b := by decide
def polyLift22_41 (b : Fin 3) : PolyHom 22 41 :=
  ![PolyHom.zero 22 41,PolyHom.zero 22 41,PolyHom.zero 22 41] b
theorem polyLiftFree22_41 : ∀ b : Fin 3, (polyLift22_41 b).freeBlock=basisInt (homKind 22 41) b := by decide
def polyRep22_42_0 : PolyHom 22 42 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift22_42 (b : Fin 3) : PolyHom 22 42 :=
  ![polyRep22_42_0,PolyHom.zero 22 42,PolyHom.zero 22 42] b
theorem polyLiftFree22_42 : ∀ b : Fin 3, (polyLift22_42 b).freeBlock=basisInt (homKind 22 42) b := by decide
def polyLift22_43 (b : Fin 3) : PolyHom 22 43 :=
  ![PolyHom.zero 22 43,PolyHom.zero 22 43,PolyHom.zero 22 43] b
theorem polyLiftFree22_43 : ∀ b : Fin 3, (polyLift22_43 b).freeBlock=basisInt (homKind 22 43) b := by decide
def polyRep22_44_0 : PolyHom 22 44 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift22_44 (b : Fin 3) : PolyHom 22 44 :=
  ![polyRep22_44_0,PolyHom.zero 22 44,PolyHom.zero 22 44] b
theorem polyLiftFree22_44 : ∀ b : Fin 3, (polyLift22_44 b).freeBlock=basisInt (homKind 22 44) b := by decide
def polyRep22_45_0 : PolyHom 22 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift22_45 (b : Fin 3) : PolyHom 22 45 :=
  ![polyRep22_45_0,PolyHom.zero 22 45,PolyHom.zero 22 45] b
theorem polyLiftFree22_45 : ∀ b : Fin 3, (polyLift22_45 b).freeBlock=basisInt (homKind 22 45) b := by decide
def polyLift22_46 (b : Fin 3) : PolyHom 22 46 :=
  ![PolyHom.zero 22 46,PolyHom.zero 22 46,PolyHom.zero 22 46] b
theorem polyLiftFree22_46 : ∀ b : Fin 3, (polyLift22_46 b).freeBlock=basisInt (homKind 22 46) b := by decide
def polyLiftRow22 (j : Fin 47) (b : Fin 3) : PolyHom 22 j :=
  match j with
  | ⟨0,_⟩ => polyLift22_0 b
  | ⟨1,_⟩ => polyLift22_1 b
  | ⟨2,_⟩ => polyLift22_2 b
  | ⟨3,_⟩ => polyLift22_3 b
  | ⟨4,_⟩ => polyLift22_4 b
  | ⟨5,_⟩ => polyLift22_5 b
  | ⟨6,_⟩ => polyLift22_6 b
  | ⟨7,_⟩ => polyLift22_7 b
  | ⟨8,_⟩ => polyLift22_8 b
  | ⟨9,_⟩ => polyLift22_9 b
  | ⟨10,_⟩ => polyLift22_10 b
  | ⟨11,_⟩ => polyLift22_11 b
  | ⟨12,_⟩ => polyLift22_12 b
  | ⟨13,_⟩ => polyLift22_13 b
  | ⟨14,_⟩ => polyLift22_14 b
  | ⟨15,_⟩ => polyLift22_15 b
  | ⟨16,_⟩ => polyLift22_16 b
  | ⟨17,_⟩ => polyLift22_17 b
  | ⟨18,_⟩ => polyLift22_18 b
  | ⟨19,_⟩ => polyLift22_19 b
  | ⟨20,_⟩ => polyLift22_20 b
  | ⟨21,_⟩ => polyLift22_21 b
  | ⟨22,_⟩ => polyLift22_22 b
  | ⟨23,_⟩ => polyLift22_23 b
  | ⟨24,_⟩ => polyLift22_24 b
  | ⟨25,_⟩ => polyLift22_25 b
  | ⟨26,_⟩ => polyLift22_26 b
  | ⟨27,_⟩ => polyLift22_27 b
  | ⟨28,_⟩ => polyLift22_28 b
  | ⟨29,_⟩ => polyLift22_29 b
  | ⟨30,_⟩ => polyLift22_30 b
  | ⟨31,_⟩ => polyLift22_31 b
  | ⟨32,_⟩ => polyLift22_32 b
  | ⟨33,_⟩ => polyLift22_33 b
  | ⟨34,_⟩ => polyLift22_34 b
  | ⟨35,_⟩ => polyLift22_35 b
  | ⟨36,_⟩ => polyLift22_36 b
  | ⟨37,_⟩ => polyLift22_37 b
  | ⟨38,_⟩ => polyLift22_38 b
  | ⟨39,_⟩ => polyLift22_39 b
  | ⟨40,_⟩ => polyLift22_40 b
  | ⟨41,_⟩ => polyLift22_41 b
  | ⟨42,_⟩ => polyLift22_42 b
  | ⟨43,_⟩ => polyLift22_43 b
  | ⟨44,_⟩ => polyLift22_44 b
  | ⟨45,_⟩ => polyLift22_45 b
  | ⟨46,_⟩ => polyLift22_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree22 (j : Fin 47) (b : Fin 3) : (polyLiftRow22 j b).freeBlock=basisInt (homKind 22 j) b := by
  fin_cases j
  · exact polyLiftFree22_0 b
  · exact polyLiftFree22_1 b
  · exact polyLiftFree22_2 b
  · exact polyLiftFree22_3 b
  · exact polyLiftFree22_4 b
  · exact polyLiftFree22_5 b
  · exact polyLiftFree22_6 b
  · exact polyLiftFree22_7 b
  · exact polyLiftFree22_8 b
  · exact polyLiftFree22_9 b
  · exact polyLiftFree22_10 b
  · exact polyLiftFree22_11 b
  · exact polyLiftFree22_12 b
  · exact polyLiftFree22_13 b
  · exact polyLiftFree22_14 b
  · exact polyLiftFree22_15 b
  · exact polyLiftFree22_16 b
  · exact polyLiftFree22_17 b
  · exact polyLiftFree22_18 b
  · exact polyLiftFree22_19 b
  · exact polyLiftFree22_20 b
  · exact polyLiftFree22_21 b
  · exact polyLiftFree22_22 b
  · exact polyLiftFree22_23 b
  · exact polyLiftFree22_24 b
  · exact polyLiftFree22_25 b
  · exact polyLiftFree22_26 b
  · exact polyLiftFree22_27 b
  · exact polyLiftFree22_28 b
  · exact polyLiftFree22_29 b
  · exact polyLiftFree22_30 b
  · exact polyLiftFree22_31 b
  · exact polyLiftFree22_32 b
  · exact polyLiftFree22_33 b
  · exact polyLiftFree22_34 b
  · exact polyLiftFree22_35 b
  · exact polyLiftFree22_36 b
  · exact polyLiftFree22_37 b
  · exact polyLiftFree22_38 b
  · exact polyLiftFree22_39 b
  · exact polyLiftFree22_40 b
  · exact polyLiftFree22_41 b
  · exact polyLiftFree22_42 b
  · exact polyLiftFree22_43 b
  · exact polyLiftFree22_44 b
  · exact polyLiftFree22_45 b
  · exact polyLiftFree22_46 b
end UniserialComputations.N6
