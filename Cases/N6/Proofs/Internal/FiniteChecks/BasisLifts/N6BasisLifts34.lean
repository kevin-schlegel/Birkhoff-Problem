import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift34_0 (b : Fin 3) : PolyHom 34 0 :=
  ![PolyHom.zero 34 0,PolyHom.zero 34 0,PolyHom.zero 34 0] b
theorem polyLiftFree34_0 : ∀ b : Fin 3, (polyLift34_0 b).freeBlock=basisInt (homKind 34 0) b := by decide
def polyLift34_1 (b : Fin 3) : PolyHom 34 1 :=
  ![PolyHom.zero 34 1,PolyHom.zero 34 1,PolyHom.zero 34 1] b
theorem polyLiftFree34_1 : ∀ b : Fin 3, (polyLift34_1 b).freeBlock=basisInt (homKind 34 1) b := by decide
def polyLift34_2 (b : Fin 3) : PolyHom 34 2 :=
  ![PolyHom.zero 34 2,PolyHom.zero 34 2,PolyHom.zero 34 2] b
theorem polyLiftFree34_2 : ∀ b : Fin 3, (polyLift34_2 b).freeBlock=basisInt (homKind 34 2) b := by decide
def polyLift34_3 (b : Fin 3) : PolyHom 34 3 :=
  ![PolyHom.zero 34 3,PolyHom.zero 34 3,PolyHom.zero 34 3] b
theorem polyLiftFree34_3 : ∀ b : Fin 3, (polyLift34_3 b).freeBlock=basisInt (homKind 34 3) b := by decide
def polyLift34_4 (b : Fin 3) : PolyHom 34 4 :=
  ![PolyHom.zero 34 4,PolyHom.zero 34 4,PolyHom.zero 34 4] b
theorem polyLiftFree34_4 : ∀ b : Fin 3, (polyLift34_4 b).freeBlock=basisInt (homKind 34 4) b := by decide
def polyLift34_5 (b : Fin 3) : PolyHom 34 5 :=
  ![PolyHom.zero 34 5,PolyHom.zero 34 5,PolyHom.zero 34 5] b
theorem polyLiftFree34_5 : ∀ b : Fin 3, (polyLift34_5 b).freeBlock=basisInt (homKind 34 5) b := by decide
def polyLift34_6 (b : Fin 3) : PolyHom 34 6 :=
  ![PolyHom.zero 34 6,PolyHom.zero 34 6,PolyHom.zero 34 6] b
theorem polyLiftFree34_6 : ∀ b : Fin 3, (polyLift34_6 b).freeBlock=basisInt (homKind 34 6) b := by decide
def polyLift34_7 (b : Fin 3) : PolyHom 34 7 :=
  ![PolyHom.zero 34 7,PolyHom.zero 34 7,PolyHom.zero 34 7] b
theorem polyLiftFree34_7 : ∀ b : Fin 3, (polyLift34_7 b).freeBlock=basisInt (homKind 34 7) b := by decide
def polyLift34_8 (b : Fin 3) : PolyHom 34 8 :=
  ![PolyHom.zero 34 8,PolyHom.zero 34 8,PolyHom.zero 34 8] b
theorem polyLiftFree34_8 : ∀ b : Fin 3, (polyLift34_8 b).freeBlock=basisInt (homKind 34 8) b := by decide
def polyLift34_9 (b : Fin 3) : PolyHom 34 9 :=
  ![PolyHom.zero 34 9,PolyHom.zero 34 9,PolyHom.zero 34 9] b
theorem polyLiftFree34_9 : ∀ b : Fin 3, (polyLift34_9 b).freeBlock=basisInt (homKind 34 9) b := by decide
def polyRep34_10_0 : PolyHom 34 10 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift34_10 (b : Fin 3) : PolyHom 34 10 :=
  ![polyRep34_10_0,PolyHom.zero 34 10,PolyHom.zero 34 10] b
theorem polyLiftFree34_10 : ∀ b : Fin 3, (polyLift34_10 b).freeBlock=basisInt (homKind 34 10) b := by decide
def polyRep34_11_0 : PolyHom 34 11 where
  M := !![(mono6 (1) 3),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift34_11 (b : Fin 3) : PolyHom 34 11 :=
  ![polyRep34_11_0,PolyHom.zero 34 11,PolyHom.zero 34 11] b
theorem polyLiftFree34_11 : ∀ b : Fin 3, (polyLift34_11 b).freeBlock=basisInt (homKind 34 11) b := by decide
def polyRep34_12_0 : PolyHom 34 12 where
  M := !![(mono6 (1) 2),0,0,0;(mono6 (-1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift34_12 (b : Fin 3) : PolyHom 34 12 :=
  ![polyRep34_12_0,PolyHom.zero 34 12,PolyHom.zero 34 12] b
theorem polyLiftFree34_12 : ∀ b : Fin 3, (polyLift34_12 b).freeBlock=basisInt (homKind 34 12) b := by decide
def polyLift34_13 (b : Fin 3) : PolyHom 34 13 :=
  ![PolyHom.zero 34 13,PolyHom.zero 34 13,PolyHom.zero 34 13] b
theorem polyLiftFree34_13 : ∀ b : Fin 3, (polyLift34_13 b).freeBlock=basisInt (homKind 34 13) b := by decide
def polyLift34_14 (b : Fin 3) : PolyHom 34 14 :=
  ![PolyHom.zero 34 14,PolyHom.zero 34 14,PolyHom.zero 34 14] b
theorem polyLiftFree34_14 : ∀ b : Fin 3, (polyLift34_14 b).freeBlock=basisInt (homKind 34 14) b := by decide
def polyLift34_15 (b : Fin 3) : PolyHom 34 15 :=
  ![PolyHom.zero 34 15,PolyHom.zero 34 15,PolyHom.zero 34 15] b
theorem polyLiftFree34_15 : ∀ b : Fin 3, (polyLift34_15 b).freeBlock=basisInt (homKind 34 15) b := by decide
def polyLift34_16 (b : Fin 3) : PolyHom 34 16 :=
  ![PolyHom.zero 34 16,PolyHom.zero 34 16,PolyHom.zero 34 16] b
theorem polyLiftFree34_16 : ∀ b : Fin 3, (polyLift34_16 b).freeBlock=basisInt (homKind 34 16) b := by decide
def polyLift34_17 (b : Fin 3) : PolyHom 34 17 :=
  ![PolyHom.zero 34 17,PolyHom.zero 34 17,PolyHom.zero 34 17] b
theorem polyLiftFree34_17 : ∀ b : Fin 3, (polyLift34_17 b).freeBlock=basisInt (homKind 34 17) b := by decide
def polyLift34_18 (b : Fin 3) : PolyHom 34 18 :=
  ![PolyHom.zero 34 18,PolyHom.zero 34 18,PolyHom.zero 34 18] b
theorem polyLiftFree34_18 : ∀ b : Fin 3, (polyLift34_18 b).freeBlock=basisInt (homKind 34 18) b := by decide
def polyLift34_19 (b : Fin 3) : PolyHom 34 19 :=
  ![PolyHom.zero 34 19,PolyHom.zero 34 19,PolyHom.zero 34 19] b
theorem polyLiftFree34_19 : ∀ b : Fin 3, (polyLift34_19 b).freeBlock=basisInt (homKind 34 19) b := by decide
def polyLift34_20 (b : Fin 3) : PolyHom 34 20 :=
  ![PolyHom.zero 34 20,PolyHom.zero 34 20,PolyHom.zero 34 20] b
theorem polyLiftFree34_20 : ∀ b : Fin 3, (polyLift34_20 b).freeBlock=basisInt (homKind 34 20) b := by decide
def polyRep34_21_0 : PolyHom 34 21 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift34_21 (b : Fin 3) : PolyHom 34 21 :=
  ![polyRep34_21_0,PolyHom.zero 34 21,PolyHom.zero 34 21] b
theorem polyLiftFree34_21 : ∀ b : Fin 3, (polyLift34_21 b).freeBlock=basisInt (homKind 34 21) b := by decide
def polyLift34_22 (b : Fin 3) : PolyHom 34 22 :=
  ![PolyHom.zero 34 22,PolyHom.zero 34 22,PolyHom.zero 34 22] b
theorem polyLiftFree34_22 : ∀ b : Fin 3, (polyLift34_22 b).freeBlock=basisInt (homKind 34 22) b := by decide
def polyLift34_23 (b : Fin 3) : PolyHom 34 23 :=
  ![PolyHom.zero 34 23,PolyHom.zero 34 23,PolyHom.zero 34 23] b
theorem polyLiftFree34_23 : ∀ b : Fin 3, (polyLift34_23 b).freeBlock=basisInt (homKind 34 23) b := by decide
def polyRep34_24_0 : PolyHom 34 24 where
  M := !![(mono6 (1) 2),0,(mono6 (1) 1),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift34_24 (b : Fin 3) : PolyHom 34 24 :=
  ![polyRep34_24_0,PolyHom.zero 34 24,PolyHom.zero 34 24] b
theorem polyLiftFree34_24 : ∀ b : Fin 3, (polyLift34_24 b).freeBlock=basisInt (homKind 34 24) b := by decide
def polyRep34_25_0 : PolyHom 34 25 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift34_25 (b : Fin 3) : PolyHom 34 25 :=
  ![polyRep34_25_0,PolyHom.zero 34 25,PolyHom.zero 34 25] b
theorem polyLiftFree34_25 : ∀ b : Fin 3, (polyLift34_25 b).freeBlock=basisInt (homKind 34 25) b := by decide
def polyLift34_26 (b : Fin 3) : PolyHom 34 26 :=
  ![PolyHom.zero 34 26,PolyHom.zero 34 26,PolyHom.zero 34 26] b
theorem polyLiftFree34_26 : ∀ b : Fin 3, (polyLift34_26 b).freeBlock=basisInt (homKind 34 26) b := by decide
def polyRep34_27_0 : PolyHom 34 27 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift34_27 (b : Fin 3) : PolyHom 34 27 :=
  ![polyRep34_27_0,PolyHom.zero 34 27,PolyHom.zero 34 27] b
theorem polyLiftFree34_27 : ∀ b : Fin 3, (polyLift34_27 b).freeBlock=basisInt (homKind 34 27) b := by decide
def polyLift34_28 (b : Fin 3) : PolyHom 34 28 :=
  ![PolyHom.zero 34 28,PolyHom.zero 34 28,PolyHom.zero 34 28] b
theorem polyLiftFree34_28 : ∀ b : Fin 3, (polyLift34_28 b).freeBlock=basisInt (homKind 34 28) b := by decide
def polyLift34_29 (b : Fin 3) : PolyHom 34 29 :=
  ![PolyHom.zero 34 29,PolyHom.zero 34 29,PolyHom.zero 34 29] b
theorem polyLiftFree34_29 : ∀ b : Fin 3, (polyLift34_29 b).freeBlock=basisInt (homKind 34 29) b := by decide
def polyRep34_30_0 : PolyHom 34 30 where
  M := !![(mono6 (1) 2),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift34_30 (b : Fin 3) : PolyHom 34 30 :=
  ![polyRep34_30_0,PolyHom.zero 34 30,PolyHom.zero 34 30] b
theorem polyLiftFree34_30 : ∀ b : Fin 3, (polyLift34_30 b).freeBlock=basisInt (homKind 34 30) b := by decide
def polyRep34_31_0 : PolyHom 34 31 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift34_31 (b : Fin 3) : PolyHom 34 31 :=
  ![polyRep34_31_0,PolyHom.zero 34 31,PolyHom.zero 34 31] b
theorem polyLiftFree34_31 : ∀ b : Fin 3, (polyLift34_31 b).freeBlock=basisInt (homKind 34 31) b := by decide
def polyRep34_32_0 : PolyHom 34 32 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift34_32 (b : Fin 3) : PolyHom 34 32 :=
  ![polyRep34_32_0,PolyHom.zero 34 32,PolyHom.zero 34 32] b
theorem polyLiftFree34_32 : ∀ b : Fin 3, (polyLift34_32 b).freeBlock=basisInt (homKind 34 32) b := by decide
def polyRep34_33_0 : PolyHom 34 33 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift34_33 (b : Fin 3) : PolyHom 34 33 :=
  ![polyRep34_33_0,PolyHom.zero 34 33,PolyHom.zero 34 33] b
theorem polyLiftFree34_33 : ∀ b : Fin 3, (polyLift34_33 b).freeBlock=basisInt (homKind 34 33) b := by decide
def polyRep34_34_0 : PolyHom 34 34 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift34_34 (b : Fin 3) : PolyHom 34 34 :=
  ![polyRep34_34_0,PolyHom.zero 34 34,PolyHom.zero 34 34] b
theorem polyLiftFree34_34 : ∀ b : Fin 3, (polyLift34_34 b).freeBlock=basisInt (homKind 34 34) b := by decide
def polyLift34_35 (b : Fin 3) : PolyHom 34 35 :=
  ![PolyHom.zero 34 35,PolyHom.zero 34 35,PolyHom.zero 34 35] b
theorem polyLiftFree34_35 : ∀ b : Fin 3, (polyLift34_35 b).freeBlock=basisInt (homKind 34 35) b := by decide
def polyLift34_36 (b : Fin 3) : PolyHom 34 36 :=
  ![PolyHom.zero 34 36,PolyHom.zero 34 36,PolyHom.zero 34 36] b
theorem polyLiftFree34_36 : ∀ b : Fin 3, (polyLift34_36 b).freeBlock=basisInt (homKind 34 36) b := by decide
def polyRep34_37_0 : PolyHom 34 37 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift34_37 (b : Fin 3) : PolyHom 34 37 :=
  ![polyRep34_37_0,PolyHom.zero 34 37,PolyHom.zero 34 37] b
theorem polyLiftFree34_37 : ∀ b : Fin 3, (polyLift34_37 b).freeBlock=basisInt (homKind 34 37) b := by decide
def polyRep34_38_0 : PolyHom 34 38 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift34_38 (b : Fin 3) : PolyHom 34 38 :=
  ![polyRep34_38_0,PolyHom.zero 34 38,PolyHom.zero 34 38] b
theorem polyLiftFree34_38 : ∀ b : Fin 3, (polyLift34_38 b).freeBlock=basisInt (homKind 34 38) b := by decide
def polyLift34_39 (b : Fin 3) : PolyHom 34 39 :=
  ![PolyHom.zero 34 39,PolyHom.zero 34 39,PolyHom.zero 34 39] b
theorem polyLiftFree34_39 : ∀ b : Fin 3, (polyLift34_39 b).freeBlock=basisInt (homKind 34 39) b := by decide
def polyRep34_40_0 : PolyHom 34 40 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift34_40 (b : Fin 3) : PolyHom 34 40 :=
  ![polyRep34_40_0,PolyHom.zero 34 40,PolyHom.zero 34 40] b
theorem polyLiftFree34_40 : ∀ b : Fin 3, (polyLift34_40 b).freeBlock=basisInt (homKind 34 40) b := by decide
def polyLift34_41 (b : Fin 3) : PolyHom 34 41 :=
  ![PolyHom.zero 34 41,PolyHom.zero 34 41,PolyHom.zero 34 41] b
theorem polyLiftFree34_41 : ∀ b : Fin 3, (polyLift34_41 b).freeBlock=basisInt (homKind 34 41) b := by decide
def polyRep34_42_0 : PolyHom 34 42 where
  M := !![0,(mono6 (1) 2),0,(mono6 (-1) 0);0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift34_42 (b : Fin 3) : PolyHom 34 42 :=
  ![polyRep34_42_0,PolyHom.zero 34 42,PolyHom.zero 34 42] b
theorem polyLiftFree34_42 : ∀ b : Fin 3, (polyLift34_42 b).freeBlock=basisInt (homKind 34 42) b := by decide
def polyLift34_43 (b : Fin 3) : PolyHom 34 43 :=
  ![PolyHom.zero 34 43,PolyHom.zero 34 43,PolyHom.zero 34 43] b
theorem polyLiftFree34_43 : ∀ b : Fin 3, (polyLift34_43 b).freeBlock=basisInt (homKind 34 43) b := by decide
def polyRep34_44_0 : PolyHom 34 44 where
  M := !![(mono6 (1) 1),(mono6 (1) 2),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift34_44 (b : Fin 3) : PolyHom 34 44 :=
  ![polyRep34_44_0,PolyHom.zero 34 44,PolyHom.zero 34 44] b
theorem polyLiftFree34_44 : ∀ b : Fin 3, (polyLift34_44 b).freeBlock=basisInt (homKind 34 44) b := by decide
def polyRep34_45_0 : PolyHom 34 45 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift34_45 (b : Fin 3) : PolyHom 34 45 :=
  ![polyRep34_45_0,PolyHom.zero 34 45,PolyHom.zero 34 45] b
theorem polyLiftFree34_45 : ∀ b : Fin 3, (polyLift34_45 b).freeBlock=basisInt (homKind 34 45) b := by decide
def polyLift34_46 (b : Fin 3) : PolyHom 34 46 :=
  ![PolyHom.zero 34 46,PolyHom.zero 34 46,PolyHom.zero 34 46] b
theorem polyLiftFree34_46 : ∀ b : Fin 3, (polyLift34_46 b).freeBlock=basisInt (homKind 34 46) b := by decide
def polyLiftRow34 (j : Fin 47) (b : Fin 3) : PolyHom 34 j :=
  match j with
  | ⟨0,_⟩ => polyLift34_0 b
  | ⟨1,_⟩ => polyLift34_1 b
  | ⟨2,_⟩ => polyLift34_2 b
  | ⟨3,_⟩ => polyLift34_3 b
  | ⟨4,_⟩ => polyLift34_4 b
  | ⟨5,_⟩ => polyLift34_5 b
  | ⟨6,_⟩ => polyLift34_6 b
  | ⟨7,_⟩ => polyLift34_7 b
  | ⟨8,_⟩ => polyLift34_8 b
  | ⟨9,_⟩ => polyLift34_9 b
  | ⟨10,_⟩ => polyLift34_10 b
  | ⟨11,_⟩ => polyLift34_11 b
  | ⟨12,_⟩ => polyLift34_12 b
  | ⟨13,_⟩ => polyLift34_13 b
  | ⟨14,_⟩ => polyLift34_14 b
  | ⟨15,_⟩ => polyLift34_15 b
  | ⟨16,_⟩ => polyLift34_16 b
  | ⟨17,_⟩ => polyLift34_17 b
  | ⟨18,_⟩ => polyLift34_18 b
  | ⟨19,_⟩ => polyLift34_19 b
  | ⟨20,_⟩ => polyLift34_20 b
  | ⟨21,_⟩ => polyLift34_21 b
  | ⟨22,_⟩ => polyLift34_22 b
  | ⟨23,_⟩ => polyLift34_23 b
  | ⟨24,_⟩ => polyLift34_24 b
  | ⟨25,_⟩ => polyLift34_25 b
  | ⟨26,_⟩ => polyLift34_26 b
  | ⟨27,_⟩ => polyLift34_27 b
  | ⟨28,_⟩ => polyLift34_28 b
  | ⟨29,_⟩ => polyLift34_29 b
  | ⟨30,_⟩ => polyLift34_30 b
  | ⟨31,_⟩ => polyLift34_31 b
  | ⟨32,_⟩ => polyLift34_32 b
  | ⟨33,_⟩ => polyLift34_33 b
  | ⟨34,_⟩ => polyLift34_34 b
  | ⟨35,_⟩ => polyLift34_35 b
  | ⟨36,_⟩ => polyLift34_36 b
  | ⟨37,_⟩ => polyLift34_37 b
  | ⟨38,_⟩ => polyLift34_38 b
  | ⟨39,_⟩ => polyLift34_39 b
  | ⟨40,_⟩ => polyLift34_40 b
  | ⟨41,_⟩ => polyLift34_41 b
  | ⟨42,_⟩ => polyLift34_42 b
  | ⟨43,_⟩ => polyLift34_43 b
  | ⟨44,_⟩ => polyLift34_44 b
  | ⟨45,_⟩ => polyLift34_45 b
  | ⟨46,_⟩ => polyLift34_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree34 (j : Fin 47) (b : Fin 3) : (polyLiftRow34 j b).freeBlock=basisInt (homKind 34 j) b := by
  fin_cases j
  · exact polyLiftFree34_0 b
  · exact polyLiftFree34_1 b
  · exact polyLiftFree34_2 b
  · exact polyLiftFree34_3 b
  · exact polyLiftFree34_4 b
  · exact polyLiftFree34_5 b
  · exact polyLiftFree34_6 b
  · exact polyLiftFree34_7 b
  · exact polyLiftFree34_8 b
  · exact polyLiftFree34_9 b
  · exact polyLiftFree34_10 b
  · exact polyLiftFree34_11 b
  · exact polyLiftFree34_12 b
  · exact polyLiftFree34_13 b
  · exact polyLiftFree34_14 b
  · exact polyLiftFree34_15 b
  · exact polyLiftFree34_16 b
  · exact polyLiftFree34_17 b
  · exact polyLiftFree34_18 b
  · exact polyLiftFree34_19 b
  · exact polyLiftFree34_20 b
  · exact polyLiftFree34_21 b
  · exact polyLiftFree34_22 b
  · exact polyLiftFree34_23 b
  · exact polyLiftFree34_24 b
  · exact polyLiftFree34_25 b
  · exact polyLiftFree34_26 b
  · exact polyLiftFree34_27 b
  · exact polyLiftFree34_28 b
  · exact polyLiftFree34_29 b
  · exact polyLiftFree34_30 b
  · exact polyLiftFree34_31 b
  · exact polyLiftFree34_32 b
  · exact polyLiftFree34_33 b
  · exact polyLiftFree34_34 b
  · exact polyLiftFree34_35 b
  · exact polyLiftFree34_36 b
  · exact polyLiftFree34_37 b
  · exact polyLiftFree34_38 b
  · exact polyLiftFree34_39 b
  · exact polyLiftFree34_40 b
  · exact polyLiftFree34_41 b
  · exact polyLiftFree34_42 b
  · exact polyLiftFree34_43 b
  · exact polyLiftFree34_44 b
  · exact polyLiftFree34_45 b
  · exact polyLiftFree34_46 b
end UniserialComputations.N6
