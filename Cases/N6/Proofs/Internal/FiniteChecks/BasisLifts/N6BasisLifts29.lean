import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift29_0 (b : Fin 3) : PolyHom 29 0 :=
  ![PolyHom.zero 29 0,PolyHom.zero 29 0,PolyHom.zero 29 0] b
theorem polyLiftFree29_0 : ∀ b : Fin 3, (polyLift29_0 b).freeBlock=basisInt (homKind 29 0) b := by decide
def polyLift29_1 (b : Fin 3) : PolyHom 29 1 :=
  ![PolyHom.zero 29 1,PolyHom.zero 29 1,PolyHom.zero 29 1] b
theorem polyLiftFree29_1 : ∀ b : Fin 3, (polyLift29_1 b).freeBlock=basisInt (homKind 29 1) b := by decide
def polyLift29_2 (b : Fin 3) : PolyHom 29 2 :=
  ![PolyHom.zero 29 2,PolyHom.zero 29 2,PolyHom.zero 29 2] b
theorem polyLiftFree29_2 : ∀ b : Fin 3, (polyLift29_2 b).freeBlock=basisInt (homKind 29 2) b := by decide
def polyLift29_3 (b : Fin 3) : PolyHom 29 3 :=
  ![PolyHom.zero 29 3,PolyHom.zero 29 3,PolyHom.zero 29 3] b
theorem polyLiftFree29_3 : ∀ b : Fin 3, (polyLift29_3 b).freeBlock=basisInt (homKind 29 3) b := by decide
def polyLift29_4 (b : Fin 3) : PolyHom 29 4 :=
  ![PolyHom.zero 29 4,PolyHom.zero 29 4,PolyHom.zero 29 4] b
theorem polyLiftFree29_4 : ∀ b : Fin 3, (polyLift29_4 b).freeBlock=basisInt (homKind 29 4) b := by decide
def polyLift29_5 (b : Fin 3) : PolyHom 29 5 :=
  ![PolyHom.zero 29 5,PolyHom.zero 29 5,PolyHom.zero 29 5] b
theorem polyLiftFree29_5 : ∀ b : Fin 3, (polyLift29_5 b).freeBlock=basisInt (homKind 29 5) b := by decide
def polyLift29_6 (b : Fin 3) : PolyHom 29 6 :=
  ![PolyHom.zero 29 6,PolyHom.zero 29 6,PolyHom.zero 29 6] b
theorem polyLiftFree29_6 : ∀ b : Fin 3, (polyLift29_6 b).freeBlock=basisInt (homKind 29 6) b := by decide
def polyLift29_7 (b : Fin 3) : PolyHom 29 7 :=
  ![PolyHom.zero 29 7,PolyHom.zero 29 7,PolyHom.zero 29 7] b
theorem polyLiftFree29_7 : ∀ b : Fin 3, (polyLift29_7 b).freeBlock=basisInt (homKind 29 7) b := by decide
def polyLift29_8 (b : Fin 3) : PolyHom 29 8 :=
  ![PolyHom.zero 29 8,PolyHom.zero 29 8,PolyHom.zero 29 8] b
theorem polyLiftFree29_8 : ∀ b : Fin 3, (polyLift29_8 b).freeBlock=basisInt (homKind 29 8) b := by decide
def polyLift29_9 (b : Fin 3) : PolyHom 29 9 :=
  ![PolyHom.zero 29 9,PolyHom.zero 29 9,PolyHom.zero 29 9] b
theorem polyLiftFree29_9 : ∀ b : Fin 3, (polyLift29_9 b).freeBlock=basisInt (homKind 29 9) b := by decide
def polyRep29_10_0 : PolyHom 29 10 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_10 (b : Fin 3) : PolyHom 29 10 :=
  ![polyRep29_10_0,PolyHom.zero 29 10,PolyHom.zero 29 10] b
theorem polyLiftFree29_10 : ∀ b : Fin 3, (polyLift29_10 b).freeBlock=basisInt (homKind 29 10) b := by decide
def polyRep29_11_0 : PolyHom 29 11 where
  M := !![(mono6 (1) 3),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_11 (b : Fin 3) : PolyHom 29 11 :=
  ![polyRep29_11_0,PolyHom.zero 29 11,PolyHom.zero 29 11] b
theorem polyLiftFree29_11 : ∀ b : Fin 3, (polyLift29_11 b).freeBlock=basisInt (homKind 29 11) b := by decide
def polyRep29_12_0 : PolyHom 29 12 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_12 (b : Fin 3) : PolyHom 29 12 :=
  ![polyRep29_12_0,PolyHom.zero 29 12,PolyHom.zero 29 12] b
theorem polyLiftFree29_12 : ∀ b : Fin 3, (polyLift29_12 b).freeBlock=basisInt (homKind 29 12) b := by decide
def polyRep29_13_0 : PolyHom 29 13 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_13 (b : Fin 3) : PolyHom 29 13 :=
  ![polyRep29_13_0,PolyHom.zero 29 13,PolyHom.zero 29 13] b
theorem polyLiftFree29_13 : ∀ b : Fin 3, (polyLift29_13 b).freeBlock=basisInt (homKind 29 13) b := by decide
def polyLift29_14 (b : Fin 3) : PolyHom 29 14 :=
  ![PolyHom.zero 29 14,PolyHom.zero 29 14,PolyHom.zero 29 14] b
theorem polyLiftFree29_14 : ∀ b : Fin 3, (polyLift29_14 b).freeBlock=basisInt (homKind 29 14) b := by decide
def polyLift29_15 (b : Fin 3) : PolyHom 29 15 :=
  ![PolyHom.zero 29 15,PolyHom.zero 29 15,PolyHom.zero 29 15] b
theorem polyLiftFree29_15 : ∀ b : Fin 3, (polyLift29_15 b).freeBlock=basisInt (homKind 29 15) b := by decide
def polyLift29_16 (b : Fin 3) : PolyHom 29 16 :=
  ![PolyHom.zero 29 16,PolyHom.zero 29 16,PolyHom.zero 29 16] b
theorem polyLiftFree29_16 : ∀ b : Fin 3, (polyLift29_16 b).freeBlock=basisInt (homKind 29 16) b := by decide
def polyLift29_17 (b : Fin 3) : PolyHom 29 17 :=
  ![PolyHom.zero 29 17,PolyHom.zero 29 17,PolyHom.zero 29 17] b
theorem polyLiftFree29_17 : ∀ b : Fin 3, (polyLift29_17 b).freeBlock=basisInt (homKind 29 17) b := by decide
def polyLift29_18 (b : Fin 3) : PolyHom 29 18 :=
  ![PolyHom.zero 29 18,PolyHom.zero 29 18,PolyHom.zero 29 18] b
theorem polyLiftFree29_18 : ∀ b : Fin 3, (polyLift29_18 b).freeBlock=basisInt (homKind 29 18) b := by decide
def polyLift29_19 (b : Fin 3) : PolyHom 29 19 :=
  ![PolyHom.zero 29 19,PolyHom.zero 29 19,PolyHom.zero 29 19] b
theorem polyLiftFree29_19 : ∀ b : Fin 3, (polyLift29_19 b).freeBlock=basisInt (homKind 29 19) b := by decide
def polyLift29_20 (b : Fin 3) : PolyHom 29 20 :=
  ![PolyHom.zero 29 20,PolyHom.zero 29 20,PolyHom.zero 29 20] b
theorem polyLiftFree29_20 : ∀ b : Fin 3, (polyLift29_20 b).freeBlock=basisInt (homKind 29 20) b := by decide
def polyRep29_21_0 : PolyHom 29 21 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_21 (b : Fin 3) : PolyHom 29 21 :=
  ![polyRep29_21_0,PolyHom.zero 29 21,PolyHom.zero 29 21] b
theorem polyLiftFree29_21 : ∀ b : Fin 3, (polyLift29_21 b).freeBlock=basisInt (homKind 29 21) b := by decide
def polyRep29_22_0 : PolyHom 29 22 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_22 (b : Fin 3) : PolyHom 29 22 :=
  ![polyRep29_22_0,PolyHom.zero 29 22,PolyHom.zero 29 22] b
theorem polyLiftFree29_22 : ∀ b : Fin 3, (polyLift29_22 b).freeBlock=basisInt (homKind 29 22) b := by decide
def polyLift29_23 (b : Fin 3) : PolyHom 29 23 :=
  ![PolyHom.zero 29 23,PolyHom.zero 29 23,PolyHom.zero 29 23] b
theorem polyLiftFree29_23 : ∀ b : Fin 3, (polyLift29_23 b).freeBlock=basisInt (homKind 29 23) b := by decide
def polyRep29_24_0 : PolyHom 29 24 where
  M := !![(mono6 (1) 2),0,(mono6 (1) 1),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_24 (b : Fin 3) : PolyHom 29 24 :=
  ![polyRep29_24_0,PolyHom.zero 29 24,PolyHom.zero 29 24] b
theorem polyLiftFree29_24 : ∀ b : Fin 3, (polyLift29_24 b).freeBlock=basisInt (homKind 29 24) b := by decide
def polyRep29_25_0 : PolyHom 29 25 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_25 (b : Fin 3) : PolyHom 29 25 :=
  ![polyRep29_25_0,PolyHom.zero 29 25,PolyHom.zero 29 25] b
theorem polyLiftFree29_25 : ∀ b : Fin 3, (polyLift29_25 b).freeBlock=basisInt (homKind 29 25) b := by decide
def polyRep29_26_0 : PolyHom 29 26 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_26 (b : Fin 3) : PolyHom 29 26 :=
  ![polyRep29_26_0,PolyHom.zero 29 26,PolyHom.zero 29 26] b
theorem polyLiftFree29_26 : ∀ b : Fin 3, (polyLift29_26 b).freeBlock=basisInt (homKind 29 26) b := by decide
def polyRep29_27_0 : PolyHom 29 27 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_27 (b : Fin 3) : PolyHom 29 27 :=
  ![polyRep29_27_0,PolyHom.zero 29 27,PolyHom.zero 29 27] b
theorem polyLiftFree29_27 : ∀ b : Fin 3, (polyLift29_27 b).freeBlock=basisInt (homKind 29 27) b := by decide
def polyRep29_28_0 : PolyHom 29 28 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_28 (b : Fin 3) : PolyHom 29 28 :=
  ![polyRep29_28_0,PolyHom.zero 29 28,PolyHom.zero 29 28] b
theorem polyLiftFree29_28 : ∀ b : Fin 3, (polyLift29_28 b).freeBlock=basisInt (homKind 29 28) b := by decide
def polyRep29_29_0 : PolyHom 29 29 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_29 (b : Fin 3) : PolyHom 29 29 :=
  ![polyRep29_29_0,PolyHom.zero 29 29,PolyHom.zero 29 29] b
theorem polyLiftFree29_29 : ∀ b : Fin 3, (polyLift29_29 b).freeBlock=basisInt (homKind 29 29) b := by decide
def polyRep29_30_0 : PolyHom 29 30 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_30 (b : Fin 3) : PolyHom 29 30 :=
  ![polyRep29_30_0,PolyHom.zero 29 30,PolyHom.zero 29 30] b
theorem polyLiftFree29_30 : ∀ b : Fin 3, (polyLift29_30 b).freeBlock=basisInt (homKind 29 30) b := by decide
def polyRep29_31_0 : PolyHom 29 31 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_31 (b : Fin 3) : PolyHom 29 31 :=
  ![polyRep29_31_0,PolyHom.zero 29 31,PolyHom.zero 29 31] b
theorem polyLiftFree29_31 : ∀ b : Fin 3, (polyLift29_31 b).freeBlock=basisInt (homKind 29 31) b := by decide
def polyRep29_32_0 : PolyHom 29 32 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_32 (b : Fin 3) : PolyHom 29 32 :=
  ![polyRep29_32_0,PolyHom.zero 29 32,PolyHom.zero 29 32] b
theorem polyLiftFree29_32 : ∀ b : Fin 3, (polyLift29_32 b).freeBlock=basisInt (homKind 29 32) b := by decide
def polyRep29_33_0 : PolyHom 29 33 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_33 (b : Fin 3) : PolyHom 29 33 :=
  ![polyRep29_33_0,PolyHom.zero 29 33,PolyHom.zero 29 33] b
theorem polyLiftFree29_33 : ∀ b : Fin 3, (polyLift29_33 b).freeBlock=basisInt (homKind 29 33) b := by decide
def polyRep29_34_0 : PolyHom 29 34 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_34 (b : Fin 3) : PolyHom 29 34 :=
  ![polyRep29_34_0,PolyHom.zero 29 34,PolyHom.zero 29 34] b
theorem polyLiftFree29_34 : ∀ b : Fin 3, (polyLift29_34 b).freeBlock=basisInt (homKind 29 34) b := by decide
def polyRep29_35_0 : PolyHom 29 35 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_35 (b : Fin 3) : PolyHom 29 35 :=
  ![polyRep29_35_0,PolyHom.zero 29 35,PolyHom.zero 29 35] b
theorem polyLiftFree29_35 : ∀ b : Fin 3, (polyLift29_35 b).freeBlock=basisInt (homKind 29 35) b := by decide
def polyRep29_36_0 : PolyHom 29 36 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_36 (b : Fin 3) : PolyHom 29 36 :=
  ![polyRep29_36_0,PolyHom.zero 29 36,PolyHom.zero 29 36] b
theorem polyLiftFree29_36 : ∀ b : Fin 3, (polyLift29_36 b).freeBlock=basisInt (homKind 29 36) b := by decide
def polyRep29_37_0 : PolyHom 29 37 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_37 (b : Fin 3) : PolyHom 29 37 :=
  ![polyRep29_37_0,PolyHom.zero 29 37,PolyHom.zero 29 37] b
theorem polyLiftFree29_37 : ∀ b : Fin 3, (polyLift29_37 b).freeBlock=basisInt (homKind 29 37) b := by decide
def polyRep29_38_0 : PolyHom 29 38 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_38 (b : Fin 3) : PolyHom 29 38 :=
  ![polyRep29_38_0,PolyHom.zero 29 38,PolyHom.zero 29 38] b
theorem polyLiftFree29_38 : ∀ b : Fin 3, (polyLift29_38 b).freeBlock=basisInt (homKind 29 38) b := by decide
def polyRep29_39_0 : PolyHom 29 39 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_39 (b : Fin 3) : PolyHom 29 39 :=
  ![polyRep29_39_0,PolyHom.zero 29 39,PolyHom.zero 29 39] b
theorem polyLiftFree29_39 : ∀ b : Fin 3, (polyLift29_39 b).freeBlock=basisInt (homKind 29 39) b := by decide
def polyRep29_40_0 : PolyHom 29 40 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_40 (b : Fin 3) : PolyHom 29 40 :=
  ![polyRep29_40_0,PolyHom.zero 29 40,PolyHom.zero 29 40] b
theorem polyLiftFree29_40 : ∀ b : Fin 3, (polyLift29_40 b).freeBlock=basisInt (homKind 29 40) b := by decide
def polyRep29_41_0 : PolyHom 29 41 where
  M := !![(mono6 (1) 0),0,0,(mono6 (1) 0);0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_41 (b : Fin 3) : PolyHom 29 41 :=
  ![polyRep29_41_0,PolyHom.zero 29 41,PolyHom.zero 29 41] b
theorem polyLiftFree29_41 : ∀ b : Fin 3, (polyLift29_41 b).freeBlock=basisInt (homKind 29 41) b := by decide
def polyRep29_42_0 : PolyHom 29 42 where
  M := !![0,(mono6 (1) 2),0,0;0,0,0,0;0,0,(mono6 (1) 0),(mono6 (-1) 1);0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (-1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_42 (b : Fin 3) : PolyHom 29 42 :=
  ![polyRep29_42_0,PolyHom.zero 29 42,PolyHom.zero 29 42] b
theorem polyLiftFree29_42 : ∀ b : Fin 3, (polyLift29_42 b).freeBlock=basisInt (homKind 29 42) b := by decide
def polyRep29_43_0 : PolyHom 29 43 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),(mono6 (1) 0);0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_43 (b : Fin 3) : PolyHom 29 43 :=
  ![polyRep29_43_0,PolyHom.zero 29 43,PolyHom.zero 29 43] b
theorem polyLiftFree29_43 : ∀ b : Fin 3, (polyLift29_43 b).freeBlock=basisInt (homKind 29 43) b := by decide
def polyRep29_44_0 : PolyHom 29 44 where
  M := !![(mono6 (1) 1),(mono6 (1) 2),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep29_44_1 : PolyHom 29 44 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_44 (b : Fin 3) : PolyHom 29 44 :=
  ![polyRep29_44_0,polyRep29_44_1,PolyHom.zero 29 44] b
theorem polyLiftFree29_44 : ∀ b : Fin 3, (polyLift29_44 b).freeBlock=basisInt (homKind 29 44) b := by decide
def polyRep29_45_0 : PolyHom 29 45 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift29_45 (b : Fin 3) : PolyHom 29 45 :=
  ![polyRep29_45_0,PolyHom.zero 29 45,PolyHom.zero 29 45] b
theorem polyLiftFree29_45 : ∀ b : Fin 3, (polyLift29_45 b).freeBlock=basisInt (homKind 29 45) b := by decide
def polyLift29_46 (b : Fin 3) : PolyHom 29 46 :=
  ![PolyHom.zero 29 46,PolyHom.zero 29 46,PolyHom.zero 29 46] b
theorem polyLiftFree29_46 : ∀ b : Fin 3, (polyLift29_46 b).freeBlock=basisInt (homKind 29 46) b := by decide
def polyLiftRow29 (j : Fin 47) (b : Fin 3) : PolyHom 29 j :=
  match j with
  | ⟨0,_⟩ => polyLift29_0 b
  | ⟨1,_⟩ => polyLift29_1 b
  | ⟨2,_⟩ => polyLift29_2 b
  | ⟨3,_⟩ => polyLift29_3 b
  | ⟨4,_⟩ => polyLift29_4 b
  | ⟨5,_⟩ => polyLift29_5 b
  | ⟨6,_⟩ => polyLift29_6 b
  | ⟨7,_⟩ => polyLift29_7 b
  | ⟨8,_⟩ => polyLift29_8 b
  | ⟨9,_⟩ => polyLift29_9 b
  | ⟨10,_⟩ => polyLift29_10 b
  | ⟨11,_⟩ => polyLift29_11 b
  | ⟨12,_⟩ => polyLift29_12 b
  | ⟨13,_⟩ => polyLift29_13 b
  | ⟨14,_⟩ => polyLift29_14 b
  | ⟨15,_⟩ => polyLift29_15 b
  | ⟨16,_⟩ => polyLift29_16 b
  | ⟨17,_⟩ => polyLift29_17 b
  | ⟨18,_⟩ => polyLift29_18 b
  | ⟨19,_⟩ => polyLift29_19 b
  | ⟨20,_⟩ => polyLift29_20 b
  | ⟨21,_⟩ => polyLift29_21 b
  | ⟨22,_⟩ => polyLift29_22 b
  | ⟨23,_⟩ => polyLift29_23 b
  | ⟨24,_⟩ => polyLift29_24 b
  | ⟨25,_⟩ => polyLift29_25 b
  | ⟨26,_⟩ => polyLift29_26 b
  | ⟨27,_⟩ => polyLift29_27 b
  | ⟨28,_⟩ => polyLift29_28 b
  | ⟨29,_⟩ => polyLift29_29 b
  | ⟨30,_⟩ => polyLift29_30 b
  | ⟨31,_⟩ => polyLift29_31 b
  | ⟨32,_⟩ => polyLift29_32 b
  | ⟨33,_⟩ => polyLift29_33 b
  | ⟨34,_⟩ => polyLift29_34 b
  | ⟨35,_⟩ => polyLift29_35 b
  | ⟨36,_⟩ => polyLift29_36 b
  | ⟨37,_⟩ => polyLift29_37 b
  | ⟨38,_⟩ => polyLift29_38 b
  | ⟨39,_⟩ => polyLift29_39 b
  | ⟨40,_⟩ => polyLift29_40 b
  | ⟨41,_⟩ => polyLift29_41 b
  | ⟨42,_⟩ => polyLift29_42 b
  | ⟨43,_⟩ => polyLift29_43 b
  | ⟨44,_⟩ => polyLift29_44 b
  | ⟨45,_⟩ => polyLift29_45 b
  | ⟨46,_⟩ => polyLift29_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree29 (j : Fin 47) (b : Fin 3) : (polyLiftRow29 j b).freeBlock=basisInt (homKind 29 j) b := by
  fin_cases j
  · exact polyLiftFree29_0 b
  · exact polyLiftFree29_1 b
  · exact polyLiftFree29_2 b
  · exact polyLiftFree29_3 b
  · exact polyLiftFree29_4 b
  · exact polyLiftFree29_5 b
  · exact polyLiftFree29_6 b
  · exact polyLiftFree29_7 b
  · exact polyLiftFree29_8 b
  · exact polyLiftFree29_9 b
  · exact polyLiftFree29_10 b
  · exact polyLiftFree29_11 b
  · exact polyLiftFree29_12 b
  · exact polyLiftFree29_13 b
  · exact polyLiftFree29_14 b
  · exact polyLiftFree29_15 b
  · exact polyLiftFree29_16 b
  · exact polyLiftFree29_17 b
  · exact polyLiftFree29_18 b
  · exact polyLiftFree29_19 b
  · exact polyLiftFree29_20 b
  · exact polyLiftFree29_21 b
  · exact polyLiftFree29_22 b
  · exact polyLiftFree29_23 b
  · exact polyLiftFree29_24 b
  · exact polyLiftFree29_25 b
  · exact polyLiftFree29_26 b
  · exact polyLiftFree29_27 b
  · exact polyLiftFree29_28 b
  · exact polyLiftFree29_29 b
  · exact polyLiftFree29_30 b
  · exact polyLiftFree29_31 b
  · exact polyLiftFree29_32 b
  · exact polyLiftFree29_33 b
  · exact polyLiftFree29_34 b
  · exact polyLiftFree29_35 b
  · exact polyLiftFree29_36 b
  · exact polyLiftFree29_37 b
  · exact polyLiftFree29_38 b
  · exact polyLiftFree29_39 b
  · exact polyLiftFree29_40 b
  · exact polyLiftFree29_41 b
  · exact polyLiftFree29_42 b
  · exact polyLiftFree29_43 b
  · exact polyLiftFree29_44 b
  · exact polyLiftFree29_45 b
  · exact polyLiftFree29_46 b
end UniserialComputations.N6
