import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift9_0 (b : Fin 3) : PolyHom 9 0 :=
  ![PolyHom.zero 9 0,PolyHom.zero 9 0,PolyHom.zero 9 0] b
theorem polyLiftFree9_0 : ∀ b : Fin 3, (polyLift9_0 b).freeBlock=basisInt (homKind 9 0) b := by decide
def polyLift9_1 (b : Fin 3) : PolyHom 9 1 :=
  ![PolyHom.zero 9 1,PolyHom.zero 9 1,PolyHom.zero 9 1] b
theorem polyLiftFree9_1 : ∀ b : Fin 3, (polyLift9_1 b).freeBlock=basisInt (homKind 9 1) b := by decide
def polyLift9_2 (b : Fin 3) : PolyHom 9 2 :=
  ![PolyHom.zero 9 2,PolyHom.zero 9 2,PolyHom.zero 9 2] b
theorem polyLiftFree9_2 : ∀ b : Fin 3, (polyLift9_2 b).freeBlock=basisInt (homKind 9 2) b := by decide
def polyLift9_3 (b : Fin 3) : PolyHom 9 3 :=
  ![PolyHom.zero 9 3,PolyHom.zero 9 3,PolyHom.zero 9 3] b
theorem polyLiftFree9_3 : ∀ b : Fin 3, (polyLift9_3 b).freeBlock=basisInt (homKind 9 3) b := by decide
def polyLift9_4 (b : Fin 3) : PolyHom 9 4 :=
  ![PolyHom.zero 9 4,PolyHom.zero 9 4,PolyHom.zero 9 4] b
theorem polyLiftFree9_4 : ∀ b : Fin 3, (polyLift9_4 b).freeBlock=basisInt (homKind 9 4) b := by decide
def polyLift9_5 (b : Fin 3) : PolyHom 9 5 :=
  ![PolyHom.zero 9 5,PolyHom.zero 9 5,PolyHom.zero 9 5] b
theorem polyLiftFree9_5 : ∀ b : Fin 3, (polyLift9_5 b).freeBlock=basisInt (homKind 9 5) b := by decide
def polyRep9_6_0 : PolyHom 9 6 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_6 (b : Fin 3) : PolyHom 9 6 :=
  ![polyRep9_6_0,PolyHom.zero 9 6,PolyHom.zero 9 6] b
theorem polyLiftFree9_6 : ∀ b : Fin 3, (polyLift9_6 b).freeBlock=basisInt (homKind 9 6) b := by decide
def polyRep9_7_0 : PolyHom 9 7 where
  M := !![(mono6 (1) 2),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_7 (b : Fin 3) : PolyHom 9 7 :=
  ![polyRep9_7_0,PolyHom.zero 9 7,PolyHom.zero 9 7] b
theorem polyLiftFree9_7 : ∀ b : Fin 3, (polyLift9_7 b).freeBlock=basisInt (homKind 9 7) b := by decide
def polyRep9_8_0 : PolyHom 9 8 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_8 (b : Fin 3) : PolyHom 9 8 :=
  ![polyRep9_8_0,PolyHom.zero 9 8,PolyHom.zero 9 8] b
theorem polyLiftFree9_8 : ∀ b : Fin 3, (polyLift9_8 b).freeBlock=basisInt (homKind 9 8) b := by decide
def polyRep9_9_0 : PolyHom 9 9 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_9 (b : Fin 3) : PolyHom 9 9 :=
  ![polyRep9_9_0,PolyHom.zero 9 9,PolyHom.zero 9 9] b
theorem polyLiftFree9_9 : ∀ b : Fin 3, (polyLift9_9 b).freeBlock=basisInt (homKind 9 9) b := by decide
def polyRep9_10_0 : PolyHom 9 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 4),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_10 (b : Fin 3) : PolyHom 9 10 :=
  ![polyRep9_10_0,PolyHom.zero 9 10,PolyHom.zero 9 10] b
theorem polyLiftFree9_10 : ∀ b : Fin 3, (polyLift9_10 b).freeBlock=basisInt (homKind 9 10) b := by decide
def polyRep9_11_0 : PolyHom 9 11 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_11 (b : Fin 3) : PolyHom 9 11 :=
  ![polyRep9_11_0,PolyHom.zero 9 11,PolyHom.zero 9 11] b
theorem polyLiftFree9_11 : ∀ b : Fin 3, (polyLift9_11 b).freeBlock=basisInt (homKind 9 11) b := by decide
def polyRep9_12_0 : PolyHom 9 12 where
  M := !![(mono6 (1) 2),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_12 (b : Fin 3) : PolyHom 9 12 :=
  ![polyRep9_12_0,PolyHom.zero 9 12,PolyHom.zero 9 12] b
theorem polyLiftFree9_12 : ∀ b : Fin 3, (polyLift9_12 b).freeBlock=basisInt (homKind 9 12) b := by decide
def polyRep9_13_0 : PolyHom 9 13 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_13 (b : Fin 3) : PolyHom 9 13 :=
  ![polyRep9_13_0,PolyHom.zero 9 13,PolyHom.zero 9 13] b
theorem polyLiftFree9_13 : ∀ b : Fin 3, (polyLift9_13 b).freeBlock=basisInt (homKind 9 13) b := by decide
def polyRep9_14_0 : PolyHom 9 14 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_14 (b : Fin 3) : PolyHom 9 14 :=
  ![polyRep9_14_0,PolyHom.zero 9 14,PolyHom.zero 9 14] b
theorem polyLiftFree9_14 : ∀ b : Fin 3, (polyLift9_14 b).freeBlock=basisInt (homKind 9 14) b := by decide
def polyLift9_15 (b : Fin 3) : PolyHom 9 15 :=
  ![PolyHom.zero 9 15,PolyHom.zero 9 15,PolyHom.zero 9 15] b
theorem polyLiftFree9_15 : ∀ b : Fin 3, (polyLift9_15 b).freeBlock=basisInt (homKind 9 15) b := by decide
def polyRep9_16_0 : PolyHom 9 16 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_16 (b : Fin 3) : PolyHom 9 16 :=
  ![polyRep9_16_0,PolyHom.zero 9 16,PolyHom.zero 9 16] b
theorem polyLiftFree9_16 : ∀ b : Fin 3, (polyLift9_16 b).freeBlock=basisInt (homKind 9 16) b := by decide
def polyRep9_17_0 : PolyHom 9 17 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_17 (b : Fin 3) : PolyHom 9 17 :=
  ![polyRep9_17_0,PolyHom.zero 9 17,PolyHom.zero 9 17] b
theorem polyLiftFree9_17 : ∀ b : Fin 3, (polyLift9_17 b).freeBlock=basisInt (homKind 9 17) b := by decide
def polyRep9_18_0 : PolyHom 9 18 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_18 (b : Fin 3) : PolyHom 9 18 :=
  ![polyRep9_18_0,PolyHom.zero 9 18,PolyHom.zero 9 18] b
theorem polyLiftFree9_18 : ∀ b : Fin 3, (polyLift9_18 b).freeBlock=basisInt (homKind 9 18) b := by decide
def polyRep9_19_0 : PolyHom 9 19 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_19 (b : Fin 3) : PolyHom 9 19 :=
  ![polyRep9_19_0,PolyHom.zero 9 19,PolyHom.zero 9 19] b
theorem polyLiftFree9_19 : ∀ b : Fin 3, (polyLift9_19 b).freeBlock=basisInt (homKind 9 19) b := by decide
def polyRep9_20_0 : PolyHom 9 20 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_20 (b : Fin 3) : PolyHom 9 20 :=
  ![polyRep9_20_0,PolyHom.zero 9 20,PolyHom.zero 9 20] b
theorem polyLiftFree9_20 : ∀ b : Fin 3, (polyLift9_20 b).freeBlock=basisInt (homKind 9 20) b := by decide
def polyRep9_21_0 : PolyHom 9 21 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_21 (b : Fin 3) : PolyHom 9 21 :=
  ![polyRep9_21_0,PolyHom.zero 9 21,PolyHom.zero 9 21] b
theorem polyLiftFree9_21 : ∀ b : Fin 3, (polyLift9_21 b).freeBlock=basisInt (homKind 9 21) b := by decide
def polyRep9_22_0 : PolyHom 9 22 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_22 (b : Fin 3) : PolyHom 9 22 :=
  ![polyRep9_22_0,PolyHom.zero 9 22,PolyHom.zero 9 22] b
theorem polyLiftFree9_22 : ∀ b : Fin 3, (polyLift9_22 b).freeBlock=basisInt (homKind 9 22) b := by decide
def polyRep9_23_0 : PolyHom 9 23 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_23 (b : Fin 3) : PolyHom 9 23 :=
  ![polyRep9_23_0,PolyHom.zero 9 23,PolyHom.zero 9 23] b
theorem polyLiftFree9_23 : ∀ b : Fin 3, (polyLift9_23 b).freeBlock=basisInt (homKind 9 23) b := by decide
def polyRep9_24_0 : PolyHom 9 24 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_24 (b : Fin 3) : PolyHom 9 24 :=
  ![polyRep9_24_0,PolyHom.zero 9 24,PolyHom.zero 9 24] b
theorem polyLiftFree9_24 : ∀ b : Fin 3, (polyLift9_24 b).freeBlock=basisInt (homKind 9 24) b := by decide
def polyRep9_25_0 : PolyHom 9 25 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_25 (b : Fin 3) : PolyHom 9 25 :=
  ![polyRep9_25_0,PolyHom.zero 9 25,PolyHom.zero 9 25] b
theorem polyLiftFree9_25 : ∀ b : Fin 3, (polyLift9_25 b).freeBlock=basisInt (homKind 9 25) b := by decide
def polyRep9_26_0 : PolyHom 9 26 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_26 (b : Fin 3) : PolyHom 9 26 :=
  ![polyRep9_26_0,PolyHom.zero 9 26,PolyHom.zero 9 26] b
theorem polyLiftFree9_26 : ∀ b : Fin 3, (polyLift9_26 b).freeBlock=basisInt (homKind 9 26) b := by decide
def polyRep9_27_0 : PolyHom 9 27 where
  M := !![(mono6 (1) 1),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_27 (b : Fin 3) : PolyHom 9 27 :=
  ![polyRep9_27_0,PolyHom.zero 9 27,PolyHom.zero 9 27] b
theorem polyLiftFree9_27 : ∀ b : Fin 3, (polyLift9_27 b).freeBlock=basisInt (homKind 9 27) b := by decide
def polyRep9_28_0 : PolyHom 9 28 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_28 (b : Fin 3) : PolyHom 9 28 :=
  ![polyRep9_28_0,PolyHom.zero 9 28,PolyHom.zero 9 28] b
theorem polyLiftFree9_28 : ∀ b : Fin 3, (polyLift9_28 b).freeBlock=basisInt (homKind 9 28) b := by decide
def polyRep9_29_0 : PolyHom 9 29 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_29 (b : Fin 3) : PolyHom 9 29 :=
  ![polyRep9_29_0,PolyHom.zero 9 29,PolyHom.zero 9 29] b
theorem polyLiftFree9_29 : ∀ b : Fin 3, (polyLift9_29 b).freeBlock=basisInt (homKind 9 29) b := by decide
def polyRep9_30_0 : PolyHom 9 30 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_30 (b : Fin 3) : PolyHom 9 30 :=
  ![polyRep9_30_0,PolyHom.zero 9 30,PolyHom.zero 9 30] b
theorem polyLiftFree9_30 : ∀ b : Fin 3, (polyLift9_30 b).freeBlock=basisInt (homKind 9 30) b := by decide
def polyRep9_31_0 : PolyHom 9 31 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_31 (b : Fin 3) : PolyHom 9 31 :=
  ![polyRep9_31_0,PolyHom.zero 9 31,PolyHom.zero 9 31] b
theorem polyLiftFree9_31 : ∀ b : Fin 3, (polyLift9_31 b).freeBlock=basisInt (homKind 9 31) b := by decide
def polyRep9_32_0 : PolyHom 9 32 where
  M := !![(mono6 (1) 1),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_32 (b : Fin 3) : PolyHom 9 32 :=
  ![polyRep9_32_0,PolyHom.zero 9 32,PolyHom.zero 9 32] b
theorem polyLiftFree9_32 : ∀ b : Fin 3, (polyLift9_32 b).freeBlock=basisInt (homKind 9 32) b := by decide
def polyRep9_33_0 : PolyHom 9 33 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_33 (b : Fin 3) : PolyHom 9 33 :=
  ![polyRep9_33_0,PolyHom.zero 9 33,PolyHom.zero 9 33] b
theorem polyLiftFree9_33 : ∀ b : Fin 3, (polyLift9_33 b).freeBlock=basisInt (homKind 9 33) b := by decide
def polyRep9_34_0 : PolyHom 9 34 where
  M := !![0,(mono6 (-1) 2),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_34 (b : Fin 3) : PolyHom 9 34 :=
  ![polyRep9_34_0,PolyHom.zero 9 34,PolyHom.zero 9 34] b
theorem polyLiftFree9_34 : ∀ b : Fin 3, (polyLift9_34 b).freeBlock=basisInt (homKind 9 34) b := by decide
def polyRep9_35_0 : PolyHom 9 35 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_35 (b : Fin 3) : PolyHom 9 35 :=
  ![polyRep9_35_0,PolyHom.zero 9 35,PolyHom.zero 9 35] b
theorem polyLiftFree9_35 : ∀ b : Fin 3, (polyLift9_35 b).freeBlock=basisInt (homKind 9 35) b := by decide
def polyRep9_36_0 : PolyHom 9 36 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_36 (b : Fin 3) : PolyHom 9 36 :=
  ![polyRep9_36_0,PolyHom.zero 9 36,PolyHom.zero 9 36] b
theorem polyLiftFree9_36 : ∀ b : Fin 3, (polyLift9_36 b).freeBlock=basisInt (homKind 9 36) b := by decide
def polyRep9_37_0 : PolyHom 9 37 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_37 (b : Fin 3) : PolyHom 9 37 :=
  ![polyRep9_37_0,PolyHom.zero 9 37,PolyHom.zero 9 37] b
theorem polyLiftFree9_37 : ∀ b : Fin 3, (polyLift9_37 b).freeBlock=basisInt (homKind 9 37) b := by decide
def polyRep9_38_0 : PolyHom 9 38 where
  M := !![(mono6 (1) 1),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 2);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_38 (b : Fin 3) : PolyHom 9 38 :=
  ![polyRep9_38_0,PolyHom.zero 9 38,PolyHom.zero 9 38] b
theorem polyLiftFree9_38 : ∀ b : Fin 3, (polyLift9_38 b).freeBlock=basisInt (homKind 9 38) b := by decide
def polyRep9_39_0 : PolyHom 9 39 where
  M := !![(mono6 (1) 1),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_39 (b : Fin 3) : PolyHom 9 39 :=
  ![polyRep9_39_0,PolyHom.zero 9 39,PolyHom.zero 9 39] b
theorem polyLiftFree9_39 : ∀ b : Fin 3, (polyLift9_39 b).freeBlock=basisInt (homKind 9 39) b := by decide
def polyRep9_40_0 : PolyHom 9 40 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_40 (b : Fin 3) : PolyHom 9 40 :=
  ![polyRep9_40_0,PolyHom.zero 9 40,PolyHom.zero 9 40] b
theorem polyLiftFree9_40 : ∀ b : Fin 3, (polyLift9_40 b).freeBlock=basisInt (homKind 9 40) b := by decide
def polyRep9_41_0 : PolyHom 9 41 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_41 (b : Fin 3) : PolyHom 9 41 :=
  ![polyRep9_41_0,PolyHom.zero 9 41,PolyHom.zero 9 41] b
theorem polyLiftFree9_41 : ∀ b : Fin 3, (polyLift9_41 b).freeBlock=basisInt (homKind 9 41) b := by decide
def polyRep9_42_0 : PolyHom 9 42 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep9_42_1 : PolyHom 9 42 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_42 (b : Fin 3) : PolyHom 9 42 :=
  ![polyRep9_42_0,polyRep9_42_1,PolyHom.zero 9 42] b
theorem polyLiftFree9_42 : ∀ b : Fin 3, (polyLift9_42 b).freeBlock=basisInt (homKind 9 42) b := by decide
def polyRep9_43_0 : PolyHom 9 43 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep9_43_1 : PolyHom 9 43 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_43 (b : Fin 3) : PolyHom 9 43 :=
  ![polyRep9_43_0,polyRep9_43_1,PolyHom.zero 9 43] b
theorem polyLiftFree9_43 : ∀ b : Fin 3, (polyLift9_43 b).freeBlock=basisInt (homKind 9 43) b := by decide
def polyRep9_44_0 : PolyHom 9 44 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep9_44_1 : PolyHom 9 44 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_44 (b : Fin 3) : PolyHom 9 44 :=
  ![polyRep9_44_0,polyRep9_44_1,PolyHom.zero 9 44] b
theorem polyLiftFree9_44 : ∀ b : Fin 3, (polyLift9_44 b).freeBlock=basisInt (homKind 9 44) b := by decide
def polyRep9_45_0 : PolyHom 9 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift9_45 (b : Fin 3) : PolyHom 9 45 :=
  ![polyRep9_45_0,PolyHom.zero 9 45,PolyHom.zero 9 45] b
theorem polyLiftFree9_45 : ∀ b : Fin 3, (polyLift9_45 b).freeBlock=basisInt (homKind 9 45) b := by decide
def polyLift9_46 (b : Fin 3) : PolyHom 9 46 :=
  ![PolyHom.zero 9 46,PolyHom.zero 9 46,PolyHom.zero 9 46] b
theorem polyLiftFree9_46 : ∀ b : Fin 3, (polyLift9_46 b).freeBlock=basisInt (homKind 9 46) b := by decide
def polyLiftRow9 (j : Fin 47) (b : Fin 3) : PolyHom 9 j :=
  match j with
  | ⟨0,_⟩ => polyLift9_0 b
  | ⟨1,_⟩ => polyLift9_1 b
  | ⟨2,_⟩ => polyLift9_2 b
  | ⟨3,_⟩ => polyLift9_3 b
  | ⟨4,_⟩ => polyLift9_4 b
  | ⟨5,_⟩ => polyLift9_5 b
  | ⟨6,_⟩ => polyLift9_6 b
  | ⟨7,_⟩ => polyLift9_7 b
  | ⟨8,_⟩ => polyLift9_8 b
  | ⟨9,_⟩ => polyLift9_9 b
  | ⟨10,_⟩ => polyLift9_10 b
  | ⟨11,_⟩ => polyLift9_11 b
  | ⟨12,_⟩ => polyLift9_12 b
  | ⟨13,_⟩ => polyLift9_13 b
  | ⟨14,_⟩ => polyLift9_14 b
  | ⟨15,_⟩ => polyLift9_15 b
  | ⟨16,_⟩ => polyLift9_16 b
  | ⟨17,_⟩ => polyLift9_17 b
  | ⟨18,_⟩ => polyLift9_18 b
  | ⟨19,_⟩ => polyLift9_19 b
  | ⟨20,_⟩ => polyLift9_20 b
  | ⟨21,_⟩ => polyLift9_21 b
  | ⟨22,_⟩ => polyLift9_22 b
  | ⟨23,_⟩ => polyLift9_23 b
  | ⟨24,_⟩ => polyLift9_24 b
  | ⟨25,_⟩ => polyLift9_25 b
  | ⟨26,_⟩ => polyLift9_26 b
  | ⟨27,_⟩ => polyLift9_27 b
  | ⟨28,_⟩ => polyLift9_28 b
  | ⟨29,_⟩ => polyLift9_29 b
  | ⟨30,_⟩ => polyLift9_30 b
  | ⟨31,_⟩ => polyLift9_31 b
  | ⟨32,_⟩ => polyLift9_32 b
  | ⟨33,_⟩ => polyLift9_33 b
  | ⟨34,_⟩ => polyLift9_34 b
  | ⟨35,_⟩ => polyLift9_35 b
  | ⟨36,_⟩ => polyLift9_36 b
  | ⟨37,_⟩ => polyLift9_37 b
  | ⟨38,_⟩ => polyLift9_38 b
  | ⟨39,_⟩ => polyLift9_39 b
  | ⟨40,_⟩ => polyLift9_40 b
  | ⟨41,_⟩ => polyLift9_41 b
  | ⟨42,_⟩ => polyLift9_42 b
  | ⟨43,_⟩ => polyLift9_43 b
  | ⟨44,_⟩ => polyLift9_44 b
  | ⟨45,_⟩ => polyLift9_45 b
  | ⟨46,_⟩ => polyLift9_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree9 (j : Fin 47) (b : Fin 3) : (polyLiftRow9 j b).freeBlock=basisInt (homKind 9 j) b := by
  fin_cases j
  · exact polyLiftFree9_0 b
  · exact polyLiftFree9_1 b
  · exact polyLiftFree9_2 b
  · exact polyLiftFree9_3 b
  · exact polyLiftFree9_4 b
  · exact polyLiftFree9_5 b
  · exact polyLiftFree9_6 b
  · exact polyLiftFree9_7 b
  · exact polyLiftFree9_8 b
  · exact polyLiftFree9_9 b
  · exact polyLiftFree9_10 b
  · exact polyLiftFree9_11 b
  · exact polyLiftFree9_12 b
  · exact polyLiftFree9_13 b
  · exact polyLiftFree9_14 b
  · exact polyLiftFree9_15 b
  · exact polyLiftFree9_16 b
  · exact polyLiftFree9_17 b
  · exact polyLiftFree9_18 b
  · exact polyLiftFree9_19 b
  · exact polyLiftFree9_20 b
  · exact polyLiftFree9_21 b
  · exact polyLiftFree9_22 b
  · exact polyLiftFree9_23 b
  · exact polyLiftFree9_24 b
  · exact polyLiftFree9_25 b
  · exact polyLiftFree9_26 b
  · exact polyLiftFree9_27 b
  · exact polyLiftFree9_28 b
  · exact polyLiftFree9_29 b
  · exact polyLiftFree9_30 b
  · exact polyLiftFree9_31 b
  · exact polyLiftFree9_32 b
  · exact polyLiftFree9_33 b
  · exact polyLiftFree9_34 b
  · exact polyLiftFree9_35 b
  · exact polyLiftFree9_36 b
  · exact polyLiftFree9_37 b
  · exact polyLiftFree9_38 b
  · exact polyLiftFree9_39 b
  · exact polyLiftFree9_40 b
  · exact polyLiftFree9_41 b
  · exact polyLiftFree9_42 b
  · exact polyLiftFree9_43 b
  · exact polyLiftFree9_44 b
  · exact polyLiftFree9_45 b
  · exact polyLiftFree9_46 b
end UniserialComputations.N6
