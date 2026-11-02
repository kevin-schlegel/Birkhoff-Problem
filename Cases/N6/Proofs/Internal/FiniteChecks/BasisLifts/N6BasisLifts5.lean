import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift5_0 (b : Fin 3) : PolyHom 5 0 :=
  ![PolyHom.zero 5 0,PolyHom.zero 5 0,PolyHom.zero 5 0] b
theorem polyLiftFree5_0 : ∀ b : Fin 3, (polyLift5_0 b).freeBlock=basisInt (homKind 5 0) b := by decide
def polyLift5_1 (b : Fin 3) : PolyHom 5 1 :=
  ![PolyHom.zero 5 1,PolyHom.zero 5 1,PolyHom.zero 5 1] b
theorem polyLiftFree5_1 : ∀ b : Fin 3, (polyLift5_1 b).freeBlock=basisInt (homKind 5 1) b := by decide
def polyLift5_2 (b : Fin 3) : PolyHom 5 2 :=
  ![PolyHom.zero 5 2,PolyHom.zero 5 2,PolyHom.zero 5 2] b
theorem polyLiftFree5_2 : ∀ b : Fin 3, (polyLift5_2 b).freeBlock=basisInt (homKind 5 2) b := by decide
def polyRep5_3_0 : PolyHom 5 3 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_3 (b : Fin 3) : PolyHom 5 3 :=
  ![polyRep5_3_0,PolyHom.zero 5 3,PolyHom.zero 5 3] b
theorem polyLiftFree5_3 : ∀ b : Fin 3, (polyLift5_3 b).freeBlock=basisInt (homKind 5 3) b := by decide
def polyRep5_4_0 : PolyHom 5 4 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_4 (b : Fin 3) : PolyHom 5 4 :=
  ![polyRep5_4_0,PolyHom.zero 5 4,PolyHom.zero 5 4] b
theorem polyLiftFree5_4 : ∀ b : Fin 3, (polyLift5_4 b).freeBlock=basisInt (homKind 5 4) b := by decide
def polyRep5_5_0 : PolyHom 5 5 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_5 (b : Fin 3) : PolyHom 5 5 :=
  ![polyRep5_5_0,PolyHom.zero 5 5,PolyHom.zero 5 5] b
theorem polyLiftFree5_5 : ∀ b : Fin 3, (polyLift5_5 b).freeBlock=basisInt (homKind 5 5) b := by decide
def polyRep5_6_0 : PolyHom 5 6 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_6 (b : Fin 3) : PolyHom 5 6 :=
  ![polyRep5_6_0,PolyHom.zero 5 6,PolyHom.zero 5 6] b
theorem polyLiftFree5_6 : ∀ b : Fin 3, (polyLift5_6 b).freeBlock=basisInt (homKind 5 6) b := by decide
def polyRep5_7_0 : PolyHom 5 7 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_7 (b : Fin 3) : PolyHom 5 7 :=
  ![polyRep5_7_0,PolyHom.zero 5 7,PolyHom.zero 5 7] b
theorem polyLiftFree5_7 : ∀ b : Fin 3, (polyLift5_7 b).freeBlock=basisInt (homKind 5 7) b := by decide
def polyRep5_8_0 : PolyHom 5 8 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_8 (b : Fin 3) : PolyHom 5 8 :=
  ![polyRep5_8_0,PolyHom.zero 5 8,PolyHom.zero 5 8] b
theorem polyLiftFree5_8 : ∀ b : Fin 3, (polyLift5_8 b).freeBlock=basisInt (homKind 5 8) b := by decide
def polyRep5_9_0 : PolyHom 5 9 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_9 (b : Fin 3) : PolyHom 5 9 :=
  ![polyRep5_9_0,PolyHom.zero 5 9,PolyHom.zero 5 9] b
theorem polyLiftFree5_9 : ∀ b : Fin 3, (polyLift5_9 b).freeBlock=basisInt (homKind 5 9) b := by decide
def polyRep5_10_0 : PolyHom 5 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 4),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_10 (b : Fin 3) : PolyHom 5 10 :=
  ![polyRep5_10_0,PolyHom.zero 5 10,PolyHom.zero 5 10] b
theorem polyLiftFree5_10 : ∀ b : Fin 3, (polyLift5_10 b).freeBlock=basisInt (homKind 5 10) b := by decide
def polyRep5_11_0 : PolyHom 5 11 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_11 (b : Fin 3) : PolyHom 5 11 :=
  ![polyRep5_11_0,PolyHom.zero 5 11,PolyHom.zero 5 11] b
theorem polyLiftFree5_11 : ∀ b : Fin 3, (polyLift5_11 b).freeBlock=basisInt (homKind 5 11) b := by decide
def polyRep5_12_0 : PolyHom 5 12 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_12 (b : Fin 3) : PolyHom 5 12 :=
  ![polyRep5_12_0,PolyHom.zero 5 12,PolyHom.zero 5 12] b
theorem polyLiftFree5_12 : ∀ b : Fin 3, (polyLift5_12 b).freeBlock=basisInt (homKind 5 12) b := by decide
def polyRep5_13_0 : PolyHom 5 13 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_13 (b : Fin 3) : PolyHom 5 13 :=
  ![polyRep5_13_0,PolyHom.zero 5 13,PolyHom.zero 5 13] b
theorem polyLiftFree5_13 : ∀ b : Fin 3, (polyLift5_13 b).freeBlock=basisInt (homKind 5 13) b := by decide
def polyRep5_14_0 : PolyHom 5 14 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_14 (b : Fin 3) : PolyHom 5 14 :=
  ![polyRep5_14_0,PolyHom.zero 5 14,PolyHom.zero 5 14] b
theorem polyLiftFree5_14 : ∀ b : Fin 3, (polyLift5_14 b).freeBlock=basisInt (homKind 5 14) b := by decide
def polyRep5_15_0 : PolyHom 5 15 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_15 (b : Fin 3) : PolyHom 5 15 :=
  ![polyRep5_15_0,PolyHom.zero 5 15,PolyHom.zero 5 15] b
theorem polyLiftFree5_15 : ∀ b : Fin 3, (polyLift5_15 b).freeBlock=basisInt (homKind 5 15) b := by decide
def polyRep5_16_0 : PolyHom 5 16 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_16 (b : Fin 3) : PolyHom 5 16 :=
  ![polyRep5_16_0,PolyHom.zero 5 16,PolyHom.zero 5 16] b
theorem polyLiftFree5_16 : ∀ b : Fin 3, (polyLift5_16 b).freeBlock=basisInt (homKind 5 16) b := by decide
def polyRep5_17_0 : PolyHom 5 17 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_17 (b : Fin 3) : PolyHom 5 17 :=
  ![polyRep5_17_0,PolyHom.zero 5 17,PolyHom.zero 5 17] b
theorem polyLiftFree5_17 : ∀ b : Fin 3, (polyLift5_17 b).freeBlock=basisInt (homKind 5 17) b := by decide
def polyRep5_18_0 : PolyHom 5 18 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_18 (b : Fin 3) : PolyHom 5 18 :=
  ![polyRep5_18_0,PolyHom.zero 5 18,PolyHom.zero 5 18] b
theorem polyLiftFree5_18 : ∀ b : Fin 3, (polyLift5_18 b).freeBlock=basisInt (homKind 5 18) b := by decide
def polyRep5_19_0 : PolyHom 5 19 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_19 (b : Fin 3) : PolyHom 5 19 :=
  ![polyRep5_19_0,PolyHom.zero 5 19,PolyHom.zero 5 19] b
theorem polyLiftFree5_19 : ∀ b : Fin 3, (polyLift5_19 b).freeBlock=basisInt (homKind 5 19) b := by decide
def polyRep5_20_0 : PolyHom 5 20 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_20 (b : Fin 3) : PolyHom 5 20 :=
  ![polyRep5_20_0,PolyHom.zero 5 20,PolyHom.zero 5 20] b
theorem polyLiftFree5_20 : ∀ b : Fin 3, (polyLift5_20 b).freeBlock=basisInt (homKind 5 20) b := by decide
def polyRep5_21_0 : PolyHom 5 21 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_21 (b : Fin 3) : PolyHom 5 21 :=
  ![polyRep5_21_0,PolyHom.zero 5 21,PolyHom.zero 5 21] b
theorem polyLiftFree5_21 : ∀ b : Fin 3, (polyLift5_21 b).freeBlock=basisInt (homKind 5 21) b := by decide
def polyRep5_22_0 : PolyHom 5 22 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_22 (b : Fin 3) : PolyHom 5 22 :=
  ![polyRep5_22_0,PolyHom.zero 5 22,PolyHom.zero 5 22] b
theorem polyLiftFree5_22 : ∀ b : Fin 3, (polyLift5_22 b).freeBlock=basisInt (homKind 5 22) b := by decide
def polyRep5_23_0 : PolyHom 5 23 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_23 (b : Fin 3) : PolyHom 5 23 :=
  ![polyRep5_23_0,PolyHom.zero 5 23,PolyHom.zero 5 23] b
theorem polyLiftFree5_23 : ∀ b : Fin 3, (polyLift5_23 b).freeBlock=basisInt (homKind 5 23) b := by decide
def polyRep5_24_0 : PolyHom 5 24 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_24 (b : Fin 3) : PolyHom 5 24 :=
  ![polyRep5_24_0,PolyHom.zero 5 24,PolyHom.zero 5 24] b
theorem polyLiftFree5_24 : ∀ b : Fin 3, (polyLift5_24 b).freeBlock=basisInt (homKind 5 24) b := by decide
def polyRep5_25_0 : PolyHom 5 25 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_25 (b : Fin 3) : PolyHom 5 25 :=
  ![polyRep5_25_0,PolyHom.zero 5 25,PolyHom.zero 5 25] b
theorem polyLiftFree5_25 : ∀ b : Fin 3, (polyLift5_25 b).freeBlock=basisInt (homKind 5 25) b := by decide
def polyRep5_26_0 : PolyHom 5 26 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_26 (b : Fin 3) : PolyHom 5 26 :=
  ![polyRep5_26_0,PolyHom.zero 5 26,PolyHom.zero 5 26] b
theorem polyLiftFree5_26 : ∀ b : Fin 3, (polyLift5_26 b).freeBlock=basisInt (homKind 5 26) b := by decide
def polyRep5_27_0 : PolyHom 5 27 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_27 (b : Fin 3) : PolyHom 5 27 :=
  ![polyRep5_27_0,PolyHom.zero 5 27,PolyHom.zero 5 27] b
theorem polyLiftFree5_27 : ∀ b : Fin 3, (polyLift5_27 b).freeBlock=basisInt (homKind 5 27) b := by decide
def polyRep5_28_0 : PolyHom 5 28 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_28 (b : Fin 3) : PolyHom 5 28 :=
  ![polyRep5_28_0,PolyHom.zero 5 28,PolyHom.zero 5 28] b
theorem polyLiftFree5_28 : ∀ b : Fin 3, (polyLift5_28 b).freeBlock=basisInt (homKind 5 28) b := by decide
def polyRep5_29_0 : PolyHom 5 29 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_29 (b : Fin 3) : PolyHom 5 29 :=
  ![polyRep5_29_0,PolyHom.zero 5 29,PolyHom.zero 5 29] b
theorem polyLiftFree5_29 : ∀ b : Fin 3, (polyLift5_29 b).freeBlock=basisInt (homKind 5 29) b := by decide
def polyRep5_30_0 : PolyHom 5 30 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep5_30_1 : PolyHom 5 30 where
  M := !![(mono6 (1) 1),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_30 (b : Fin 3) : PolyHom 5 30 :=
  ![polyRep5_30_0,polyRep5_30_1,PolyHom.zero 5 30] b
theorem polyLiftFree5_30 : ∀ b : Fin 3, (polyLift5_30 b).freeBlock=basisInt (homKind 5 30) b := by decide
def polyRep5_31_0 : PolyHom 5 31 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep5_31_1 : PolyHom 5 31 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_31 (b : Fin 3) : PolyHom 5 31 :=
  ![polyRep5_31_0,polyRep5_31_1,PolyHom.zero 5 31] b
theorem polyLiftFree5_31 : ∀ b : Fin 3, (polyLift5_31 b).freeBlock=basisInt (homKind 5 31) b := by decide
def polyRep5_32_0 : PolyHom 5 32 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep5_32_1 : PolyHom 5 32 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_32 (b : Fin 3) : PolyHom 5 32 :=
  ![polyRep5_32_0,polyRep5_32_1,PolyHom.zero 5 32] b
theorem polyLiftFree5_32 : ∀ b : Fin 3, (polyLift5_32 b).freeBlock=basisInt (homKind 5 32) b := by decide
def polyRep5_33_0 : PolyHom 5 33 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_33 (b : Fin 3) : PolyHom 5 33 :=
  ![polyRep5_33_0,PolyHom.zero 5 33,PolyHom.zero 5 33] b
theorem polyLiftFree5_33 : ∀ b : Fin 3, (polyLift5_33 b).freeBlock=basisInt (homKind 5 33) b := by decide
def polyRep5_34_0 : PolyHom 5 34 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_34 (b : Fin 3) : PolyHom 5 34 :=
  ![polyRep5_34_0,PolyHom.zero 5 34,PolyHom.zero 5 34] b
theorem polyLiftFree5_34 : ∀ b : Fin 3, (polyLift5_34 b).freeBlock=basisInt (homKind 5 34) b := by decide
def polyRep5_35_0 : PolyHom 5 35 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_35 (b : Fin 3) : PolyHom 5 35 :=
  ![polyRep5_35_0,PolyHom.zero 5 35,PolyHom.zero 5 35] b
theorem polyLiftFree5_35 : ∀ b : Fin 3, (polyLift5_35 b).freeBlock=basisInt (homKind 5 35) b := by decide
def polyRep5_36_0 : PolyHom 5 36 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_36 (b : Fin 3) : PolyHom 5 36 :=
  ![polyRep5_36_0,PolyHom.zero 5 36,PolyHom.zero 5 36] b
theorem polyLiftFree5_36 : ∀ b : Fin 3, (polyLift5_36 b).freeBlock=basisInt (homKind 5 36) b := by decide
def polyRep5_37_0 : PolyHom 5 37 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep5_37_1 : PolyHom 5 37 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_37 (b : Fin 3) : PolyHom 5 37 :=
  ![polyRep5_37_0,polyRep5_37_1,PolyHom.zero 5 37] b
theorem polyLiftFree5_37 : ∀ b : Fin 3, (polyLift5_37 b).freeBlock=basisInt (homKind 5 37) b := by decide
def polyRep5_38_0 : PolyHom 5 38 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep5_38_1 : PolyHom 5 38 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_38 (b : Fin 3) : PolyHom 5 38 :=
  ![polyRep5_38_0,polyRep5_38_1,PolyHom.zero 5 38] b
theorem polyLiftFree5_38 : ∀ b : Fin 3, (polyLift5_38 b).freeBlock=basisInt (homKind 5 38) b := by decide
def polyRep5_39_0 : PolyHom 5 39 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep5_39_1 : PolyHom 5 39 where
  M := !![(mono6 (1) 0),(mono6 (1) 0),0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_39 (b : Fin 3) : PolyHom 5 39 :=
  ![polyRep5_39_0,polyRep5_39_1,PolyHom.zero 5 39] b
theorem polyLiftFree5_39 : ∀ b : Fin 3, (polyLift5_39 b).freeBlock=basisInt (homKind 5 39) b := by decide
def polyRep5_40_0 : PolyHom 5 40 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep5_40_1 : PolyHom 5 40 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_40 (b : Fin 3) : PolyHom 5 40 :=
  ![polyRep5_40_0,polyRep5_40_1,PolyHom.zero 5 40] b
theorem polyLiftFree5_40 : ∀ b : Fin 3, (polyLift5_40 b).freeBlock=basisInt (homKind 5 40) b := by decide
def polyRep5_41_0 : PolyHom 5 41 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_41 (b : Fin 3) : PolyHom 5 41 :=
  ![polyRep5_41_0,PolyHom.zero 5 41,PolyHom.zero 5 41] b
theorem polyLiftFree5_41 : ∀ b : Fin 3, (polyLift5_41 b).freeBlock=basisInt (homKind 5 41) b := by decide
def polyRep5_42_0 : PolyHom 5 42 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep5_42_1 : PolyHom 5 42 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_42 (b : Fin 3) : PolyHom 5 42 :=
  ![polyRep5_42_0,polyRep5_42_1,PolyHom.zero 5 42] b
theorem polyLiftFree5_42 : ∀ b : Fin 3, (polyLift5_42 b).freeBlock=basisInt (homKind 5 42) b := by decide
def polyRep5_43_0 : PolyHom 5 43 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep5_43_1 : PolyHom 5 43 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_43 (b : Fin 3) : PolyHom 5 43 :=
  ![polyRep5_43_0,polyRep5_43_1,PolyHom.zero 5 43] b
theorem polyLiftFree5_43 : ∀ b : Fin 3, (polyLift5_43 b).freeBlock=basisInt (homKind 5 43) b := by decide
def polyRep5_44_0 : PolyHom 5 44 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep5_44_1 : PolyHom 5 44 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_44 (b : Fin 3) : PolyHom 5 44 :=
  ![polyRep5_44_0,polyRep5_44_1,PolyHom.zero 5 44] b
theorem polyLiftFree5_44 : ∀ b : Fin 3, (polyLift5_44 b).freeBlock=basisInt (homKind 5 44) b := by decide
def polyRep5_45_0 : PolyHom 5 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift5_45 (b : Fin 3) : PolyHom 5 45 :=
  ![polyRep5_45_0,PolyHom.zero 5 45,PolyHom.zero 5 45] b
theorem polyLiftFree5_45 : ∀ b : Fin 3, (polyLift5_45 b).freeBlock=basisInt (homKind 5 45) b := by decide
def polyLift5_46 (b : Fin 3) : PolyHom 5 46 :=
  ![PolyHom.zero 5 46,PolyHom.zero 5 46,PolyHom.zero 5 46] b
theorem polyLiftFree5_46 : ∀ b : Fin 3, (polyLift5_46 b).freeBlock=basisInt (homKind 5 46) b := by decide
def polyLiftRow5 (j : Fin 47) (b : Fin 3) : PolyHom 5 j :=
  match j with
  | ⟨0,_⟩ => polyLift5_0 b
  | ⟨1,_⟩ => polyLift5_1 b
  | ⟨2,_⟩ => polyLift5_2 b
  | ⟨3,_⟩ => polyLift5_3 b
  | ⟨4,_⟩ => polyLift5_4 b
  | ⟨5,_⟩ => polyLift5_5 b
  | ⟨6,_⟩ => polyLift5_6 b
  | ⟨7,_⟩ => polyLift5_7 b
  | ⟨8,_⟩ => polyLift5_8 b
  | ⟨9,_⟩ => polyLift5_9 b
  | ⟨10,_⟩ => polyLift5_10 b
  | ⟨11,_⟩ => polyLift5_11 b
  | ⟨12,_⟩ => polyLift5_12 b
  | ⟨13,_⟩ => polyLift5_13 b
  | ⟨14,_⟩ => polyLift5_14 b
  | ⟨15,_⟩ => polyLift5_15 b
  | ⟨16,_⟩ => polyLift5_16 b
  | ⟨17,_⟩ => polyLift5_17 b
  | ⟨18,_⟩ => polyLift5_18 b
  | ⟨19,_⟩ => polyLift5_19 b
  | ⟨20,_⟩ => polyLift5_20 b
  | ⟨21,_⟩ => polyLift5_21 b
  | ⟨22,_⟩ => polyLift5_22 b
  | ⟨23,_⟩ => polyLift5_23 b
  | ⟨24,_⟩ => polyLift5_24 b
  | ⟨25,_⟩ => polyLift5_25 b
  | ⟨26,_⟩ => polyLift5_26 b
  | ⟨27,_⟩ => polyLift5_27 b
  | ⟨28,_⟩ => polyLift5_28 b
  | ⟨29,_⟩ => polyLift5_29 b
  | ⟨30,_⟩ => polyLift5_30 b
  | ⟨31,_⟩ => polyLift5_31 b
  | ⟨32,_⟩ => polyLift5_32 b
  | ⟨33,_⟩ => polyLift5_33 b
  | ⟨34,_⟩ => polyLift5_34 b
  | ⟨35,_⟩ => polyLift5_35 b
  | ⟨36,_⟩ => polyLift5_36 b
  | ⟨37,_⟩ => polyLift5_37 b
  | ⟨38,_⟩ => polyLift5_38 b
  | ⟨39,_⟩ => polyLift5_39 b
  | ⟨40,_⟩ => polyLift5_40 b
  | ⟨41,_⟩ => polyLift5_41 b
  | ⟨42,_⟩ => polyLift5_42 b
  | ⟨43,_⟩ => polyLift5_43 b
  | ⟨44,_⟩ => polyLift5_44 b
  | ⟨45,_⟩ => polyLift5_45 b
  | ⟨46,_⟩ => polyLift5_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree5 (j : Fin 47) (b : Fin 3) : (polyLiftRow5 j b).freeBlock=basisInt (homKind 5 j) b := by
  fin_cases j
  · exact polyLiftFree5_0 b
  · exact polyLiftFree5_1 b
  · exact polyLiftFree5_2 b
  · exact polyLiftFree5_3 b
  · exact polyLiftFree5_4 b
  · exact polyLiftFree5_5 b
  · exact polyLiftFree5_6 b
  · exact polyLiftFree5_7 b
  · exact polyLiftFree5_8 b
  · exact polyLiftFree5_9 b
  · exact polyLiftFree5_10 b
  · exact polyLiftFree5_11 b
  · exact polyLiftFree5_12 b
  · exact polyLiftFree5_13 b
  · exact polyLiftFree5_14 b
  · exact polyLiftFree5_15 b
  · exact polyLiftFree5_16 b
  · exact polyLiftFree5_17 b
  · exact polyLiftFree5_18 b
  · exact polyLiftFree5_19 b
  · exact polyLiftFree5_20 b
  · exact polyLiftFree5_21 b
  · exact polyLiftFree5_22 b
  · exact polyLiftFree5_23 b
  · exact polyLiftFree5_24 b
  · exact polyLiftFree5_25 b
  · exact polyLiftFree5_26 b
  · exact polyLiftFree5_27 b
  · exact polyLiftFree5_28 b
  · exact polyLiftFree5_29 b
  · exact polyLiftFree5_30 b
  · exact polyLiftFree5_31 b
  · exact polyLiftFree5_32 b
  · exact polyLiftFree5_33 b
  · exact polyLiftFree5_34 b
  · exact polyLiftFree5_35 b
  · exact polyLiftFree5_36 b
  · exact polyLiftFree5_37 b
  · exact polyLiftFree5_38 b
  · exact polyLiftFree5_39 b
  · exact polyLiftFree5_40 b
  · exact polyLiftFree5_41 b
  · exact polyLiftFree5_42 b
  · exact polyLiftFree5_43 b
  · exact polyLiftFree5_44 b
  · exact polyLiftFree5_45 b
  · exact polyLiftFree5_46 b
end UniserialComputations.N6
