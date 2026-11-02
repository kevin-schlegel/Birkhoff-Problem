import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyRep46_0_0 : PolyHom 46 0 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_0 (b : Fin 3) : PolyHom 46 0 :=
  ![polyRep46_0_0,PolyHom.zero 46 0,PolyHom.zero 46 0] b
theorem polyLiftFree46_0 : ∀ b : Fin 3, (polyLift46_0 b).freeBlock=basisInt (homKind 46 0) b := by decide
def polyRep46_1_0 : PolyHom 46 1 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_1 (b : Fin 3) : PolyHom 46 1 :=
  ![polyRep46_1_0,PolyHom.zero 46 1,PolyHom.zero 46 1] b
theorem polyLiftFree46_1 : ∀ b : Fin 3, (polyLift46_1 b).freeBlock=basisInt (homKind 46 1) b := by decide
def polyRep46_2_0 : PolyHom 46 2 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_2 (b : Fin 3) : PolyHom 46 2 :=
  ![polyRep46_2_0,PolyHom.zero 46 2,PolyHom.zero 46 2] b
theorem polyLiftFree46_2 : ∀ b : Fin 3, (polyLift46_2 b).freeBlock=basisInt (homKind 46 2) b := by decide
def polyRep46_3_0 : PolyHom 46 3 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_3 (b : Fin 3) : PolyHom 46 3 :=
  ![polyRep46_3_0,PolyHom.zero 46 3,PolyHom.zero 46 3] b
theorem polyLiftFree46_3 : ∀ b : Fin 3, (polyLift46_3 b).freeBlock=basisInt (homKind 46 3) b := by decide
def polyRep46_4_0 : PolyHom 46 4 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_4 (b : Fin 3) : PolyHom 46 4 :=
  ![polyRep46_4_0,PolyHom.zero 46 4,PolyHom.zero 46 4] b
theorem polyLiftFree46_4 : ∀ b : Fin 3, (polyLift46_4 b).freeBlock=basisInt (homKind 46 4) b := by decide
def polyRep46_5_0 : PolyHom 46 5 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_5 (b : Fin 3) : PolyHom 46 5 :=
  ![polyRep46_5_0,PolyHom.zero 46 5,PolyHom.zero 46 5] b
theorem polyLiftFree46_5 : ∀ b : Fin 3, (polyLift46_5 b).freeBlock=basisInt (homKind 46 5) b := by decide
def polyRep46_6_0 : PolyHom 46 6 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 4),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_6 (b : Fin 3) : PolyHom 46 6 :=
  ![polyRep46_6_0,PolyHom.zero 46 6,PolyHom.zero 46 6] b
theorem polyLiftFree46_6 : ∀ b : Fin 3, (polyLift46_6 b).freeBlock=basisInt (homKind 46 6) b := by decide
def polyRep46_7_0 : PolyHom 46 7 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_7 (b : Fin 3) : PolyHom 46 7 :=
  ![polyRep46_7_0,PolyHom.zero 46 7,PolyHom.zero 46 7] b
theorem polyLiftFree46_7 : ∀ b : Fin 3, (polyLift46_7 b).freeBlock=basisInt (homKind 46 7) b := by decide
def polyRep46_8_0 : PolyHom 46 8 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_8 (b : Fin 3) : PolyHom 46 8 :=
  ![polyRep46_8_0,PolyHom.zero 46 8,PolyHom.zero 46 8] b
theorem polyLiftFree46_8 : ∀ b : Fin 3, (polyLift46_8 b).freeBlock=basisInt (homKind 46 8) b := by decide
def polyRep46_9_0 : PolyHom 46 9 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_9 (b : Fin 3) : PolyHom 46 9 :=
  ![polyRep46_9_0,PolyHom.zero 46 9,PolyHom.zero 46 9] b
theorem polyLiftFree46_9 : ∀ b : Fin 3, (polyLift46_9 b).freeBlock=basisInt (homKind 46 9) b := by decide
def polyRep46_10_0 : PolyHom 46 10 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 5),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_10 (b : Fin 3) : PolyHom 46 10 :=
  ![polyRep46_10_0,PolyHom.zero 46 10,PolyHom.zero 46 10] b
theorem polyLiftFree46_10 : ∀ b : Fin 3, (polyLift46_10 b).freeBlock=basisInt (homKind 46 10) b := by decide
def polyRep46_11_0 : PolyHom 46 11 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 4),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_11 (b : Fin 3) : PolyHom 46 11 :=
  ![polyRep46_11_0,PolyHom.zero 46 11,PolyHom.zero 46 11] b
theorem polyLiftFree46_11 : ∀ b : Fin 3, (polyLift46_11 b).freeBlock=basisInt (homKind 46 11) b := by decide
def polyRep46_12_0 : PolyHom 46 12 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_12 (b : Fin 3) : PolyHom 46 12 :=
  ![polyRep46_12_0,PolyHom.zero 46 12,PolyHom.zero 46 12] b
theorem polyLiftFree46_12 : ∀ b : Fin 3, (polyLift46_12 b).freeBlock=basisInt (homKind 46 12) b := by decide
def polyRep46_13_0 : PolyHom 46 13 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_13 (b : Fin 3) : PolyHom 46 13 :=
  ![polyRep46_13_0,PolyHom.zero 46 13,PolyHom.zero 46 13] b
theorem polyLiftFree46_13 : ∀ b : Fin 3, (polyLift46_13 b).freeBlock=basisInt (homKind 46 13) b := by decide
def polyRep46_14_0 : PolyHom 46 14 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_14 (b : Fin 3) : PolyHom 46 14 :=
  ![polyRep46_14_0,PolyHom.zero 46 14,PolyHom.zero 46 14] b
theorem polyLiftFree46_14 : ∀ b : Fin 3, (polyLift46_14 b).freeBlock=basisInt (homKind 46 14) b := by decide
def polyRep46_15_0 : PolyHom 46 15 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_15 (b : Fin 3) : PolyHom 46 15 :=
  ![polyRep46_15_0,PolyHom.zero 46 15,PolyHom.zero 46 15] b
theorem polyLiftFree46_15 : ∀ b : Fin 3, (polyLift46_15 b).freeBlock=basisInt (homKind 46 15) b := by decide
def polyRep46_16_0 : PolyHom 46 16 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_16 (b : Fin 3) : PolyHom 46 16 :=
  ![polyRep46_16_0,PolyHom.zero 46 16,PolyHom.zero 46 16] b
theorem polyLiftFree46_16 : ∀ b : Fin 3, (polyLift46_16 b).freeBlock=basisInt (homKind 46 16) b := by decide
def polyRep46_17_0 : PolyHom 46 17 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_17 (b : Fin 3) : PolyHom 46 17 :=
  ![polyRep46_17_0,PolyHom.zero 46 17,PolyHom.zero 46 17] b
theorem polyLiftFree46_17 : ∀ b : Fin 3, (polyLift46_17 b).freeBlock=basisInt (homKind 46 17) b := by decide
def polyRep46_18_0 : PolyHom 46 18 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep46_18_1 : PolyHom 46 18 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_18 (b : Fin 3) : PolyHom 46 18 :=
  ![polyRep46_18_0,polyRep46_18_1,PolyHom.zero 46 18] b
theorem polyLiftFree46_18 : ∀ b : Fin 3, (polyLift46_18 b).freeBlock=basisInt (homKind 46 18) b := by decide
def polyRep46_19_0 : PolyHom 46 19 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_19 (b : Fin 3) : PolyHom 46 19 :=
  ![polyRep46_19_0,PolyHom.zero 46 19,PolyHom.zero 46 19] b
theorem polyLiftFree46_19 : ∀ b : Fin 3, (polyLift46_19 b).freeBlock=basisInt (homKind 46 19) b := by decide
def polyRep46_20_0 : PolyHom 46 20 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_20 (b : Fin 3) : PolyHom 46 20 :=
  ![polyRep46_20_0,PolyHom.zero 46 20,PolyHom.zero 46 20] b
theorem polyLiftFree46_20 : ∀ b : Fin 3, (polyLift46_20 b).freeBlock=basisInt (homKind 46 20) b := by decide
def polyRep46_21_0 : PolyHom 46 21 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 4),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_21 (b : Fin 3) : PolyHom 46 21 :=
  ![polyRep46_21_0,PolyHom.zero 46 21,PolyHom.zero 46 21] b
theorem polyLiftFree46_21 : ∀ b : Fin 3, (polyLift46_21 b).freeBlock=basisInt (homKind 46 21) b := by decide
def polyRep46_22_0 : PolyHom 46 22 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_22 (b : Fin 3) : PolyHom 46 22 :=
  ![polyRep46_22_0,PolyHom.zero 46 22,PolyHom.zero 46 22] b
theorem polyLiftFree46_22 : ∀ b : Fin 3, (polyLift46_22 b).freeBlock=basisInt (homKind 46 22) b := by decide
def polyRep46_23_0 : PolyHom 46 23 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_23 (b : Fin 3) : PolyHom 46 23 :=
  ![polyRep46_23_0,PolyHom.zero 46 23,PolyHom.zero 46 23] b
theorem polyLiftFree46_23 : ∀ b : Fin 3, (polyLift46_23 b).freeBlock=basisInt (homKind 46 23) b := by decide
def polyRep46_24_0 : PolyHom 46 24 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 4),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep46_24_1 : PolyHom 46 24 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_24 (b : Fin 3) : PolyHom 46 24 :=
  ![polyRep46_24_0,polyRep46_24_1,PolyHom.zero 46 24] b
theorem polyLiftFree46_24 : ∀ b : Fin 3, (polyLift46_24 b).freeBlock=basisInt (homKind 46 24) b := by decide
def polyRep46_25_0 : PolyHom 46 25 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 4),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_25 (b : Fin 3) : PolyHom 46 25 :=
  ![polyRep46_25_0,PolyHom.zero 46 25,PolyHom.zero 46 25] b
theorem polyLiftFree46_25 : ∀ b : Fin 3, (polyLift46_25 b).freeBlock=basisInt (homKind 46 25) b := by decide
def polyRep46_26_0 : PolyHom 46 26 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep46_26_1 : PolyHom 46 26 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_26 (b : Fin 3) : PolyHom 46 26 :=
  ![polyRep46_26_0,polyRep46_26_1,PolyHom.zero 46 26] b
theorem polyLiftFree46_26 : ∀ b : Fin 3, (polyLift46_26 b).freeBlock=basisInt (homKind 46 26) b := by decide
def polyRep46_27_0 : PolyHom 46 27 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_27 (b : Fin 3) : PolyHom 46 27 :=
  ![polyRep46_27_0,PolyHom.zero 46 27,PolyHom.zero 46 27] b
theorem polyLiftFree46_27 : ∀ b : Fin 3, (polyLift46_27 b).freeBlock=basisInt (homKind 46 27) b := by decide
def polyRep46_28_0 : PolyHom 46 28 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_28 (b : Fin 3) : PolyHom 46 28 :=
  ![polyRep46_28_0,PolyHom.zero 46 28,PolyHom.zero 46 28] b
theorem polyLiftFree46_28 : ∀ b : Fin 3, (polyLift46_28 b).freeBlock=basisInt (homKind 46 28) b := by decide
def polyRep46_29_0 : PolyHom 46 29 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_29 (b : Fin 3) : PolyHom 46 29 :=
  ![polyRep46_29_0,PolyHom.zero 46 29,PolyHom.zero 46 29] b
theorem polyLiftFree46_29 : ∀ b : Fin 3, (polyLift46_29 b).freeBlock=basisInt (homKind 46 29) b := by decide
def polyRep46_30_0 : PolyHom 46 30 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 4),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep46_30_1 : PolyHom 46 30 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 2);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_30 (b : Fin 3) : PolyHom 46 30 :=
  ![polyRep46_30_0,polyRep46_30_1,PolyHom.zero 46 30] b
theorem polyLiftFree46_30 : ∀ b : Fin 3, (polyLift46_30 b).freeBlock=basisInt (homKind 46 30) b := by decide
def polyRep46_31_0 : PolyHom 46 31 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 4),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep46_31_1 : PolyHom 46 31 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_31 (b : Fin 3) : PolyHom 46 31 :=
  ![polyRep46_31_0,polyRep46_31_1,PolyHom.zero 46 31] b
theorem polyLiftFree46_31 : ∀ b : Fin 3, (polyLift46_31 b).freeBlock=basisInt (homKind 46 31) b := by decide
def polyRep46_32_0 : PolyHom 46 32 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep46_32_1 : PolyHom 46 32 where
  M := !![0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_32 (b : Fin 3) : PolyHom 46 32 :=
  ![polyRep46_32_0,polyRep46_32_1,PolyHom.zero 46 32] b
theorem polyLiftFree46_32 : ∀ b : Fin 3, (polyLift46_32 b).freeBlock=basisInt (homKind 46 32) b := by decide
def polyRep46_33_0 : PolyHom 46 33 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 4),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_33 (b : Fin 3) : PolyHom 46 33 :=
  ![polyRep46_33_0,PolyHom.zero 46 33,PolyHom.zero 46 33] b
theorem polyLiftFree46_33 : ∀ b : Fin 3, (polyLift46_33 b).freeBlock=basisInt (homKind 46 33) b := by decide
def polyRep46_34_0 : PolyHom 46 34 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_34 (b : Fin 3) : PolyHom 46 34 :=
  ![polyRep46_34_0,PolyHom.zero 46 34,PolyHom.zero 46 34] b
theorem polyLiftFree46_34 : ∀ b : Fin 3, (polyLift46_34 b).freeBlock=basisInt (homKind 46 34) b := by decide
def polyRep46_35_0 : PolyHom 46 35 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_35 (b : Fin 3) : PolyHom 46 35 :=
  ![polyRep46_35_0,PolyHom.zero 46 35,PolyHom.zero 46 35] b
theorem polyLiftFree46_35 : ∀ b : Fin 3, (polyLift46_35 b).freeBlock=basisInt (homKind 46 35) b := by decide
def polyRep46_36_0 : PolyHom 46 36 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_36 (b : Fin 3) : PolyHom 46 36 :=
  ![polyRep46_36_0,PolyHom.zero 46 36,PolyHom.zero 46 36] b
theorem polyLiftFree46_36 : ∀ b : Fin 3, (polyLift46_36 b).freeBlock=basisInt (homKind 46 36) b := by decide
def polyRep46_37_0 : PolyHom 46 37 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 4),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep46_37_1 : PolyHom 46 37 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 2);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_37 (b : Fin 3) : PolyHom 46 37 :=
  ![polyRep46_37_0,polyRep46_37_1,PolyHom.zero 46 37] b
theorem polyLiftFree46_37 : ∀ b : Fin 3, (polyLift46_37 b).freeBlock=basisInt (homKind 46 37) b := by decide
def polyRep46_38_0 : PolyHom 46 38 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep46_38_1 : PolyHom 46 38 where
  M := !![0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 2);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_38 (b : Fin 3) : PolyHom 46 38 :=
  ![polyRep46_38_0,polyRep46_38_1,PolyHom.zero 46 38] b
theorem polyLiftFree46_38 : ∀ b : Fin 3, (polyLift46_38 b).freeBlock=basisInt (homKind 46 38) b := by decide
def polyRep46_39_0 : PolyHom 46 39 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep46_39_1 : PolyHom 46 39 where
  M := !![0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_39 (b : Fin 3) : PolyHom 46 39 :=
  ![polyRep46_39_0,polyRep46_39_1,PolyHom.zero 46 39] b
theorem polyLiftFree46_39 : ∀ b : Fin 3, (polyLift46_39 b).freeBlock=basisInt (homKind 46 39) b := by decide
def polyRep46_40_0 : PolyHom 46 40 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 4),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep46_40_1 : PolyHom 46 40 where
  M := !![0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 2);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_40 (b : Fin 3) : PolyHom 46 40 :=
  ![polyRep46_40_0,polyRep46_40_1,PolyHom.zero 46 40] b
theorem polyLiftFree46_40 : ∀ b : Fin 3, (polyLift46_40 b).freeBlock=basisInt (homKind 46 40) b := by decide
def polyRep46_41_0 : PolyHom 46 41 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep46_41_1 : PolyHom 46 41 where
  M := !![0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_41 (b : Fin 3) : PolyHom 46 41 :=
  ![polyRep46_41_0,polyRep46_41_1,PolyHom.zero 46 41] b
theorem polyLiftFree46_41 : ∀ b : Fin 3, (polyLift46_41 b).freeBlock=basisInt (homKind 46 41) b := by decide
def polyRep46_42_0 : PolyHom 46 42 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 4),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep46_42_1 : PolyHom 46 42 where
  M := !![0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 2);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_42 (b : Fin 3) : PolyHom 46 42 :=
  ![polyRep46_42_0,polyRep46_42_1,PolyHom.zero 46 42] b
theorem polyLiftFree46_42 : ∀ b : Fin 3, (polyLift46_42 b).freeBlock=basisInt (homKind 46 42) b := by decide
def polyRep46_43_0 : PolyHom 46 43 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep46_43_1 : PolyHom 46 43 where
  M := !![0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 2);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_43 (b : Fin 3) : PolyHom 46 43 :=
  ![polyRep46_43_0,polyRep46_43_1,PolyHom.zero 46 43] b
theorem polyLiftFree46_43 : ∀ b : Fin 3, (polyLift46_43 b).freeBlock=basisInt (homKind 46 43) b := by decide
def polyRep46_44_0 : PolyHom 46 44 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 4),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep46_44_1 : PolyHom 46 44 where
  M := !![0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 2);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_44 (b : Fin 3) : PolyHom 46 44 :=
  ![polyRep46_44_0,polyRep46_44_1,PolyHom.zero 46 44] b
theorem polyLiftFree46_44 : ∀ b : Fin 3, (polyLift46_44 b).freeBlock=basisInt (homKind 46 44) b := by decide
def polyRep46_45_0 : PolyHom 46 45 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_45 (b : Fin 3) : PolyHom 46 45 :=
  ![polyRep46_45_0,PolyHom.zero 46 45,PolyHom.zero 46 45] b
theorem polyLiftFree46_45 : ∀ b : Fin 3, (polyLift46_45 b).freeBlock=basisInt (homKind 46 45) b := by decide
def polyRep46_46_0 : PolyHom 46 46 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift46_46 (b : Fin 3) : PolyHom 46 46 :=
  ![polyRep46_46_0,PolyHom.zero 46 46,PolyHom.zero 46 46] b
theorem polyLiftFree46_46 : ∀ b : Fin 3, (polyLift46_46 b).freeBlock=basisInt (homKind 46 46) b := by decide
def polyLiftRow46 (j : Fin 47) (b : Fin 3) : PolyHom 46 j :=
  match j with
  | ⟨0,_⟩ => polyLift46_0 b
  | ⟨1,_⟩ => polyLift46_1 b
  | ⟨2,_⟩ => polyLift46_2 b
  | ⟨3,_⟩ => polyLift46_3 b
  | ⟨4,_⟩ => polyLift46_4 b
  | ⟨5,_⟩ => polyLift46_5 b
  | ⟨6,_⟩ => polyLift46_6 b
  | ⟨7,_⟩ => polyLift46_7 b
  | ⟨8,_⟩ => polyLift46_8 b
  | ⟨9,_⟩ => polyLift46_9 b
  | ⟨10,_⟩ => polyLift46_10 b
  | ⟨11,_⟩ => polyLift46_11 b
  | ⟨12,_⟩ => polyLift46_12 b
  | ⟨13,_⟩ => polyLift46_13 b
  | ⟨14,_⟩ => polyLift46_14 b
  | ⟨15,_⟩ => polyLift46_15 b
  | ⟨16,_⟩ => polyLift46_16 b
  | ⟨17,_⟩ => polyLift46_17 b
  | ⟨18,_⟩ => polyLift46_18 b
  | ⟨19,_⟩ => polyLift46_19 b
  | ⟨20,_⟩ => polyLift46_20 b
  | ⟨21,_⟩ => polyLift46_21 b
  | ⟨22,_⟩ => polyLift46_22 b
  | ⟨23,_⟩ => polyLift46_23 b
  | ⟨24,_⟩ => polyLift46_24 b
  | ⟨25,_⟩ => polyLift46_25 b
  | ⟨26,_⟩ => polyLift46_26 b
  | ⟨27,_⟩ => polyLift46_27 b
  | ⟨28,_⟩ => polyLift46_28 b
  | ⟨29,_⟩ => polyLift46_29 b
  | ⟨30,_⟩ => polyLift46_30 b
  | ⟨31,_⟩ => polyLift46_31 b
  | ⟨32,_⟩ => polyLift46_32 b
  | ⟨33,_⟩ => polyLift46_33 b
  | ⟨34,_⟩ => polyLift46_34 b
  | ⟨35,_⟩ => polyLift46_35 b
  | ⟨36,_⟩ => polyLift46_36 b
  | ⟨37,_⟩ => polyLift46_37 b
  | ⟨38,_⟩ => polyLift46_38 b
  | ⟨39,_⟩ => polyLift46_39 b
  | ⟨40,_⟩ => polyLift46_40 b
  | ⟨41,_⟩ => polyLift46_41 b
  | ⟨42,_⟩ => polyLift46_42 b
  | ⟨43,_⟩ => polyLift46_43 b
  | ⟨44,_⟩ => polyLift46_44 b
  | ⟨45,_⟩ => polyLift46_45 b
  | ⟨46,_⟩ => polyLift46_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree46 (j : Fin 47) (b : Fin 3) : (polyLiftRow46 j b).freeBlock=basisInt (homKind 46 j) b := by
  fin_cases j
  · exact polyLiftFree46_0 b
  · exact polyLiftFree46_1 b
  · exact polyLiftFree46_2 b
  · exact polyLiftFree46_3 b
  · exact polyLiftFree46_4 b
  · exact polyLiftFree46_5 b
  · exact polyLiftFree46_6 b
  · exact polyLiftFree46_7 b
  · exact polyLiftFree46_8 b
  · exact polyLiftFree46_9 b
  · exact polyLiftFree46_10 b
  · exact polyLiftFree46_11 b
  · exact polyLiftFree46_12 b
  · exact polyLiftFree46_13 b
  · exact polyLiftFree46_14 b
  · exact polyLiftFree46_15 b
  · exact polyLiftFree46_16 b
  · exact polyLiftFree46_17 b
  · exact polyLiftFree46_18 b
  · exact polyLiftFree46_19 b
  · exact polyLiftFree46_20 b
  · exact polyLiftFree46_21 b
  · exact polyLiftFree46_22 b
  · exact polyLiftFree46_23 b
  · exact polyLiftFree46_24 b
  · exact polyLiftFree46_25 b
  · exact polyLiftFree46_26 b
  · exact polyLiftFree46_27 b
  · exact polyLiftFree46_28 b
  · exact polyLiftFree46_29 b
  · exact polyLiftFree46_30 b
  · exact polyLiftFree46_31 b
  · exact polyLiftFree46_32 b
  · exact polyLiftFree46_33 b
  · exact polyLiftFree46_34 b
  · exact polyLiftFree46_35 b
  · exact polyLiftFree46_36 b
  · exact polyLiftFree46_37 b
  · exact polyLiftFree46_38 b
  · exact polyLiftFree46_39 b
  · exact polyLiftFree46_40 b
  · exact polyLiftFree46_41 b
  · exact polyLiftFree46_42 b
  · exact polyLiftFree46_43 b
  · exact polyLiftFree46_44 b
  · exact polyLiftFree46_45 b
  · exact polyLiftFree46_46 b
end UniserialComputations.N6
