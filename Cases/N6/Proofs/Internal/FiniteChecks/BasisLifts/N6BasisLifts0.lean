import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyRep0_0_0 : PolyHom 0 0 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_0 (b : Fin 3) : PolyHom 0 0 :=
  ![polyRep0_0_0,PolyHom.zero 0 0,PolyHom.zero 0 0] b
theorem polyLiftFree0_0 : ∀ b : Fin 3, (polyLift0_0 b).freeBlock=basisInt (homKind 0 0) b := by decide
def polyRep0_1_0 : PolyHom 0 1 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_1 (b : Fin 3) : PolyHom 0 1 :=
  ![polyRep0_1_0,PolyHom.zero 0 1,PolyHom.zero 0 1] b
theorem polyLiftFree0_1 : ∀ b : Fin 3, (polyLift0_1 b).freeBlock=basisInt (homKind 0 1) b := by decide
def polyRep0_2_0 : PolyHom 0 2 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_2 (b : Fin 3) : PolyHom 0 2 :=
  ![polyRep0_2_0,PolyHom.zero 0 2,PolyHom.zero 0 2] b
theorem polyLiftFree0_2 : ∀ b : Fin 3, (polyLift0_2 b).freeBlock=basisInt (homKind 0 2) b := by decide
def polyRep0_3_0 : PolyHom 0 3 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_3 (b : Fin 3) : PolyHom 0 3 :=
  ![polyRep0_3_0,PolyHom.zero 0 3,PolyHom.zero 0 3] b
theorem polyLiftFree0_3 : ∀ b : Fin 3, (polyLift0_3 b).freeBlock=basisInt (homKind 0 3) b := by decide
def polyRep0_4_0 : PolyHom 0 4 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_4 (b : Fin 3) : PolyHom 0 4 :=
  ![polyRep0_4_0,PolyHom.zero 0 4,PolyHom.zero 0 4] b
theorem polyLiftFree0_4 : ∀ b : Fin 3, (polyLift0_4 b).freeBlock=basisInt (homKind 0 4) b := by decide
def polyRep0_5_0 : PolyHom 0 5 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_5 (b : Fin 3) : PolyHom 0 5 :=
  ![polyRep0_5_0,PolyHom.zero 0 5,PolyHom.zero 0 5] b
theorem polyLiftFree0_5 : ∀ b : Fin 3, (polyLift0_5 b).freeBlock=basisInt (homKind 0 5) b := by decide
def polyRep0_6_0 : PolyHom 0 6 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_6 (b : Fin 3) : PolyHom 0 6 :=
  ![polyRep0_6_0,PolyHom.zero 0 6,PolyHom.zero 0 6] b
theorem polyLiftFree0_6 : ∀ b : Fin 3, (polyLift0_6 b).freeBlock=basisInt (homKind 0 6) b := by decide
def polyRep0_7_0 : PolyHom 0 7 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_7 (b : Fin 3) : PolyHom 0 7 :=
  ![polyRep0_7_0,PolyHom.zero 0 7,PolyHom.zero 0 7] b
theorem polyLiftFree0_7 : ∀ b : Fin 3, (polyLift0_7 b).freeBlock=basisInt (homKind 0 7) b := by decide
def polyRep0_8_0 : PolyHom 0 8 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_8 (b : Fin 3) : PolyHom 0 8 :=
  ![polyRep0_8_0,PolyHom.zero 0 8,PolyHom.zero 0 8] b
theorem polyLiftFree0_8 : ∀ b : Fin 3, (polyLift0_8 b).freeBlock=basisInt (homKind 0 8) b := by decide
def polyRep0_9_0 : PolyHom 0 9 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_9 (b : Fin 3) : PolyHom 0 9 :=
  ![polyRep0_9_0,PolyHom.zero 0 9,PolyHom.zero 0 9] b
theorem polyLiftFree0_9 : ∀ b : Fin 3, (polyLift0_9 b).freeBlock=basisInt (homKind 0 9) b := by decide
def polyRep0_10_0 : PolyHom 0 10 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 4),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_10 (b : Fin 3) : PolyHom 0 10 :=
  ![polyRep0_10_0,PolyHom.zero 0 10,PolyHom.zero 0 10] b
theorem polyLiftFree0_10 : ∀ b : Fin 3, (polyLift0_10 b).freeBlock=basisInt (homKind 0 10) b := by decide
def polyRep0_11_0 : PolyHom 0 11 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_11 (b : Fin 3) : PolyHom 0 11 :=
  ![polyRep0_11_0,PolyHom.zero 0 11,PolyHom.zero 0 11] b
theorem polyLiftFree0_11 : ∀ b : Fin 3, (polyLift0_11 b).freeBlock=basisInt (homKind 0 11) b := by decide
def polyRep0_12_0 : PolyHom 0 12 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_12 (b : Fin 3) : PolyHom 0 12 :=
  ![polyRep0_12_0,PolyHom.zero 0 12,PolyHom.zero 0 12] b
theorem polyLiftFree0_12 : ∀ b : Fin 3, (polyLift0_12 b).freeBlock=basisInt (homKind 0 12) b := by decide
def polyRep0_13_0 : PolyHom 0 13 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_13 (b : Fin 3) : PolyHom 0 13 :=
  ![polyRep0_13_0,PolyHom.zero 0 13,PolyHom.zero 0 13] b
theorem polyLiftFree0_13 : ∀ b : Fin 3, (polyLift0_13 b).freeBlock=basisInt (homKind 0 13) b := by decide
def polyRep0_14_0 : PolyHom 0 14 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_14 (b : Fin 3) : PolyHom 0 14 :=
  ![polyRep0_14_0,PolyHom.zero 0 14,PolyHom.zero 0 14] b
theorem polyLiftFree0_14 : ∀ b : Fin 3, (polyLift0_14 b).freeBlock=basisInt (homKind 0 14) b := by decide
def polyRep0_15_0 : PolyHom 0 15 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_15 (b : Fin 3) : PolyHom 0 15 :=
  ![polyRep0_15_0,PolyHom.zero 0 15,PolyHom.zero 0 15] b
theorem polyLiftFree0_15 : ∀ b : Fin 3, (polyLift0_15 b).freeBlock=basisInt (homKind 0 15) b := by decide
def polyRep0_16_0 : PolyHom 0 16 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_16 (b : Fin 3) : PolyHom 0 16 :=
  ![polyRep0_16_0,PolyHom.zero 0 16,PolyHom.zero 0 16] b
theorem polyLiftFree0_16 : ∀ b : Fin 3, (polyLift0_16 b).freeBlock=basisInt (homKind 0 16) b := by decide
def polyRep0_17_0 : PolyHom 0 17 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_17 (b : Fin 3) : PolyHom 0 17 :=
  ![polyRep0_17_0,PolyHom.zero 0 17,PolyHom.zero 0 17] b
theorem polyLiftFree0_17 : ∀ b : Fin 3, (polyLift0_17 b).freeBlock=basisInt (homKind 0 17) b := by decide
def polyRep0_18_0 : PolyHom 0 18 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep0_18_1 : PolyHom 0 18 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_18 (b : Fin 3) : PolyHom 0 18 :=
  ![polyRep0_18_0,polyRep0_18_1,PolyHom.zero 0 18] b
theorem polyLiftFree0_18 : ∀ b : Fin 3, (polyLift0_18 b).freeBlock=basisInt (homKind 0 18) b := by decide
def polyRep0_19_0 : PolyHom 0 19 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_19 (b : Fin 3) : PolyHom 0 19 :=
  ![polyRep0_19_0,PolyHom.zero 0 19,PolyHom.zero 0 19] b
theorem polyLiftFree0_19 : ∀ b : Fin 3, (polyLift0_19 b).freeBlock=basisInt (homKind 0 19) b := by decide
def polyRep0_20_0 : PolyHom 0 20 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_20 (b : Fin 3) : PolyHom 0 20 :=
  ![polyRep0_20_0,PolyHom.zero 0 20,PolyHom.zero 0 20] b
theorem polyLiftFree0_20 : ∀ b : Fin 3, (polyLift0_20 b).freeBlock=basisInt (homKind 0 20) b := by decide
def polyRep0_21_0 : PolyHom 0 21 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_21 (b : Fin 3) : PolyHom 0 21 :=
  ![polyRep0_21_0,PolyHom.zero 0 21,PolyHom.zero 0 21] b
theorem polyLiftFree0_21 : ∀ b : Fin 3, (polyLift0_21 b).freeBlock=basisInt (homKind 0 21) b := by decide
def polyRep0_22_0 : PolyHom 0 22 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_22 (b : Fin 3) : PolyHom 0 22 :=
  ![polyRep0_22_0,PolyHom.zero 0 22,PolyHom.zero 0 22] b
theorem polyLiftFree0_22 : ∀ b : Fin 3, (polyLift0_22 b).freeBlock=basisInt (homKind 0 22) b := by decide
def polyRep0_23_0 : PolyHom 0 23 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_23 (b : Fin 3) : PolyHom 0 23 :=
  ![polyRep0_23_0,PolyHom.zero 0 23,PolyHom.zero 0 23] b
theorem polyLiftFree0_23 : ∀ b : Fin 3, (polyLift0_23 b).freeBlock=basisInt (homKind 0 23) b := by decide
def polyRep0_24_0 : PolyHom 0 24 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep0_24_1 : PolyHom 0 24 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_24 (b : Fin 3) : PolyHom 0 24 :=
  ![polyRep0_24_0,polyRep0_24_1,PolyHom.zero 0 24] b
theorem polyLiftFree0_24 : ∀ b : Fin 3, (polyLift0_24 b).freeBlock=basisInt (homKind 0 24) b := by decide
def polyRep0_25_0 : PolyHom 0 25 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_25 (b : Fin 3) : PolyHom 0 25 :=
  ![polyRep0_25_0,PolyHom.zero 0 25,PolyHom.zero 0 25] b
theorem polyLiftFree0_25 : ∀ b : Fin 3, (polyLift0_25 b).freeBlock=basisInt (homKind 0 25) b := by decide
def polyRep0_26_0 : PolyHom 0 26 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep0_26_1 : PolyHom 0 26 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_26 (b : Fin 3) : PolyHom 0 26 :=
  ![polyRep0_26_0,polyRep0_26_1,PolyHom.zero 0 26] b
theorem polyLiftFree0_26 : ∀ b : Fin 3, (polyLift0_26 b).freeBlock=basisInt (homKind 0 26) b := by decide
def polyRep0_27_0 : PolyHom 0 27 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_27 (b : Fin 3) : PolyHom 0 27 :=
  ![polyRep0_27_0,PolyHom.zero 0 27,PolyHom.zero 0 27] b
theorem polyLiftFree0_27 : ∀ b : Fin 3, (polyLift0_27 b).freeBlock=basisInt (homKind 0 27) b := by decide
def polyRep0_28_0 : PolyHom 0 28 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_28 (b : Fin 3) : PolyHom 0 28 :=
  ![polyRep0_28_0,PolyHom.zero 0 28,PolyHom.zero 0 28] b
theorem polyLiftFree0_28 : ∀ b : Fin 3, (polyLift0_28 b).freeBlock=basisInt (homKind 0 28) b := by decide
def polyRep0_29_0 : PolyHom 0 29 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_29 (b : Fin 3) : PolyHom 0 29 :=
  ![polyRep0_29_0,PolyHom.zero 0 29,PolyHom.zero 0 29] b
theorem polyLiftFree0_29 : ∀ b : Fin 3, (polyLift0_29 b).freeBlock=basisInt (homKind 0 29) b := by decide
def polyRep0_30_0 : PolyHom 0 30 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep0_30_1 : PolyHom 0 30 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_30 (b : Fin 3) : PolyHom 0 30 :=
  ![polyRep0_30_0,polyRep0_30_1,PolyHom.zero 0 30] b
theorem polyLiftFree0_30 : ∀ b : Fin 3, (polyLift0_30 b).freeBlock=basisInt (homKind 0 30) b := by decide
def polyRep0_31_0 : PolyHom 0 31 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep0_31_1 : PolyHom 0 31 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_31 (b : Fin 3) : PolyHom 0 31 :=
  ![polyRep0_31_0,polyRep0_31_1,PolyHom.zero 0 31] b
theorem polyLiftFree0_31 : ∀ b : Fin 3, (polyLift0_31 b).freeBlock=basisInt (homKind 0 31) b := by decide
def polyRep0_32_0 : PolyHom 0 32 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep0_32_1 : PolyHom 0 32 where
  M := !![0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_32 (b : Fin 3) : PolyHom 0 32 :=
  ![polyRep0_32_0,polyRep0_32_1,PolyHom.zero 0 32] b
theorem polyLiftFree0_32 : ∀ b : Fin 3, (polyLift0_32 b).freeBlock=basisInt (homKind 0 32) b := by decide
def polyRep0_33_0 : PolyHom 0 33 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_33 (b : Fin 3) : PolyHom 0 33 :=
  ![polyRep0_33_0,PolyHom.zero 0 33,PolyHom.zero 0 33] b
theorem polyLiftFree0_33 : ∀ b : Fin 3, (polyLift0_33 b).freeBlock=basisInt (homKind 0 33) b := by decide
def polyRep0_34_0 : PolyHom 0 34 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_34 (b : Fin 3) : PolyHom 0 34 :=
  ![polyRep0_34_0,PolyHom.zero 0 34,PolyHom.zero 0 34] b
theorem polyLiftFree0_34 : ∀ b : Fin 3, (polyLift0_34 b).freeBlock=basisInt (homKind 0 34) b := by decide
def polyRep0_35_0 : PolyHom 0 35 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_35 (b : Fin 3) : PolyHom 0 35 :=
  ![polyRep0_35_0,PolyHom.zero 0 35,PolyHom.zero 0 35] b
theorem polyLiftFree0_35 : ∀ b : Fin 3, (polyLift0_35 b).freeBlock=basisInt (homKind 0 35) b := by decide
def polyRep0_36_0 : PolyHom 0 36 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_36 (b : Fin 3) : PolyHom 0 36 :=
  ![polyRep0_36_0,PolyHom.zero 0 36,PolyHom.zero 0 36] b
theorem polyLiftFree0_36 : ∀ b : Fin 3, (polyLift0_36 b).freeBlock=basisInt (homKind 0 36) b := by decide
def polyRep0_37_0 : PolyHom 0 37 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep0_37_1 : PolyHom 0 37 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_37 (b : Fin 3) : PolyHom 0 37 :=
  ![polyRep0_37_0,polyRep0_37_1,PolyHom.zero 0 37] b
theorem polyLiftFree0_37 : ∀ b : Fin 3, (polyLift0_37 b).freeBlock=basisInt (homKind 0 37) b := by decide
def polyRep0_38_0 : PolyHom 0 38 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep0_38_1 : PolyHom 0 38 where
  M := !![0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_38 (b : Fin 3) : PolyHom 0 38 :=
  ![polyRep0_38_0,polyRep0_38_1,PolyHom.zero 0 38] b
theorem polyLiftFree0_38 : ∀ b : Fin 3, (polyLift0_38 b).freeBlock=basisInt (homKind 0 38) b := by decide
def polyRep0_39_0 : PolyHom 0 39 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep0_39_1 : PolyHom 0 39 where
  M := !![0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_39 (b : Fin 3) : PolyHom 0 39 :=
  ![polyRep0_39_0,polyRep0_39_1,PolyHom.zero 0 39] b
theorem polyLiftFree0_39 : ∀ b : Fin 3, (polyLift0_39 b).freeBlock=basisInt (homKind 0 39) b := by decide
def polyRep0_40_0 : PolyHom 0 40 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep0_40_1 : PolyHom 0 40 where
  M := !![0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_40 (b : Fin 3) : PolyHom 0 40 :=
  ![polyRep0_40_0,polyRep0_40_1,PolyHom.zero 0 40] b
theorem polyLiftFree0_40 : ∀ b : Fin 3, (polyLift0_40 b).freeBlock=basisInt (homKind 0 40) b := by decide
def polyRep0_41_0 : PolyHom 0 41 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep0_41_1 : PolyHom 0 41 where
  M := !![0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_41 (b : Fin 3) : PolyHom 0 41 :=
  ![polyRep0_41_0,polyRep0_41_1,PolyHom.zero 0 41] b
theorem polyLiftFree0_41 : ∀ b : Fin 3, (polyLift0_41 b).freeBlock=basisInt (homKind 0 41) b := by decide
def polyRep0_42_0 : PolyHom 0 42 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep0_42_1 : PolyHom 0 42 where
  M := !![0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_42 (b : Fin 3) : PolyHom 0 42 :=
  ![polyRep0_42_0,polyRep0_42_1,PolyHom.zero 0 42] b
theorem polyLiftFree0_42 : ∀ b : Fin 3, (polyLift0_42 b).freeBlock=basisInt (homKind 0 42) b := by decide
def polyRep0_43_0 : PolyHom 0 43 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep0_43_1 : PolyHom 0 43 where
  M := !![0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_43 (b : Fin 3) : PolyHom 0 43 :=
  ![polyRep0_43_0,polyRep0_43_1,PolyHom.zero 0 43] b
theorem polyLiftFree0_43 : ∀ b : Fin 3, (polyLift0_43 b).freeBlock=basisInt (homKind 0 43) b := by decide
def polyRep0_44_0 : PolyHom 0 44 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep0_44_1 : PolyHom 0 44 where
  M := !![0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_44 (b : Fin 3) : PolyHom 0 44 :=
  ![polyRep0_44_0,polyRep0_44_1,PolyHom.zero 0 44] b
theorem polyLiftFree0_44 : ∀ b : Fin 3, (polyLift0_44 b).freeBlock=basisInt (homKind 0 44) b := by decide
def polyRep0_45_0 : PolyHom 0 45 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift0_45 (b : Fin 3) : PolyHom 0 45 :=
  ![polyRep0_45_0,PolyHom.zero 0 45,PolyHom.zero 0 45] b
theorem polyLiftFree0_45 : ∀ b : Fin 3, (polyLift0_45 b).freeBlock=basisInt (homKind 0 45) b := by decide
def polyLift0_46 (b : Fin 3) : PolyHom 0 46 :=
  ![PolyHom.zero 0 46,PolyHom.zero 0 46,PolyHom.zero 0 46] b
theorem polyLiftFree0_46 : ∀ b : Fin 3, (polyLift0_46 b).freeBlock=basisInt (homKind 0 46) b := by decide
def polyLiftRow0 (j : Fin 47) (b : Fin 3) : PolyHom 0 j :=
  match j with
  | ⟨0,_⟩ => polyLift0_0 b
  | ⟨1,_⟩ => polyLift0_1 b
  | ⟨2,_⟩ => polyLift0_2 b
  | ⟨3,_⟩ => polyLift0_3 b
  | ⟨4,_⟩ => polyLift0_4 b
  | ⟨5,_⟩ => polyLift0_5 b
  | ⟨6,_⟩ => polyLift0_6 b
  | ⟨7,_⟩ => polyLift0_7 b
  | ⟨8,_⟩ => polyLift0_8 b
  | ⟨9,_⟩ => polyLift0_9 b
  | ⟨10,_⟩ => polyLift0_10 b
  | ⟨11,_⟩ => polyLift0_11 b
  | ⟨12,_⟩ => polyLift0_12 b
  | ⟨13,_⟩ => polyLift0_13 b
  | ⟨14,_⟩ => polyLift0_14 b
  | ⟨15,_⟩ => polyLift0_15 b
  | ⟨16,_⟩ => polyLift0_16 b
  | ⟨17,_⟩ => polyLift0_17 b
  | ⟨18,_⟩ => polyLift0_18 b
  | ⟨19,_⟩ => polyLift0_19 b
  | ⟨20,_⟩ => polyLift0_20 b
  | ⟨21,_⟩ => polyLift0_21 b
  | ⟨22,_⟩ => polyLift0_22 b
  | ⟨23,_⟩ => polyLift0_23 b
  | ⟨24,_⟩ => polyLift0_24 b
  | ⟨25,_⟩ => polyLift0_25 b
  | ⟨26,_⟩ => polyLift0_26 b
  | ⟨27,_⟩ => polyLift0_27 b
  | ⟨28,_⟩ => polyLift0_28 b
  | ⟨29,_⟩ => polyLift0_29 b
  | ⟨30,_⟩ => polyLift0_30 b
  | ⟨31,_⟩ => polyLift0_31 b
  | ⟨32,_⟩ => polyLift0_32 b
  | ⟨33,_⟩ => polyLift0_33 b
  | ⟨34,_⟩ => polyLift0_34 b
  | ⟨35,_⟩ => polyLift0_35 b
  | ⟨36,_⟩ => polyLift0_36 b
  | ⟨37,_⟩ => polyLift0_37 b
  | ⟨38,_⟩ => polyLift0_38 b
  | ⟨39,_⟩ => polyLift0_39 b
  | ⟨40,_⟩ => polyLift0_40 b
  | ⟨41,_⟩ => polyLift0_41 b
  | ⟨42,_⟩ => polyLift0_42 b
  | ⟨43,_⟩ => polyLift0_43 b
  | ⟨44,_⟩ => polyLift0_44 b
  | ⟨45,_⟩ => polyLift0_45 b
  | ⟨46,_⟩ => polyLift0_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree0 (j : Fin 47) (b : Fin 3) : (polyLiftRow0 j b).freeBlock=basisInt (homKind 0 j) b := by
  fin_cases j
  · exact polyLiftFree0_0 b
  · exact polyLiftFree0_1 b
  · exact polyLiftFree0_2 b
  · exact polyLiftFree0_3 b
  · exact polyLiftFree0_4 b
  · exact polyLiftFree0_5 b
  · exact polyLiftFree0_6 b
  · exact polyLiftFree0_7 b
  · exact polyLiftFree0_8 b
  · exact polyLiftFree0_9 b
  · exact polyLiftFree0_10 b
  · exact polyLiftFree0_11 b
  · exact polyLiftFree0_12 b
  · exact polyLiftFree0_13 b
  · exact polyLiftFree0_14 b
  · exact polyLiftFree0_15 b
  · exact polyLiftFree0_16 b
  · exact polyLiftFree0_17 b
  · exact polyLiftFree0_18 b
  · exact polyLiftFree0_19 b
  · exact polyLiftFree0_20 b
  · exact polyLiftFree0_21 b
  · exact polyLiftFree0_22 b
  · exact polyLiftFree0_23 b
  · exact polyLiftFree0_24 b
  · exact polyLiftFree0_25 b
  · exact polyLiftFree0_26 b
  · exact polyLiftFree0_27 b
  · exact polyLiftFree0_28 b
  · exact polyLiftFree0_29 b
  · exact polyLiftFree0_30 b
  · exact polyLiftFree0_31 b
  · exact polyLiftFree0_32 b
  · exact polyLiftFree0_33 b
  · exact polyLiftFree0_34 b
  · exact polyLiftFree0_35 b
  · exact polyLiftFree0_36 b
  · exact polyLiftFree0_37 b
  · exact polyLiftFree0_38 b
  · exact polyLiftFree0_39 b
  · exact polyLiftFree0_40 b
  · exact polyLiftFree0_41 b
  · exact polyLiftFree0_42 b
  · exact polyLiftFree0_43 b
  · exact polyLiftFree0_44 b
  · exact polyLiftFree0_45 b
  · exact polyLiftFree0_46 b
end UniserialComputations.N6
