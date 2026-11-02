import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift1_0 (b : Fin 3) : PolyHom 1 0 :=
  ![PolyHom.zero 1 0,PolyHom.zero 1 0,PolyHom.zero 1 0] b
theorem polyLiftFree1_0 : ∀ b : Fin 3, (polyLift1_0 b).freeBlock=basisInt (homKind 1 0) b := by decide
def polyRep1_1_0 : PolyHom 1 1 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_1 (b : Fin 3) : PolyHom 1 1 :=
  ![polyRep1_1_0,PolyHom.zero 1 1,PolyHom.zero 1 1] b
theorem polyLiftFree1_1 : ∀ b : Fin 3, (polyLift1_1 b).freeBlock=basisInt (homKind 1 1) b := by decide
def polyLift1_2 (b : Fin 3) : PolyHom 1 2 :=
  ![PolyHom.zero 1 2,PolyHom.zero 1 2,PolyHom.zero 1 2] b
theorem polyLiftFree1_2 : ∀ b : Fin 3, (polyLift1_2 b).freeBlock=basisInt (homKind 1 2) b := by decide
def polyRep1_3_0 : PolyHom 1 3 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_3 (b : Fin 3) : PolyHom 1 3 :=
  ![polyRep1_3_0,PolyHom.zero 1 3,PolyHom.zero 1 3] b
theorem polyLiftFree1_3 : ∀ b : Fin 3, (polyLift1_3 b).freeBlock=basisInt (homKind 1 3) b := by decide
def polyRep1_4_0 : PolyHom 1 4 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_4 (b : Fin 3) : PolyHom 1 4 :=
  ![polyRep1_4_0,PolyHom.zero 1 4,PolyHom.zero 1 4] b
theorem polyLiftFree1_4 : ∀ b : Fin 3, (polyLift1_4 b).freeBlock=basisInt (homKind 1 4) b := by decide
def polyLift1_5 (b : Fin 3) : PolyHom 1 5 :=
  ![PolyHom.zero 1 5,PolyHom.zero 1 5,PolyHom.zero 1 5] b
theorem polyLiftFree1_5 : ∀ b : Fin 3, (polyLift1_5 b).freeBlock=basisInt (homKind 1 5) b := by decide
def polyRep1_6_0 : PolyHom 1 6 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_6 (b : Fin 3) : PolyHom 1 6 :=
  ![polyRep1_6_0,PolyHom.zero 1 6,PolyHom.zero 1 6] b
theorem polyLiftFree1_6 : ∀ b : Fin 3, (polyLift1_6 b).freeBlock=basisInt (homKind 1 6) b := by decide
def polyRep1_7_0 : PolyHom 1 7 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_7 (b : Fin 3) : PolyHom 1 7 :=
  ![polyRep1_7_0,PolyHom.zero 1 7,PolyHom.zero 1 7] b
theorem polyLiftFree1_7 : ∀ b : Fin 3, (polyLift1_7 b).freeBlock=basisInt (homKind 1 7) b := by decide
def polyRep1_8_0 : PolyHom 1 8 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_8 (b : Fin 3) : PolyHom 1 8 :=
  ![polyRep1_8_0,PolyHom.zero 1 8,PolyHom.zero 1 8] b
theorem polyLiftFree1_8 : ∀ b : Fin 3, (polyLift1_8 b).freeBlock=basisInt (homKind 1 8) b := by decide
def polyLift1_9 (b : Fin 3) : PolyHom 1 9 :=
  ![PolyHom.zero 1 9,PolyHom.zero 1 9,PolyHom.zero 1 9] b
theorem polyLiftFree1_9 : ∀ b : Fin 3, (polyLift1_9 b).freeBlock=basisInt (homKind 1 9) b := by decide
def polyRep1_10_0 : PolyHom 1 10 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_10 (b : Fin 3) : PolyHom 1 10 :=
  ![polyRep1_10_0,PolyHom.zero 1 10,PolyHom.zero 1 10] b
theorem polyLiftFree1_10 : ∀ b : Fin 3, (polyLift1_10 b).freeBlock=basisInt (homKind 1 10) b := by decide
def polyRep1_11_0 : PolyHom 1 11 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_11 (b : Fin 3) : PolyHom 1 11 :=
  ![polyRep1_11_0,PolyHom.zero 1 11,PolyHom.zero 1 11] b
theorem polyLiftFree1_11 : ∀ b : Fin 3, (polyLift1_11 b).freeBlock=basisInt (homKind 1 11) b := by decide
def polyRep1_12_0 : PolyHom 1 12 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_12 (b : Fin 3) : PolyHom 1 12 :=
  ![polyRep1_12_0,PolyHom.zero 1 12,PolyHom.zero 1 12] b
theorem polyLiftFree1_12 : ∀ b : Fin 3, (polyLift1_12 b).freeBlock=basisInt (homKind 1 12) b := by decide
def polyRep1_13_0 : PolyHom 1 13 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_13 (b : Fin 3) : PolyHom 1 13 :=
  ![polyRep1_13_0,PolyHom.zero 1 13,PolyHom.zero 1 13] b
theorem polyLiftFree1_13 : ∀ b : Fin 3, (polyLift1_13 b).freeBlock=basisInt (homKind 1 13) b := by decide
def polyLift1_14 (b : Fin 3) : PolyHom 1 14 :=
  ![PolyHom.zero 1 14,PolyHom.zero 1 14,PolyHom.zero 1 14] b
theorem polyLiftFree1_14 : ∀ b : Fin 3, (polyLift1_14 b).freeBlock=basisInt (homKind 1 14) b := by decide
def polyRep1_15_0 : PolyHom 1 15 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_15 (b : Fin 3) : PolyHom 1 15 :=
  ![polyRep1_15_0,PolyHom.zero 1 15,PolyHom.zero 1 15] b
theorem polyLiftFree1_15 : ∀ b : Fin 3, (polyLift1_15 b).freeBlock=basisInt (homKind 1 15) b := by decide
def polyRep1_16_0 : PolyHom 1 16 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_16 (b : Fin 3) : PolyHom 1 16 :=
  ![polyRep1_16_0,PolyHom.zero 1 16,PolyHom.zero 1 16] b
theorem polyLiftFree1_16 : ∀ b : Fin 3, (polyLift1_16 b).freeBlock=basisInt (homKind 1 16) b := by decide
def polyRep1_17_0 : PolyHom 1 17 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_17 (b : Fin 3) : PolyHom 1 17 :=
  ![polyRep1_17_0,PolyHom.zero 1 17,PolyHom.zero 1 17] b
theorem polyLiftFree1_17 : ∀ b : Fin 3, (polyLift1_17 b).freeBlock=basisInt (homKind 1 17) b := by decide
def polyRep1_18_0 : PolyHom 1 18 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_18 (b : Fin 3) : PolyHom 1 18 :=
  ![polyRep1_18_0,PolyHom.zero 1 18,PolyHom.zero 1 18] b
theorem polyLiftFree1_18 : ∀ b : Fin 3, (polyLift1_18 b).freeBlock=basisInt (homKind 1 18) b := by decide
def polyRep1_19_0 : PolyHom 1 19 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_19 (b : Fin 3) : PolyHom 1 19 :=
  ![polyRep1_19_0,PolyHom.zero 1 19,PolyHom.zero 1 19] b
theorem polyLiftFree1_19 : ∀ b : Fin 3, (polyLift1_19 b).freeBlock=basisInt (homKind 1 19) b := by decide
def polyRep1_20_0 : PolyHom 1 20 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_20 (b : Fin 3) : PolyHom 1 20 :=
  ![polyRep1_20_0,PolyHom.zero 1 20,PolyHom.zero 1 20] b
theorem polyLiftFree1_20 : ∀ b : Fin 3, (polyLift1_20 b).freeBlock=basisInt (homKind 1 20) b := by decide
def polyRep1_21_0 : PolyHom 1 21 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_21 (b : Fin 3) : PolyHom 1 21 :=
  ![polyRep1_21_0,PolyHom.zero 1 21,PolyHom.zero 1 21] b
theorem polyLiftFree1_21 : ∀ b : Fin 3, (polyLift1_21 b).freeBlock=basisInt (homKind 1 21) b := by decide
def polyRep1_22_0 : PolyHom 1 22 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_22 (b : Fin 3) : PolyHom 1 22 :=
  ![polyRep1_22_0,PolyHom.zero 1 22,PolyHom.zero 1 22] b
theorem polyLiftFree1_22 : ∀ b : Fin 3, (polyLift1_22 b).freeBlock=basisInt (homKind 1 22) b := by decide
def polyRep1_23_0 : PolyHom 1 23 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_23 (b : Fin 3) : PolyHom 1 23 :=
  ![polyRep1_23_0,PolyHom.zero 1 23,PolyHom.zero 1 23] b
theorem polyLiftFree1_23 : ∀ b : Fin 3, (polyLift1_23 b).freeBlock=basisInt (homKind 1 23) b := by decide
def polyRep1_24_0 : PolyHom 1 24 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_24 (b : Fin 3) : PolyHom 1 24 :=
  ![polyRep1_24_0,PolyHom.zero 1 24,PolyHom.zero 1 24] b
theorem polyLiftFree1_24 : ∀ b : Fin 3, (polyLift1_24 b).freeBlock=basisInt (homKind 1 24) b := by decide
def polyRep1_25_0 : PolyHom 1 25 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_25 (b : Fin 3) : PolyHom 1 25 :=
  ![polyRep1_25_0,PolyHom.zero 1 25,PolyHom.zero 1 25] b
theorem polyLiftFree1_25 : ∀ b : Fin 3, (polyLift1_25 b).freeBlock=basisInt (homKind 1 25) b := by decide
def polyRep1_26_0 : PolyHom 1 26 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_26 (b : Fin 3) : PolyHom 1 26 :=
  ![polyRep1_26_0,PolyHom.zero 1 26,PolyHom.zero 1 26] b
theorem polyLiftFree1_26 : ∀ b : Fin 3, (polyLift1_26 b).freeBlock=basisInt (homKind 1 26) b := by decide
def polyRep1_27_0 : PolyHom 1 27 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_27 (b : Fin 3) : PolyHom 1 27 :=
  ![polyRep1_27_0,PolyHom.zero 1 27,PolyHom.zero 1 27] b
theorem polyLiftFree1_27 : ∀ b : Fin 3, (polyLift1_27 b).freeBlock=basisInt (homKind 1 27) b := by decide
def polyRep1_28_0 : PolyHom 1 28 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_28 (b : Fin 3) : PolyHom 1 28 :=
  ![polyRep1_28_0,PolyHom.zero 1 28,PolyHom.zero 1 28] b
theorem polyLiftFree1_28 : ∀ b : Fin 3, (polyLift1_28 b).freeBlock=basisInt (homKind 1 28) b := by decide
def polyRep1_29_0 : PolyHom 1 29 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_29 (b : Fin 3) : PolyHom 1 29 :=
  ![polyRep1_29_0,PolyHom.zero 1 29,PolyHom.zero 1 29] b
theorem polyLiftFree1_29 : ∀ b : Fin 3, (polyLift1_29 b).freeBlock=basisInt (homKind 1 29) b := by decide
def polyRep1_30_0 : PolyHom 1 30 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep1_30_1 : PolyHom 1 30 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_30 (b : Fin 3) : PolyHom 1 30 :=
  ![polyRep1_30_0,polyRep1_30_1,PolyHom.zero 1 30] b
theorem polyLiftFree1_30 : ∀ b : Fin 3, (polyLift1_30 b).freeBlock=basisInt (homKind 1 30) b := by decide
def polyRep1_31_0 : PolyHom 1 31 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_31 (b : Fin 3) : PolyHom 1 31 :=
  ![polyRep1_31_0,PolyHom.zero 1 31,PolyHom.zero 1 31] b
theorem polyLiftFree1_31 : ∀ b : Fin 3, (polyLift1_31 b).freeBlock=basisInt (homKind 1 31) b := by decide
def polyRep1_32_0 : PolyHom 1 32 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_32 (b : Fin 3) : PolyHom 1 32 :=
  ![polyRep1_32_0,PolyHom.zero 1 32,PolyHom.zero 1 32] b
theorem polyLiftFree1_32 : ∀ b : Fin 3, (polyLift1_32 b).freeBlock=basisInt (homKind 1 32) b := by decide
def polyRep1_33_0 : PolyHom 1 33 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_33 (b : Fin 3) : PolyHom 1 33 :=
  ![polyRep1_33_0,PolyHom.zero 1 33,PolyHom.zero 1 33] b
theorem polyLiftFree1_33 : ∀ b : Fin 3, (polyLift1_33 b).freeBlock=basisInt (homKind 1 33) b := by decide
def polyRep1_34_0 : PolyHom 1 34 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_34 (b : Fin 3) : PolyHom 1 34 :=
  ![polyRep1_34_0,PolyHom.zero 1 34,PolyHom.zero 1 34] b
theorem polyLiftFree1_34 : ∀ b : Fin 3, (polyLift1_34 b).freeBlock=basisInt (homKind 1 34) b := by decide
def polyRep1_35_0 : PolyHom 1 35 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_35 (b : Fin 3) : PolyHom 1 35 :=
  ![polyRep1_35_0,PolyHom.zero 1 35,PolyHom.zero 1 35] b
theorem polyLiftFree1_35 : ∀ b : Fin 3, (polyLift1_35 b).freeBlock=basisInt (homKind 1 35) b := by decide
def polyRep1_36_0 : PolyHom 1 36 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_36 (b : Fin 3) : PolyHom 1 36 :=
  ![polyRep1_36_0,PolyHom.zero 1 36,PolyHom.zero 1 36] b
theorem polyLiftFree1_36 : ∀ b : Fin 3, (polyLift1_36 b).freeBlock=basisInt (homKind 1 36) b := by decide
def polyRep1_37_0 : PolyHom 1 37 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep1_37_1 : PolyHom 1 37 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_37 (b : Fin 3) : PolyHom 1 37 :=
  ![polyRep1_37_0,polyRep1_37_1,PolyHom.zero 1 37] b
theorem polyLiftFree1_37 : ∀ b : Fin 3, (polyLift1_37 b).freeBlock=basisInt (homKind 1 37) b := by decide
def polyRep1_38_0 : PolyHom 1 38 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep1_38_1 : PolyHom 1 38 where
  M := !![0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_38 (b : Fin 3) : PolyHom 1 38 :=
  ![polyRep1_38_0,polyRep1_38_1,PolyHom.zero 1 38] b
theorem polyLiftFree1_38 : ∀ b : Fin 3, (polyLift1_38 b).freeBlock=basisInt (homKind 1 38) b := by decide
def polyRep1_39_0 : PolyHom 1 39 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_39 (b : Fin 3) : PolyHom 1 39 :=
  ![polyRep1_39_0,PolyHom.zero 1 39,PolyHom.zero 1 39] b
theorem polyLiftFree1_39 : ∀ b : Fin 3, (polyLift1_39 b).freeBlock=basisInt (homKind 1 39) b := by decide
def polyRep1_40_0 : PolyHom 1 40 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep1_40_1 : PolyHom 1 40 where
  M := !![0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_40 (b : Fin 3) : PolyHom 1 40 :=
  ![polyRep1_40_0,polyRep1_40_1,PolyHom.zero 1 40] b
theorem polyLiftFree1_40 : ∀ b : Fin 3, (polyLift1_40 b).freeBlock=basisInt (homKind 1 40) b := by decide
def polyRep1_41_0 : PolyHom 1 41 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_41 (b : Fin 3) : PolyHom 1 41 :=
  ![polyRep1_41_0,PolyHom.zero 1 41,PolyHom.zero 1 41] b
theorem polyLiftFree1_41 : ∀ b : Fin 3, (polyLift1_41 b).freeBlock=basisInt (homKind 1 41) b := by decide
def polyRep1_42_0 : PolyHom 1 42 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep1_42_1 : PolyHom 1 42 where
  M := !![0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_42 (b : Fin 3) : PolyHom 1 42 :=
  ![polyRep1_42_0,polyRep1_42_1,PolyHom.zero 1 42] b
theorem polyLiftFree1_42 : ∀ b : Fin 3, (polyLift1_42 b).freeBlock=basisInt (homKind 1 42) b := by decide
def polyRep1_43_0 : PolyHom 1 43 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep1_43_1 : PolyHom 1 43 where
  M := !![0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_43 (b : Fin 3) : PolyHom 1 43 :=
  ![polyRep1_43_0,polyRep1_43_1,PolyHom.zero 1 43] b
theorem polyLiftFree1_43 : ∀ b : Fin 3, (polyLift1_43 b).freeBlock=basisInt (homKind 1 43) b := by decide
def polyRep1_44_0 : PolyHom 1 44 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep1_44_1 : PolyHom 1 44 where
  M := !![0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_44 (b : Fin 3) : PolyHom 1 44 :=
  ![polyRep1_44_0,polyRep1_44_1,PolyHom.zero 1 44] b
theorem polyLiftFree1_44 : ∀ b : Fin 3, (polyLift1_44 b).freeBlock=basisInt (homKind 1 44) b := by decide
def polyRep1_45_0 : PolyHom 1 45 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift1_45 (b : Fin 3) : PolyHom 1 45 :=
  ![polyRep1_45_0,PolyHom.zero 1 45,PolyHom.zero 1 45] b
theorem polyLiftFree1_45 : ∀ b : Fin 3, (polyLift1_45 b).freeBlock=basisInt (homKind 1 45) b := by decide
def polyLift1_46 (b : Fin 3) : PolyHom 1 46 :=
  ![PolyHom.zero 1 46,PolyHom.zero 1 46,PolyHom.zero 1 46] b
theorem polyLiftFree1_46 : ∀ b : Fin 3, (polyLift1_46 b).freeBlock=basisInt (homKind 1 46) b := by decide
def polyLiftRow1 (j : Fin 47) (b : Fin 3) : PolyHom 1 j :=
  match j with
  | ⟨0,_⟩ => polyLift1_0 b
  | ⟨1,_⟩ => polyLift1_1 b
  | ⟨2,_⟩ => polyLift1_2 b
  | ⟨3,_⟩ => polyLift1_3 b
  | ⟨4,_⟩ => polyLift1_4 b
  | ⟨5,_⟩ => polyLift1_5 b
  | ⟨6,_⟩ => polyLift1_6 b
  | ⟨7,_⟩ => polyLift1_7 b
  | ⟨8,_⟩ => polyLift1_8 b
  | ⟨9,_⟩ => polyLift1_9 b
  | ⟨10,_⟩ => polyLift1_10 b
  | ⟨11,_⟩ => polyLift1_11 b
  | ⟨12,_⟩ => polyLift1_12 b
  | ⟨13,_⟩ => polyLift1_13 b
  | ⟨14,_⟩ => polyLift1_14 b
  | ⟨15,_⟩ => polyLift1_15 b
  | ⟨16,_⟩ => polyLift1_16 b
  | ⟨17,_⟩ => polyLift1_17 b
  | ⟨18,_⟩ => polyLift1_18 b
  | ⟨19,_⟩ => polyLift1_19 b
  | ⟨20,_⟩ => polyLift1_20 b
  | ⟨21,_⟩ => polyLift1_21 b
  | ⟨22,_⟩ => polyLift1_22 b
  | ⟨23,_⟩ => polyLift1_23 b
  | ⟨24,_⟩ => polyLift1_24 b
  | ⟨25,_⟩ => polyLift1_25 b
  | ⟨26,_⟩ => polyLift1_26 b
  | ⟨27,_⟩ => polyLift1_27 b
  | ⟨28,_⟩ => polyLift1_28 b
  | ⟨29,_⟩ => polyLift1_29 b
  | ⟨30,_⟩ => polyLift1_30 b
  | ⟨31,_⟩ => polyLift1_31 b
  | ⟨32,_⟩ => polyLift1_32 b
  | ⟨33,_⟩ => polyLift1_33 b
  | ⟨34,_⟩ => polyLift1_34 b
  | ⟨35,_⟩ => polyLift1_35 b
  | ⟨36,_⟩ => polyLift1_36 b
  | ⟨37,_⟩ => polyLift1_37 b
  | ⟨38,_⟩ => polyLift1_38 b
  | ⟨39,_⟩ => polyLift1_39 b
  | ⟨40,_⟩ => polyLift1_40 b
  | ⟨41,_⟩ => polyLift1_41 b
  | ⟨42,_⟩ => polyLift1_42 b
  | ⟨43,_⟩ => polyLift1_43 b
  | ⟨44,_⟩ => polyLift1_44 b
  | ⟨45,_⟩ => polyLift1_45 b
  | ⟨46,_⟩ => polyLift1_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree1 (j : Fin 47) (b : Fin 3) : (polyLiftRow1 j b).freeBlock=basisInt (homKind 1 j) b := by
  fin_cases j
  · exact polyLiftFree1_0 b
  · exact polyLiftFree1_1 b
  · exact polyLiftFree1_2 b
  · exact polyLiftFree1_3 b
  · exact polyLiftFree1_4 b
  · exact polyLiftFree1_5 b
  · exact polyLiftFree1_6 b
  · exact polyLiftFree1_7 b
  · exact polyLiftFree1_8 b
  · exact polyLiftFree1_9 b
  · exact polyLiftFree1_10 b
  · exact polyLiftFree1_11 b
  · exact polyLiftFree1_12 b
  · exact polyLiftFree1_13 b
  · exact polyLiftFree1_14 b
  · exact polyLiftFree1_15 b
  · exact polyLiftFree1_16 b
  · exact polyLiftFree1_17 b
  · exact polyLiftFree1_18 b
  · exact polyLiftFree1_19 b
  · exact polyLiftFree1_20 b
  · exact polyLiftFree1_21 b
  · exact polyLiftFree1_22 b
  · exact polyLiftFree1_23 b
  · exact polyLiftFree1_24 b
  · exact polyLiftFree1_25 b
  · exact polyLiftFree1_26 b
  · exact polyLiftFree1_27 b
  · exact polyLiftFree1_28 b
  · exact polyLiftFree1_29 b
  · exact polyLiftFree1_30 b
  · exact polyLiftFree1_31 b
  · exact polyLiftFree1_32 b
  · exact polyLiftFree1_33 b
  · exact polyLiftFree1_34 b
  · exact polyLiftFree1_35 b
  · exact polyLiftFree1_36 b
  · exact polyLiftFree1_37 b
  · exact polyLiftFree1_38 b
  · exact polyLiftFree1_39 b
  · exact polyLiftFree1_40 b
  · exact polyLiftFree1_41 b
  · exact polyLiftFree1_42 b
  · exact polyLiftFree1_43 b
  · exact polyLiftFree1_44 b
  · exact polyLiftFree1_45 b
  · exact polyLiftFree1_46 b
end UniserialComputations.N6
