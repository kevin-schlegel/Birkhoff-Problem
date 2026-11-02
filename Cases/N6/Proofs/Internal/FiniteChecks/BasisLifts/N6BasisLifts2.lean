import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift2_0 (b : Fin 3) : PolyHom 2 0 :=
  ![PolyHom.zero 2 0,PolyHom.zero 2 0,PolyHom.zero 2 0] b
theorem polyLiftFree2_0 : ∀ b : Fin 3, (polyLift2_0 b).freeBlock=basisInt (homKind 2 0) b := by decide
def polyRep2_1_0 : PolyHom 2 1 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_1 (b : Fin 3) : PolyHom 2 1 :=
  ![polyRep2_1_0,PolyHom.zero 2 1,PolyHom.zero 2 1] b
theorem polyLiftFree2_1 : ∀ b : Fin 3, (polyLift2_1 b).freeBlock=basisInt (homKind 2 1) b := by decide
def polyRep2_2_0 : PolyHom 2 2 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_2 (b : Fin 3) : PolyHom 2 2 :=
  ![polyRep2_2_0,PolyHom.zero 2 2,PolyHom.zero 2 2] b
theorem polyLiftFree2_2 : ∀ b : Fin 3, (polyLift2_2 b).freeBlock=basisInt (homKind 2 2) b := by decide
def polyRep2_3_0 : PolyHom 2 3 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_3 (b : Fin 3) : PolyHom 2 3 :=
  ![polyRep2_3_0,PolyHom.zero 2 3,PolyHom.zero 2 3] b
theorem polyLiftFree2_3 : ∀ b : Fin 3, (polyLift2_3 b).freeBlock=basisInt (homKind 2 3) b := by decide
def polyRep2_4_0 : PolyHom 2 4 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_4 (b : Fin 3) : PolyHom 2 4 :=
  ![polyRep2_4_0,PolyHom.zero 2 4,PolyHom.zero 2 4] b
theorem polyLiftFree2_4 : ∀ b : Fin 3, (polyLift2_4 b).freeBlock=basisInt (homKind 2 4) b := by decide
def polyRep2_5_0 : PolyHom 2 5 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_5 (b : Fin 3) : PolyHom 2 5 :=
  ![polyRep2_5_0,PolyHom.zero 2 5,PolyHom.zero 2 5] b
theorem polyLiftFree2_5 : ∀ b : Fin 3, (polyLift2_5 b).freeBlock=basisInt (homKind 2 5) b := by decide
def polyRep2_6_0 : PolyHom 2 6 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_6 (b : Fin 3) : PolyHom 2 6 :=
  ![polyRep2_6_0,PolyHom.zero 2 6,PolyHom.zero 2 6] b
theorem polyLiftFree2_6 : ∀ b : Fin 3, (polyLift2_6 b).freeBlock=basisInt (homKind 2 6) b := by decide
def polyRep2_7_0 : PolyHom 2 7 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_7 (b : Fin 3) : PolyHom 2 7 :=
  ![polyRep2_7_0,PolyHom.zero 2 7,PolyHom.zero 2 7] b
theorem polyLiftFree2_7 : ∀ b : Fin 3, (polyLift2_7 b).freeBlock=basisInt (homKind 2 7) b := by decide
def polyRep2_8_0 : PolyHom 2 8 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_8 (b : Fin 3) : PolyHom 2 8 :=
  ![polyRep2_8_0,PolyHom.zero 2 8,PolyHom.zero 2 8] b
theorem polyLiftFree2_8 : ∀ b : Fin 3, (polyLift2_8 b).freeBlock=basisInt (homKind 2 8) b := by decide
def polyRep2_9_0 : PolyHom 2 9 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_9 (b : Fin 3) : PolyHom 2 9 :=
  ![polyRep2_9_0,PolyHom.zero 2 9,PolyHom.zero 2 9] b
theorem polyLiftFree2_9 : ∀ b : Fin 3, (polyLift2_9 b).freeBlock=basisInt (homKind 2 9) b := by decide
def polyRep2_10_0 : PolyHom 2 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 4),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_10 (b : Fin 3) : PolyHom 2 10 :=
  ![polyRep2_10_0,PolyHom.zero 2 10,PolyHom.zero 2 10] b
theorem polyLiftFree2_10 : ∀ b : Fin 3, (polyLift2_10 b).freeBlock=basisInt (homKind 2 10) b := by decide
def polyRep2_11_0 : PolyHom 2 11 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_11 (b : Fin 3) : PolyHom 2 11 :=
  ![polyRep2_11_0,PolyHom.zero 2 11,PolyHom.zero 2 11] b
theorem polyLiftFree2_11 : ∀ b : Fin 3, (polyLift2_11 b).freeBlock=basisInt (homKind 2 11) b := by decide
def polyRep2_12_0 : PolyHom 2 12 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_12 (b : Fin 3) : PolyHom 2 12 :=
  ![polyRep2_12_0,PolyHom.zero 2 12,PolyHom.zero 2 12] b
theorem polyLiftFree2_12 : ∀ b : Fin 3, (polyLift2_12 b).freeBlock=basisInt (homKind 2 12) b := by decide
def polyRep2_13_0 : PolyHom 2 13 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_13 (b : Fin 3) : PolyHom 2 13 :=
  ![polyRep2_13_0,PolyHom.zero 2 13,PolyHom.zero 2 13] b
theorem polyLiftFree2_13 : ∀ b : Fin 3, (polyLift2_13 b).freeBlock=basisInt (homKind 2 13) b := by decide
def polyRep2_14_0 : PolyHom 2 14 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_14 (b : Fin 3) : PolyHom 2 14 :=
  ![polyRep2_14_0,PolyHom.zero 2 14,PolyHom.zero 2 14] b
theorem polyLiftFree2_14 : ∀ b : Fin 3, (polyLift2_14 b).freeBlock=basisInt (homKind 2 14) b := by decide
def polyRep2_15_0 : PolyHom 2 15 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_15 (b : Fin 3) : PolyHom 2 15 :=
  ![polyRep2_15_0,PolyHom.zero 2 15,PolyHom.zero 2 15] b
theorem polyLiftFree2_15 : ∀ b : Fin 3, (polyLift2_15 b).freeBlock=basisInt (homKind 2 15) b := by decide
def polyRep2_16_0 : PolyHom 2 16 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_16 (b : Fin 3) : PolyHom 2 16 :=
  ![polyRep2_16_0,PolyHom.zero 2 16,PolyHom.zero 2 16] b
theorem polyLiftFree2_16 : ∀ b : Fin 3, (polyLift2_16 b).freeBlock=basisInt (homKind 2 16) b := by decide
def polyRep2_17_0 : PolyHom 2 17 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_17 (b : Fin 3) : PolyHom 2 17 :=
  ![polyRep2_17_0,PolyHom.zero 2 17,PolyHom.zero 2 17] b
theorem polyLiftFree2_17 : ∀ b : Fin 3, (polyLift2_17 b).freeBlock=basisInt (homKind 2 17) b := by decide
def polyRep2_18_0 : PolyHom 2 18 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep2_18_1 : PolyHom 2 18 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_18 (b : Fin 3) : PolyHom 2 18 :=
  ![polyRep2_18_0,polyRep2_18_1,PolyHom.zero 2 18] b
theorem polyLiftFree2_18 : ∀ b : Fin 3, (polyLift2_18 b).freeBlock=basisInt (homKind 2 18) b := by decide
def polyRep2_19_0 : PolyHom 2 19 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_19 (b : Fin 3) : PolyHom 2 19 :=
  ![polyRep2_19_0,PolyHom.zero 2 19,PolyHom.zero 2 19] b
theorem polyLiftFree2_19 : ∀ b : Fin 3, (polyLift2_19 b).freeBlock=basisInt (homKind 2 19) b := by decide
def polyRep2_20_0 : PolyHom 2 20 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_20 (b : Fin 3) : PolyHom 2 20 :=
  ![polyRep2_20_0,PolyHom.zero 2 20,PolyHom.zero 2 20] b
theorem polyLiftFree2_20 : ∀ b : Fin 3, (polyLift2_20 b).freeBlock=basisInt (homKind 2 20) b := by decide
def polyRep2_21_0 : PolyHom 2 21 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_21 (b : Fin 3) : PolyHom 2 21 :=
  ![polyRep2_21_0,PolyHom.zero 2 21,PolyHom.zero 2 21] b
theorem polyLiftFree2_21 : ∀ b : Fin 3, (polyLift2_21 b).freeBlock=basisInt (homKind 2 21) b := by decide
def polyRep2_22_0 : PolyHom 2 22 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_22 (b : Fin 3) : PolyHom 2 22 :=
  ![polyRep2_22_0,PolyHom.zero 2 22,PolyHom.zero 2 22] b
theorem polyLiftFree2_22 : ∀ b : Fin 3, (polyLift2_22 b).freeBlock=basisInt (homKind 2 22) b := by decide
def polyRep2_23_0 : PolyHom 2 23 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_23 (b : Fin 3) : PolyHom 2 23 :=
  ![polyRep2_23_0,PolyHom.zero 2 23,PolyHom.zero 2 23] b
theorem polyLiftFree2_23 : ∀ b : Fin 3, (polyLift2_23 b).freeBlock=basisInt (homKind 2 23) b := by decide
def polyRep2_24_0 : PolyHom 2 24 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep2_24_1 : PolyHom 2 24 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_24 (b : Fin 3) : PolyHom 2 24 :=
  ![polyRep2_24_0,polyRep2_24_1,PolyHom.zero 2 24] b
theorem polyLiftFree2_24 : ∀ b : Fin 3, (polyLift2_24 b).freeBlock=basisInt (homKind 2 24) b := by decide
def polyRep2_25_0 : PolyHom 2 25 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_25 (b : Fin 3) : PolyHom 2 25 :=
  ![polyRep2_25_0,PolyHom.zero 2 25,PolyHom.zero 2 25] b
theorem polyLiftFree2_25 : ∀ b : Fin 3, (polyLift2_25 b).freeBlock=basisInt (homKind 2 25) b := by decide
def polyRep2_26_0 : PolyHom 2 26 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep2_26_1 : PolyHom 2 26 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_26 (b : Fin 3) : PolyHom 2 26 :=
  ![polyRep2_26_0,polyRep2_26_1,PolyHom.zero 2 26] b
theorem polyLiftFree2_26 : ∀ b : Fin 3, (polyLift2_26 b).freeBlock=basisInt (homKind 2 26) b := by decide
def polyRep2_27_0 : PolyHom 2 27 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_27 (b : Fin 3) : PolyHom 2 27 :=
  ![polyRep2_27_0,PolyHom.zero 2 27,PolyHom.zero 2 27] b
theorem polyLiftFree2_27 : ∀ b : Fin 3, (polyLift2_27 b).freeBlock=basisInt (homKind 2 27) b := by decide
def polyRep2_28_0 : PolyHom 2 28 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_28 (b : Fin 3) : PolyHom 2 28 :=
  ![polyRep2_28_0,PolyHom.zero 2 28,PolyHom.zero 2 28] b
theorem polyLiftFree2_28 : ∀ b : Fin 3, (polyLift2_28 b).freeBlock=basisInt (homKind 2 28) b := by decide
def polyRep2_29_0 : PolyHom 2 29 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_29 (b : Fin 3) : PolyHom 2 29 :=
  ![polyRep2_29_0,PolyHom.zero 2 29,PolyHom.zero 2 29] b
theorem polyLiftFree2_29 : ∀ b : Fin 3, (polyLift2_29 b).freeBlock=basisInt (homKind 2 29) b := by decide
def polyRep2_30_0 : PolyHom 2 30 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep2_30_1 : PolyHom 2 30 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_30 (b : Fin 3) : PolyHom 2 30 :=
  ![polyRep2_30_0,polyRep2_30_1,PolyHom.zero 2 30] b
theorem polyLiftFree2_30 : ∀ b : Fin 3, (polyLift2_30 b).freeBlock=basisInt (homKind 2 30) b := by decide
def polyRep2_31_0 : PolyHom 2 31 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep2_31_1 : PolyHom 2 31 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_31 (b : Fin 3) : PolyHom 2 31 :=
  ![polyRep2_31_0,polyRep2_31_1,PolyHom.zero 2 31] b
theorem polyLiftFree2_31 : ∀ b : Fin 3, (polyLift2_31 b).freeBlock=basisInt (homKind 2 31) b := by decide
def polyRep2_32_0 : PolyHom 2 32 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep2_32_1 : PolyHom 2 32 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_32 (b : Fin 3) : PolyHom 2 32 :=
  ![polyRep2_32_0,polyRep2_32_1,PolyHom.zero 2 32] b
theorem polyLiftFree2_32 : ∀ b : Fin 3, (polyLift2_32 b).freeBlock=basisInt (homKind 2 32) b := by decide
def polyRep2_33_0 : PolyHom 2 33 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_33 (b : Fin 3) : PolyHom 2 33 :=
  ![polyRep2_33_0,PolyHom.zero 2 33,PolyHom.zero 2 33] b
theorem polyLiftFree2_33 : ∀ b : Fin 3, (polyLift2_33 b).freeBlock=basisInt (homKind 2 33) b := by decide
def polyRep2_34_0 : PolyHom 2 34 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_34 (b : Fin 3) : PolyHom 2 34 :=
  ![polyRep2_34_0,PolyHom.zero 2 34,PolyHom.zero 2 34] b
theorem polyLiftFree2_34 : ∀ b : Fin 3, (polyLift2_34 b).freeBlock=basisInt (homKind 2 34) b := by decide
def polyRep2_35_0 : PolyHom 2 35 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_35 (b : Fin 3) : PolyHom 2 35 :=
  ![polyRep2_35_0,PolyHom.zero 2 35,PolyHom.zero 2 35] b
theorem polyLiftFree2_35 : ∀ b : Fin 3, (polyLift2_35 b).freeBlock=basisInt (homKind 2 35) b := by decide
def polyRep2_36_0 : PolyHom 2 36 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_36 (b : Fin 3) : PolyHom 2 36 :=
  ![polyRep2_36_0,PolyHom.zero 2 36,PolyHom.zero 2 36] b
theorem polyLiftFree2_36 : ∀ b : Fin 3, (polyLift2_36 b).freeBlock=basisInt (homKind 2 36) b := by decide
def polyRep2_37_0 : PolyHom 2 37 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep2_37_1 : PolyHom 2 37 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_37 (b : Fin 3) : PolyHom 2 37 :=
  ![polyRep2_37_0,polyRep2_37_1,PolyHom.zero 2 37] b
theorem polyLiftFree2_37 : ∀ b : Fin 3, (polyLift2_37 b).freeBlock=basisInt (homKind 2 37) b := by decide
def polyRep2_38_0 : PolyHom 2 38 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep2_38_1 : PolyHom 2 38 where
  M := !![0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_38 (b : Fin 3) : PolyHom 2 38 :=
  ![polyRep2_38_0,polyRep2_38_1,PolyHom.zero 2 38] b
theorem polyLiftFree2_38 : ∀ b : Fin 3, (polyLift2_38 b).freeBlock=basisInt (homKind 2 38) b := by decide
def polyRep2_39_0 : PolyHom 2 39 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep2_39_1 : PolyHom 2 39 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_39 (b : Fin 3) : PolyHom 2 39 :=
  ![polyRep2_39_0,polyRep2_39_1,PolyHom.zero 2 39] b
theorem polyLiftFree2_39 : ∀ b : Fin 3, (polyLift2_39 b).freeBlock=basisInt (homKind 2 39) b := by decide
def polyRep2_40_0 : PolyHom 2 40 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep2_40_1 : PolyHom 2 40 where
  M := !![0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_40 (b : Fin 3) : PolyHom 2 40 :=
  ![polyRep2_40_0,polyRep2_40_1,PolyHom.zero 2 40] b
theorem polyLiftFree2_40 : ∀ b : Fin 3, (polyLift2_40 b).freeBlock=basisInt (homKind 2 40) b := by decide
def polyRep2_41_0 : PolyHom 2 41 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep2_41_1 : PolyHom 2 41 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_41 (b : Fin 3) : PolyHom 2 41 :=
  ![polyRep2_41_0,polyRep2_41_1,PolyHom.zero 2 41] b
theorem polyLiftFree2_41 : ∀ b : Fin 3, (polyLift2_41 b).freeBlock=basisInt (homKind 2 41) b := by decide
def polyRep2_42_0 : PolyHom 2 42 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep2_42_1 : PolyHom 2 42 where
  M := !![0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_42 (b : Fin 3) : PolyHom 2 42 :=
  ![polyRep2_42_0,polyRep2_42_1,PolyHom.zero 2 42] b
theorem polyLiftFree2_42 : ∀ b : Fin 3, (polyLift2_42 b).freeBlock=basisInt (homKind 2 42) b := by decide
def polyRep2_43_0 : PolyHom 2 43 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep2_43_1 : PolyHom 2 43 where
  M := !![0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_43 (b : Fin 3) : PolyHom 2 43 :=
  ![polyRep2_43_0,polyRep2_43_1,PolyHom.zero 2 43] b
theorem polyLiftFree2_43 : ∀ b : Fin 3, (polyLift2_43 b).freeBlock=basisInt (homKind 2 43) b := by decide
def polyRep2_44_0 : PolyHom 2 44 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep2_44_1 : PolyHom 2 44 where
  M := !![0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_44 (b : Fin 3) : PolyHom 2 44 :=
  ![polyRep2_44_0,polyRep2_44_1,PolyHom.zero 2 44] b
theorem polyLiftFree2_44 : ∀ b : Fin 3, (polyLift2_44 b).freeBlock=basisInt (homKind 2 44) b := by decide
def polyRep2_45_0 : PolyHom 2 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift2_45 (b : Fin 3) : PolyHom 2 45 :=
  ![polyRep2_45_0,PolyHom.zero 2 45,PolyHom.zero 2 45] b
theorem polyLiftFree2_45 : ∀ b : Fin 3, (polyLift2_45 b).freeBlock=basisInt (homKind 2 45) b := by decide
def polyLift2_46 (b : Fin 3) : PolyHom 2 46 :=
  ![PolyHom.zero 2 46,PolyHom.zero 2 46,PolyHom.zero 2 46] b
theorem polyLiftFree2_46 : ∀ b : Fin 3, (polyLift2_46 b).freeBlock=basisInt (homKind 2 46) b := by decide
def polyLiftRow2 (j : Fin 47) (b : Fin 3) : PolyHom 2 j :=
  match j with
  | ⟨0,_⟩ => polyLift2_0 b
  | ⟨1,_⟩ => polyLift2_1 b
  | ⟨2,_⟩ => polyLift2_2 b
  | ⟨3,_⟩ => polyLift2_3 b
  | ⟨4,_⟩ => polyLift2_4 b
  | ⟨5,_⟩ => polyLift2_5 b
  | ⟨6,_⟩ => polyLift2_6 b
  | ⟨7,_⟩ => polyLift2_7 b
  | ⟨8,_⟩ => polyLift2_8 b
  | ⟨9,_⟩ => polyLift2_9 b
  | ⟨10,_⟩ => polyLift2_10 b
  | ⟨11,_⟩ => polyLift2_11 b
  | ⟨12,_⟩ => polyLift2_12 b
  | ⟨13,_⟩ => polyLift2_13 b
  | ⟨14,_⟩ => polyLift2_14 b
  | ⟨15,_⟩ => polyLift2_15 b
  | ⟨16,_⟩ => polyLift2_16 b
  | ⟨17,_⟩ => polyLift2_17 b
  | ⟨18,_⟩ => polyLift2_18 b
  | ⟨19,_⟩ => polyLift2_19 b
  | ⟨20,_⟩ => polyLift2_20 b
  | ⟨21,_⟩ => polyLift2_21 b
  | ⟨22,_⟩ => polyLift2_22 b
  | ⟨23,_⟩ => polyLift2_23 b
  | ⟨24,_⟩ => polyLift2_24 b
  | ⟨25,_⟩ => polyLift2_25 b
  | ⟨26,_⟩ => polyLift2_26 b
  | ⟨27,_⟩ => polyLift2_27 b
  | ⟨28,_⟩ => polyLift2_28 b
  | ⟨29,_⟩ => polyLift2_29 b
  | ⟨30,_⟩ => polyLift2_30 b
  | ⟨31,_⟩ => polyLift2_31 b
  | ⟨32,_⟩ => polyLift2_32 b
  | ⟨33,_⟩ => polyLift2_33 b
  | ⟨34,_⟩ => polyLift2_34 b
  | ⟨35,_⟩ => polyLift2_35 b
  | ⟨36,_⟩ => polyLift2_36 b
  | ⟨37,_⟩ => polyLift2_37 b
  | ⟨38,_⟩ => polyLift2_38 b
  | ⟨39,_⟩ => polyLift2_39 b
  | ⟨40,_⟩ => polyLift2_40 b
  | ⟨41,_⟩ => polyLift2_41 b
  | ⟨42,_⟩ => polyLift2_42 b
  | ⟨43,_⟩ => polyLift2_43 b
  | ⟨44,_⟩ => polyLift2_44 b
  | ⟨45,_⟩ => polyLift2_45 b
  | ⟨46,_⟩ => polyLift2_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree2 (j : Fin 47) (b : Fin 3) : (polyLiftRow2 j b).freeBlock=basisInt (homKind 2 j) b := by
  fin_cases j
  · exact polyLiftFree2_0 b
  · exact polyLiftFree2_1 b
  · exact polyLiftFree2_2 b
  · exact polyLiftFree2_3 b
  · exact polyLiftFree2_4 b
  · exact polyLiftFree2_5 b
  · exact polyLiftFree2_6 b
  · exact polyLiftFree2_7 b
  · exact polyLiftFree2_8 b
  · exact polyLiftFree2_9 b
  · exact polyLiftFree2_10 b
  · exact polyLiftFree2_11 b
  · exact polyLiftFree2_12 b
  · exact polyLiftFree2_13 b
  · exact polyLiftFree2_14 b
  · exact polyLiftFree2_15 b
  · exact polyLiftFree2_16 b
  · exact polyLiftFree2_17 b
  · exact polyLiftFree2_18 b
  · exact polyLiftFree2_19 b
  · exact polyLiftFree2_20 b
  · exact polyLiftFree2_21 b
  · exact polyLiftFree2_22 b
  · exact polyLiftFree2_23 b
  · exact polyLiftFree2_24 b
  · exact polyLiftFree2_25 b
  · exact polyLiftFree2_26 b
  · exact polyLiftFree2_27 b
  · exact polyLiftFree2_28 b
  · exact polyLiftFree2_29 b
  · exact polyLiftFree2_30 b
  · exact polyLiftFree2_31 b
  · exact polyLiftFree2_32 b
  · exact polyLiftFree2_33 b
  · exact polyLiftFree2_34 b
  · exact polyLiftFree2_35 b
  · exact polyLiftFree2_36 b
  · exact polyLiftFree2_37 b
  · exact polyLiftFree2_38 b
  · exact polyLiftFree2_39 b
  · exact polyLiftFree2_40 b
  · exact polyLiftFree2_41 b
  · exact polyLiftFree2_42 b
  · exact polyLiftFree2_43 b
  · exact polyLiftFree2_44 b
  · exact polyLiftFree2_45 b
  · exact polyLiftFree2_46 b
end UniserialComputations.N6
