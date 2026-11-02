import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift15_0 (b : Fin 3) : PolyHom 15 0 :=
  ![PolyHom.zero 15 0,PolyHom.zero 15 0,PolyHom.zero 15 0] b
theorem polyLiftFree15_0 : ∀ b : Fin 3, (polyLift15_0 b).freeBlock=basisInt (homKind 15 0) b := by decide
def polyLift15_1 (b : Fin 3) : PolyHom 15 1 :=
  ![PolyHom.zero 15 1,PolyHom.zero 15 1,PolyHom.zero 15 1] b
theorem polyLiftFree15_1 : ∀ b : Fin 3, (polyLift15_1 b).freeBlock=basisInt (homKind 15 1) b := by decide
def polyLift15_2 (b : Fin 3) : PolyHom 15 2 :=
  ![PolyHom.zero 15 2,PolyHom.zero 15 2,PolyHom.zero 15 2] b
theorem polyLiftFree15_2 : ∀ b : Fin 3, (polyLift15_2 b).freeBlock=basisInt (homKind 15 2) b := by decide
def polyRep15_3_0 : PolyHom 15 3 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_3 (b : Fin 3) : PolyHom 15 3 :=
  ![polyRep15_3_0,PolyHom.zero 15 3,PolyHom.zero 15 3] b
theorem polyLiftFree15_3 : ∀ b : Fin 3, (polyLift15_3 b).freeBlock=basisInt (homKind 15 3) b := by decide
def polyRep15_4_0 : PolyHom 15 4 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_4 (b : Fin 3) : PolyHom 15 4 :=
  ![polyRep15_4_0,PolyHom.zero 15 4,PolyHom.zero 15 4] b
theorem polyLiftFree15_4 : ∀ b : Fin 3, (polyLift15_4 b).freeBlock=basisInt (homKind 15 4) b := by decide
def polyLift15_5 (b : Fin 3) : PolyHom 15 5 :=
  ![PolyHom.zero 15 5,PolyHom.zero 15 5,PolyHom.zero 15 5] b
theorem polyLiftFree15_5 : ∀ b : Fin 3, (polyLift15_5 b).freeBlock=basisInt (homKind 15 5) b := by decide
def polyRep15_6_0 : PolyHom 15 6 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_6 (b : Fin 3) : PolyHom 15 6 :=
  ![polyRep15_6_0,PolyHom.zero 15 6,PolyHom.zero 15 6] b
theorem polyLiftFree15_6 : ∀ b : Fin 3, (polyLift15_6 b).freeBlock=basisInt (homKind 15 6) b := by decide
def polyRep15_7_0 : PolyHom 15 7 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_7 (b : Fin 3) : PolyHom 15 7 :=
  ![polyRep15_7_0,PolyHom.zero 15 7,PolyHom.zero 15 7] b
theorem polyLiftFree15_7 : ∀ b : Fin 3, (polyLift15_7 b).freeBlock=basisInt (homKind 15 7) b := by decide
def polyRep15_8_0 : PolyHom 15 8 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_8 (b : Fin 3) : PolyHom 15 8 :=
  ![polyRep15_8_0,PolyHom.zero 15 8,PolyHom.zero 15 8] b
theorem polyLiftFree15_8 : ∀ b : Fin 3, (polyLift15_8 b).freeBlock=basisInt (homKind 15 8) b := by decide
def polyLift15_9 (b : Fin 3) : PolyHom 15 9 :=
  ![PolyHom.zero 15 9,PolyHom.zero 15 9,PolyHom.zero 15 9] b
theorem polyLiftFree15_9 : ∀ b : Fin 3, (polyLift15_9 b).freeBlock=basisInt (homKind 15 9) b := by decide
def polyRep15_10_0 : PolyHom 15 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_10 (b : Fin 3) : PolyHom 15 10 :=
  ![polyRep15_10_0,PolyHom.zero 15 10,PolyHom.zero 15 10] b
theorem polyLiftFree15_10 : ∀ b : Fin 3, (polyLift15_10 b).freeBlock=basisInt (homKind 15 10) b := by decide
def polyRep15_11_0 : PolyHom 15 11 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_11 (b : Fin 3) : PolyHom 15 11 :=
  ![polyRep15_11_0,PolyHom.zero 15 11,PolyHom.zero 15 11] b
theorem polyLiftFree15_11 : ∀ b : Fin 3, (polyLift15_11 b).freeBlock=basisInt (homKind 15 11) b := by decide
def polyRep15_12_0 : PolyHom 15 12 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_12 (b : Fin 3) : PolyHom 15 12 :=
  ![polyRep15_12_0,PolyHom.zero 15 12,PolyHom.zero 15 12] b
theorem polyLiftFree15_12 : ∀ b : Fin 3, (polyLift15_12 b).freeBlock=basisInt (homKind 15 12) b := by decide
def polyRep15_13_0 : PolyHom 15 13 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_13 (b : Fin 3) : PolyHom 15 13 :=
  ![polyRep15_13_0,PolyHom.zero 15 13,PolyHom.zero 15 13] b
theorem polyLiftFree15_13 : ∀ b : Fin 3, (polyLift15_13 b).freeBlock=basisInt (homKind 15 13) b := by decide
def polyLift15_14 (b : Fin 3) : PolyHom 15 14 :=
  ![PolyHom.zero 15 14,PolyHom.zero 15 14,PolyHom.zero 15 14] b
theorem polyLiftFree15_14 : ∀ b : Fin 3, (polyLift15_14 b).freeBlock=basisInt (homKind 15 14) b := by decide
def polyRep15_15_0 : PolyHom 15 15 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_15 (b : Fin 3) : PolyHom 15 15 :=
  ![polyRep15_15_0,PolyHom.zero 15 15,PolyHom.zero 15 15] b
theorem polyLiftFree15_15 : ∀ b : Fin 3, (polyLift15_15 b).freeBlock=basisInt (homKind 15 15) b := by decide
def polyRep15_16_0 : PolyHom 15 16 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_16 (b : Fin 3) : PolyHom 15 16 :=
  ![polyRep15_16_0,PolyHom.zero 15 16,PolyHom.zero 15 16] b
theorem polyLiftFree15_16 : ∀ b : Fin 3, (polyLift15_16 b).freeBlock=basisInt (homKind 15 16) b := by decide
def polyRep15_17_0 : PolyHom 15 17 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_17 (b : Fin 3) : PolyHom 15 17 :=
  ![polyRep15_17_0,PolyHom.zero 15 17,PolyHom.zero 15 17] b
theorem polyLiftFree15_17 : ∀ b : Fin 3, (polyLift15_17 b).freeBlock=basisInt (homKind 15 17) b := by decide
def polyRep15_18_0 : PolyHom 15 18 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_18 (b : Fin 3) : PolyHom 15 18 :=
  ![polyRep15_18_0,PolyHom.zero 15 18,PolyHom.zero 15 18] b
theorem polyLiftFree15_18 : ∀ b : Fin 3, (polyLift15_18 b).freeBlock=basisInt (homKind 15 18) b := by decide
def polyRep15_19_0 : PolyHom 15 19 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_19 (b : Fin 3) : PolyHom 15 19 :=
  ![polyRep15_19_0,PolyHom.zero 15 19,PolyHom.zero 15 19] b
theorem polyLiftFree15_19 : ∀ b : Fin 3, (polyLift15_19 b).freeBlock=basisInt (homKind 15 19) b := by decide
def polyRep15_20_0 : PolyHom 15 20 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_20 (b : Fin 3) : PolyHom 15 20 :=
  ![polyRep15_20_0,PolyHom.zero 15 20,PolyHom.zero 15 20] b
theorem polyLiftFree15_20 : ∀ b : Fin 3, (polyLift15_20 b).freeBlock=basisInt (homKind 15 20) b := by decide
def polyRep15_21_0 : PolyHom 15 21 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_21 (b : Fin 3) : PolyHom 15 21 :=
  ![polyRep15_21_0,PolyHom.zero 15 21,PolyHom.zero 15 21] b
theorem polyLiftFree15_21 : ∀ b : Fin 3, (polyLift15_21 b).freeBlock=basisInt (homKind 15 21) b := by decide
def polyRep15_22_0 : PolyHom 15 22 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_22 (b : Fin 3) : PolyHom 15 22 :=
  ![polyRep15_22_0,PolyHom.zero 15 22,PolyHom.zero 15 22] b
theorem polyLiftFree15_22 : ∀ b : Fin 3, (polyLift15_22 b).freeBlock=basisInt (homKind 15 22) b := by decide
def polyRep15_23_0 : PolyHom 15 23 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_23 (b : Fin 3) : PolyHom 15 23 :=
  ![polyRep15_23_0,PolyHom.zero 15 23,PolyHom.zero 15 23] b
theorem polyLiftFree15_23 : ∀ b : Fin 3, (polyLift15_23 b).freeBlock=basisInt (homKind 15 23) b := by decide
def polyRep15_24_0 : PolyHom 15 24 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_24 (b : Fin 3) : PolyHom 15 24 :=
  ![polyRep15_24_0,PolyHom.zero 15 24,PolyHom.zero 15 24] b
theorem polyLiftFree15_24 : ∀ b : Fin 3, (polyLift15_24 b).freeBlock=basisInt (homKind 15 24) b := by decide
def polyRep15_25_0 : PolyHom 15 25 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_25 (b : Fin 3) : PolyHom 15 25 :=
  ![polyRep15_25_0,PolyHom.zero 15 25,PolyHom.zero 15 25] b
theorem polyLiftFree15_25 : ∀ b : Fin 3, (polyLift15_25 b).freeBlock=basisInt (homKind 15 25) b := by decide
def polyRep15_26_0 : PolyHom 15 26 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_26 (b : Fin 3) : PolyHom 15 26 :=
  ![polyRep15_26_0,PolyHom.zero 15 26,PolyHom.zero 15 26] b
theorem polyLiftFree15_26 : ∀ b : Fin 3, (polyLift15_26 b).freeBlock=basisInt (homKind 15 26) b := by decide
def polyRep15_27_0 : PolyHom 15 27 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_27 (b : Fin 3) : PolyHom 15 27 :=
  ![polyRep15_27_0,PolyHom.zero 15 27,PolyHom.zero 15 27] b
theorem polyLiftFree15_27 : ∀ b : Fin 3, (polyLift15_27 b).freeBlock=basisInt (homKind 15 27) b := by decide
def polyRep15_28_0 : PolyHom 15 28 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_28 (b : Fin 3) : PolyHom 15 28 :=
  ![polyRep15_28_0,PolyHom.zero 15 28,PolyHom.zero 15 28] b
theorem polyLiftFree15_28 : ∀ b : Fin 3, (polyLift15_28 b).freeBlock=basisInt (homKind 15 28) b := by decide
def polyRep15_29_0 : PolyHom 15 29 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_29 (b : Fin 3) : PolyHom 15 29 :=
  ![polyRep15_29_0,PolyHom.zero 15 29,PolyHom.zero 15 29] b
theorem polyLiftFree15_29 : ∀ b : Fin 3, (polyLift15_29 b).freeBlock=basisInt (homKind 15 29) b := by decide
def polyRep15_30_0 : PolyHom 15 30 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep15_30_1 : PolyHom 15 30 where
  M := !![(mono6 (1) 1),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_30 (b : Fin 3) : PolyHom 15 30 :=
  ![polyRep15_30_0,polyRep15_30_1,PolyHom.zero 15 30] b
theorem polyLiftFree15_30 : ∀ b : Fin 3, (polyLift15_30 b).freeBlock=basisInt (homKind 15 30) b := by decide
def polyRep15_31_0 : PolyHom 15 31 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_31 (b : Fin 3) : PolyHom 15 31 :=
  ![polyRep15_31_0,PolyHom.zero 15 31,PolyHom.zero 15 31] b
theorem polyLiftFree15_31 : ∀ b : Fin 3, (polyLift15_31 b).freeBlock=basisInt (homKind 15 31) b := by decide
def polyRep15_32_0 : PolyHom 15 32 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_32 (b : Fin 3) : PolyHom 15 32 :=
  ![polyRep15_32_0,PolyHom.zero 15 32,PolyHom.zero 15 32] b
theorem polyLiftFree15_32 : ∀ b : Fin 3, (polyLift15_32 b).freeBlock=basisInt (homKind 15 32) b := by decide
def polyRep15_33_0 : PolyHom 15 33 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_33 (b : Fin 3) : PolyHom 15 33 :=
  ![polyRep15_33_0,PolyHom.zero 15 33,PolyHom.zero 15 33] b
theorem polyLiftFree15_33 : ∀ b : Fin 3, (polyLift15_33 b).freeBlock=basisInt (homKind 15 33) b := by decide
def polyRep15_34_0 : PolyHom 15 34 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_34 (b : Fin 3) : PolyHom 15 34 :=
  ![polyRep15_34_0,PolyHom.zero 15 34,PolyHom.zero 15 34] b
theorem polyLiftFree15_34 : ∀ b : Fin 3, (polyLift15_34 b).freeBlock=basisInt (homKind 15 34) b := by decide
def polyRep15_35_0 : PolyHom 15 35 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_35 (b : Fin 3) : PolyHom 15 35 :=
  ![polyRep15_35_0,PolyHom.zero 15 35,PolyHom.zero 15 35] b
theorem polyLiftFree15_35 : ∀ b : Fin 3, (polyLift15_35 b).freeBlock=basisInt (homKind 15 35) b := by decide
def polyRep15_36_0 : PolyHom 15 36 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_36 (b : Fin 3) : PolyHom 15 36 :=
  ![polyRep15_36_0,PolyHom.zero 15 36,PolyHom.zero 15 36] b
theorem polyLiftFree15_36 : ∀ b : Fin 3, (polyLift15_36 b).freeBlock=basisInt (homKind 15 36) b := by decide
def polyRep15_37_0 : PolyHom 15 37 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep15_37_1 : PolyHom 15 37 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_37 (b : Fin 3) : PolyHom 15 37 :=
  ![polyRep15_37_0,polyRep15_37_1,PolyHom.zero 15 37] b
theorem polyLiftFree15_37 : ∀ b : Fin 3, (polyLift15_37 b).freeBlock=basisInt (homKind 15 37) b := by decide
def polyRep15_38_0 : PolyHom 15 38 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep15_38_1 : PolyHom 15 38 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_38 (b : Fin 3) : PolyHom 15 38 :=
  ![polyRep15_38_0,polyRep15_38_1,PolyHom.zero 15 38] b
theorem polyLiftFree15_38 : ∀ b : Fin 3, (polyLift15_38 b).freeBlock=basisInt (homKind 15 38) b := by decide
def polyRep15_39_0 : PolyHom 15 39 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_39 (b : Fin 3) : PolyHom 15 39 :=
  ![polyRep15_39_0,PolyHom.zero 15 39,PolyHom.zero 15 39] b
theorem polyLiftFree15_39 : ∀ b : Fin 3, (polyLift15_39 b).freeBlock=basisInt (homKind 15 39) b := by decide
def polyRep15_40_0 : PolyHom 15 40 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep15_40_1 : PolyHom 15 40 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_40 (b : Fin 3) : PolyHom 15 40 :=
  ![polyRep15_40_0,polyRep15_40_1,PolyHom.zero 15 40] b
theorem polyLiftFree15_40 : ∀ b : Fin 3, (polyLift15_40 b).freeBlock=basisInt (homKind 15 40) b := by decide
def polyRep15_41_0 : PolyHom 15 41 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_41 (b : Fin 3) : PolyHom 15 41 :=
  ![polyRep15_41_0,PolyHom.zero 15 41,PolyHom.zero 15 41] b
theorem polyLiftFree15_41 : ∀ b : Fin 3, (polyLift15_41 b).freeBlock=basisInt (homKind 15 41) b := by decide
def polyRep15_42_0 : PolyHom 15 42 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep15_42_1 : PolyHom 15 42 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_42 (b : Fin 3) : PolyHom 15 42 :=
  ![polyRep15_42_0,polyRep15_42_1,PolyHom.zero 15 42] b
theorem polyLiftFree15_42 : ∀ b : Fin 3, (polyLift15_42 b).freeBlock=basisInt (homKind 15 42) b := by decide
def polyRep15_43_0 : PolyHom 15 43 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep15_43_1 : PolyHom 15 43 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_43 (b : Fin 3) : PolyHom 15 43 :=
  ![polyRep15_43_0,polyRep15_43_1,PolyHom.zero 15 43] b
theorem polyLiftFree15_43 : ∀ b : Fin 3, (polyLift15_43 b).freeBlock=basisInt (homKind 15 43) b := by decide
def polyRep15_44_0 : PolyHom 15 44 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep15_44_1 : PolyHom 15 44 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_44 (b : Fin 3) : PolyHom 15 44 :=
  ![polyRep15_44_0,polyRep15_44_1,PolyHom.zero 15 44] b
theorem polyLiftFree15_44 : ∀ b : Fin 3, (polyLift15_44 b).freeBlock=basisInt (homKind 15 44) b := by decide
def polyRep15_45_0 : PolyHom 15 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift15_45 (b : Fin 3) : PolyHom 15 45 :=
  ![polyRep15_45_0,PolyHom.zero 15 45,PolyHom.zero 15 45] b
theorem polyLiftFree15_45 : ∀ b : Fin 3, (polyLift15_45 b).freeBlock=basisInt (homKind 15 45) b := by decide
def polyLift15_46 (b : Fin 3) : PolyHom 15 46 :=
  ![PolyHom.zero 15 46,PolyHom.zero 15 46,PolyHom.zero 15 46] b
theorem polyLiftFree15_46 : ∀ b : Fin 3, (polyLift15_46 b).freeBlock=basisInt (homKind 15 46) b := by decide
def polyLiftRow15 (j : Fin 47) (b : Fin 3) : PolyHom 15 j :=
  match j with
  | ⟨0,_⟩ => polyLift15_0 b
  | ⟨1,_⟩ => polyLift15_1 b
  | ⟨2,_⟩ => polyLift15_2 b
  | ⟨3,_⟩ => polyLift15_3 b
  | ⟨4,_⟩ => polyLift15_4 b
  | ⟨5,_⟩ => polyLift15_5 b
  | ⟨6,_⟩ => polyLift15_6 b
  | ⟨7,_⟩ => polyLift15_7 b
  | ⟨8,_⟩ => polyLift15_8 b
  | ⟨9,_⟩ => polyLift15_9 b
  | ⟨10,_⟩ => polyLift15_10 b
  | ⟨11,_⟩ => polyLift15_11 b
  | ⟨12,_⟩ => polyLift15_12 b
  | ⟨13,_⟩ => polyLift15_13 b
  | ⟨14,_⟩ => polyLift15_14 b
  | ⟨15,_⟩ => polyLift15_15 b
  | ⟨16,_⟩ => polyLift15_16 b
  | ⟨17,_⟩ => polyLift15_17 b
  | ⟨18,_⟩ => polyLift15_18 b
  | ⟨19,_⟩ => polyLift15_19 b
  | ⟨20,_⟩ => polyLift15_20 b
  | ⟨21,_⟩ => polyLift15_21 b
  | ⟨22,_⟩ => polyLift15_22 b
  | ⟨23,_⟩ => polyLift15_23 b
  | ⟨24,_⟩ => polyLift15_24 b
  | ⟨25,_⟩ => polyLift15_25 b
  | ⟨26,_⟩ => polyLift15_26 b
  | ⟨27,_⟩ => polyLift15_27 b
  | ⟨28,_⟩ => polyLift15_28 b
  | ⟨29,_⟩ => polyLift15_29 b
  | ⟨30,_⟩ => polyLift15_30 b
  | ⟨31,_⟩ => polyLift15_31 b
  | ⟨32,_⟩ => polyLift15_32 b
  | ⟨33,_⟩ => polyLift15_33 b
  | ⟨34,_⟩ => polyLift15_34 b
  | ⟨35,_⟩ => polyLift15_35 b
  | ⟨36,_⟩ => polyLift15_36 b
  | ⟨37,_⟩ => polyLift15_37 b
  | ⟨38,_⟩ => polyLift15_38 b
  | ⟨39,_⟩ => polyLift15_39 b
  | ⟨40,_⟩ => polyLift15_40 b
  | ⟨41,_⟩ => polyLift15_41 b
  | ⟨42,_⟩ => polyLift15_42 b
  | ⟨43,_⟩ => polyLift15_43 b
  | ⟨44,_⟩ => polyLift15_44 b
  | ⟨45,_⟩ => polyLift15_45 b
  | ⟨46,_⟩ => polyLift15_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree15 (j : Fin 47) (b : Fin 3) : (polyLiftRow15 j b).freeBlock=basisInt (homKind 15 j) b := by
  fin_cases j
  · exact polyLiftFree15_0 b
  · exact polyLiftFree15_1 b
  · exact polyLiftFree15_2 b
  · exact polyLiftFree15_3 b
  · exact polyLiftFree15_4 b
  · exact polyLiftFree15_5 b
  · exact polyLiftFree15_6 b
  · exact polyLiftFree15_7 b
  · exact polyLiftFree15_8 b
  · exact polyLiftFree15_9 b
  · exact polyLiftFree15_10 b
  · exact polyLiftFree15_11 b
  · exact polyLiftFree15_12 b
  · exact polyLiftFree15_13 b
  · exact polyLiftFree15_14 b
  · exact polyLiftFree15_15 b
  · exact polyLiftFree15_16 b
  · exact polyLiftFree15_17 b
  · exact polyLiftFree15_18 b
  · exact polyLiftFree15_19 b
  · exact polyLiftFree15_20 b
  · exact polyLiftFree15_21 b
  · exact polyLiftFree15_22 b
  · exact polyLiftFree15_23 b
  · exact polyLiftFree15_24 b
  · exact polyLiftFree15_25 b
  · exact polyLiftFree15_26 b
  · exact polyLiftFree15_27 b
  · exact polyLiftFree15_28 b
  · exact polyLiftFree15_29 b
  · exact polyLiftFree15_30 b
  · exact polyLiftFree15_31 b
  · exact polyLiftFree15_32 b
  · exact polyLiftFree15_33 b
  · exact polyLiftFree15_34 b
  · exact polyLiftFree15_35 b
  · exact polyLiftFree15_36 b
  · exact polyLiftFree15_37 b
  · exact polyLiftFree15_38 b
  · exact polyLiftFree15_39 b
  · exact polyLiftFree15_40 b
  · exact polyLiftFree15_41 b
  · exact polyLiftFree15_42 b
  · exact polyLiftFree15_43 b
  · exact polyLiftFree15_44 b
  · exact polyLiftFree15_45 b
  · exact polyLiftFree15_46 b
end UniserialComputations.N6
