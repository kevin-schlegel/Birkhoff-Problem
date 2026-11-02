import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift40_0 (b : Fin 3) : PolyHom 40 0 :=
  ![PolyHom.zero 40 0,PolyHom.zero 40 0,PolyHom.zero 40 0] b
theorem polyLiftFree40_0 : ∀ b : Fin 3, (polyLift40_0 b).freeBlock=basisInt (homKind 40 0) b := by decide
def polyLift40_1 (b : Fin 3) : PolyHom 40 1 :=
  ![PolyHom.zero 40 1,PolyHom.zero 40 1,PolyHom.zero 40 1] b
theorem polyLiftFree40_1 : ∀ b : Fin 3, (polyLift40_1 b).freeBlock=basisInt (homKind 40 1) b := by decide
def polyLift40_2 (b : Fin 3) : PolyHom 40 2 :=
  ![PolyHom.zero 40 2,PolyHom.zero 40 2,PolyHom.zero 40 2] b
theorem polyLiftFree40_2 : ∀ b : Fin 3, (polyLift40_2 b).freeBlock=basisInt (homKind 40 2) b := by decide
def polyRep40_3_0 : PolyHom 40 3 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (-1) 1),0,0,0;(mono6 (1) 0),0,0,0]
  U := !![(mono6 (-1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_3 (b : Fin 3) : PolyHom 40 3 :=
  ![polyRep40_3_0,PolyHom.zero 40 3,PolyHom.zero 40 3] b
theorem polyLiftFree40_3 : ∀ b : Fin 3, (polyLift40_3 b).freeBlock=basisInt (homKind 40 3) b := by decide
def polyLift40_4 (b : Fin 3) : PolyHom 40 4 :=
  ![PolyHom.zero 40 4,PolyHom.zero 40 4,PolyHom.zero 40 4] b
theorem polyLiftFree40_4 : ∀ b : Fin 3, (polyLift40_4 b).freeBlock=basisInt (homKind 40 4) b := by decide
def polyLift40_5 (b : Fin 3) : PolyHom 40 5 :=
  ![PolyHom.zero 40 5,PolyHom.zero 40 5,PolyHom.zero 40 5] b
theorem polyLiftFree40_5 : ∀ b : Fin 3, (polyLift40_5 b).freeBlock=basisInt (homKind 40 5) b := by decide
def polyRep40_6_0 : PolyHom 40 6 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_6 (b : Fin 3) : PolyHom 40 6 :=
  ![polyRep40_6_0,PolyHom.zero 40 6,PolyHom.zero 40 6] b
theorem polyLiftFree40_6 : ∀ b : Fin 3, (polyLift40_6 b).freeBlock=basisInt (homKind 40 6) b := by decide
def polyRep40_7_0 : PolyHom 40 7 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_7 (b : Fin 3) : PolyHom 40 7 :=
  ![polyRep40_7_0,PolyHom.zero 40 7,PolyHom.zero 40 7] b
theorem polyLiftFree40_7 : ∀ b : Fin 3, (polyLift40_7 b).freeBlock=basisInt (homKind 40 7) b := by decide
def polyRep40_8_0 : PolyHom 40 8 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_8 (b : Fin 3) : PolyHom 40 8 :=
  ![polyRep40_8_0,PolyHom.zero 40 8,PolyHom.zero 40 8] b
theorem polyLiftFree40_8 : ∀ b : Fin 3, (polyLift40_8 b).freeBlock=basisInt (homKind 40 8) b := by decide
def polyLift40_9 (b : Fin 3) : PolyHom 40 9 :=
  ![PolyHom.zero 40 9,PolyHom.zero 40 9,PolyHom.zero 40 9] b
theorem polyLiftFree40_9 : ∀ b : Fin 3, (polyLift40_9 b).freeBlock=basisInt (homKind 40 9) b := by decide
def polyRep40_10_0 : PolyHom 40 10 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep40_10_1 : PolyHom 40 10 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_10 (b : Fin 3) : PolyHom 40 10 :=
  ![polyRep40_10_0,polyRep40_10_1,PolyHom.zero 40 10] b
theorem polyLiftFree40_10 : ∀ b : Fin 3, (polyLift40_10 b).freeBlock=basisInt (homKind 40 10) b := by decide
def polyRep40_11_0 : PolyHom 40 11 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep40_11_1 : PolyHom 40 11 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_11 (b : Fin 3) : PolyHom 40 11 :=
  ![polyRep40_11_0,polyRep40_11_1,PolyHom.zero 40 11] b
theorem polyLiftFree40_11 : ∀ b : Fin 3, (polyLift40_11 b).freeBlock=basisInt (homKind 40 11) b := by decide
def polyRep40_12_0 : PolyHom 40 12 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_12 (b : Fin 3) : PolyHom 40 12 :=
  ![polyRep40_12_0,PolyHom.zero 40 12,PolyHom.zero 40 12] b
theorem polyLiftFree40_12 : ∀ b : Fin 3, (polyLift40_12 b).freeBlock=basisInt (homKind 40 12) b := by decide
def polyRep40_13_0 : PolyHom 40 13 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_13 (b : Fin 3) : PolyHom 40 13 :=
  ![polyRep40_13_0,PolyHom.zero 40 13,PolyHom.zero 40 13] b
theorem polyLiftFree40_13 : ∀ b : Fin 3, (polyLift40_13 b).freeBlock=basisInt (homKind 40 13) b := by decide
def polyLift40_14 (b : Fin 3) : PolyHom 40 14 :=
  ![PolyHom.zero 40 14,PolyHom.zero 40 14,PolyHom.zero 40 14] b
theorem polyLiftFree40_14 : ∀ b : Fin 3, (polyLift40_14 b).freeBlock=basisInt (homKind 40 14) b := by decide
def polyLift40_15 (b : Fin 3) : PolyHom 40 15 :=
  ![PolyHom.zero 40 15,PolyHom.zero 40 15,PolyHom.zero 40 15] b
theorem polyLiftFree40_15 : ∀ b : Fin 3, (polyLift40_15 b).freeBlock=basisInt (homKind 40 15) b := by decide
def polyRep40_16_0 : PolyHom 40 16 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_16 (b : Fin 3) : PolyHom 40 16 :=
  ![polyRep40_16_0,PolyHom.zero 40 16,PolyHom.zero 40 16] b
theorem polyLiftFree40_16 : ∀ b : Fin 3, (polyLift40_16 b).freeBlock=basisInt (homKind 40 16) b := by decide
def polyLift40_17 (b : Fin 3) : PolyHom 40 17 :=
  ![PolyHom.zero 40 17,PolyHom.zero 40 17,PolyHom.zero 40 17] b
theorem polyLiftFree40_17 : ∀ b : Fin 3, (polyLift40_17 b).freeBlock=basisInt (homKind 40 17) b := by decide
def polyRep40_18_0 : PolyHom 40 18 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_18 (b : Fin 3) : PolyHom 40 18 :=
  ![polyRep40_18_0,PolyHom.zero 40 18,PolyHom.zero 40 18] b
theorem polyLiftFree40_18 : ∀ b : Fin 3, (polyLift40_18 b).freeBlock=basisInt (homKind 40 18) b := by decide
def polyRep40_19_0 : PolyHom 40 19 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_19 (b : Fin 3) : PolyHom 40 19 :=
  ![polyRep40_19_0,PolyHom.zero 40 19,PolyHom.zero 40 19] b
theorem polyLiftFree40_19 : ∀ b : Fin 3, (polyLift40_19 b).freeBlock=basisInt (homKind 40 19) b := by decide
def polyRep40_20_0 : PolyHom 40 20 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_20 (b : Fin 3) : PolyHom 40 20 :=
  ![polyRep40_20_0,PolyHom.zero 40 20,PolyHom.zero 40 20] b
theorem polyLiftFree40_20 : ∀ b : Fin 3, (polyLift40_20 b).freeBlock=basisInt (homKind 40 20) b := by decide
def polyRep40_21_0 : PolyHom 40 21 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep40_21_1 : PolyHom 40 21 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_21 (b : Fin 3) : PolyHom 40 21 :=
  ![polyRep40_21_0,polyRep40_21_1,PolyHom.zero 40 21] b
theorem polyLiftFree40_21 : ∀ b : Fin 3, (polyLift40_21 b).freeBlock=basisInt (homKind 40 21) b := by decide
def polyRep40_22_0 : PolyHom 40 22 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_22 (b : Fin 3) : PolyHom 40 22 :=
  ![polyRep40_22_0,PolyHom.zero 40 22,PolyHom.zero 40 22] b
theorem polyLiftFree40_22 : ∀ b : Fin 3, (polyLift40_22 b).freeBlock=basisInt (homKind 40 22) b := by decide
def polyLift40_23 (b : Fin 3) : PolyHom 40 23 :=
  ![PolyHom.zero 40 23,PolyHom.zero 40 23,PolyHom.zero 40 23] b
theorem polyLiftFree40_23 : ∀ b : Fin 3, (polyLift40_23 b).freeBlock=basisInt (homKind 40 23) b := by decide
def polyRep40_24_0 : PolyHom 40 24 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep40_24_1 : PolyHom 40 24 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_24 (b : Fin 3) : PolyHom 40 24 :=
  ![polyRep40_24_0,polyRep40_24_1,PolyHom.zero 40 24] b
theorem polyLiftFree40_24 : ∀ b : Fin 3, (polyLift40_24 b).freeBlock=basisInt (homKind 40 24) b := by decide
def polyRep40_25_0 : PolyHom 40 25 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep40_25_1 : PolyHom 40 25 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_25 (b : Fin 3) : PolyHom 40 25 :=
  ![polyRep40_25_0,polyRep40_25_1,PolyHom.zero 40 25] b
theorem polyLiftFree40_25 : ∀ b : Fin 3, (polyLift40_25 b).freeBlock=basisInt (homKind 40 25) b := by decide
def polyRep40_26_0 : PolyHom 40 26 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_26 (b : Fin 3) : PolyHom 40 26 :=
  ![polyRep40_26_0,PolyHom.zero 40 26,PolyHom.zero 40 26] b
theorem polyLiftFree40_26 : ∀ b : Fin 3, (polyLift40_26 b).freeBlock=basisInt (homKind 40 26) b := by decide
def polyRep40_27_0 : PolyHom 40 27 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_27 (b : Fin 3) : PolyHom 40 27 :=
  ![polyRep40_27_0,PolyHom.zero 40 27,PolyHom.zero 40 27] b
theorem polyLiftFree40_27 : ∀ b : Fin 3, (polyLift40_27 b).freeBlock=basisInt (homKind 40 27) b := by decide
def polyRep40_28_0 : PolyHom 40 28 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_28 (b : Fin 3) : PolyHom 40 28 :=
  ![polyRep40_28_0,PolyHom.zero 40 28,PolyHom.zero 40 28] b
theorem polyLiftFree40_28 : ∀ b : Fin 3, (polyLift40_28 b).freeBlock=basisInt (homKind 40 28) b := by decide
def polyRep40_29_0 : PolyHom 40 29 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_29 (b : Fin 3) : PolyHom 40 29 :=
  ![polyRep40_29_0,PolyHom.zero 40 29,PolyHom.zero 40 29] b
theorem polyLiftFree40_29 : ∀ b : Fin 3, (polyLift40_29 b).freeBlock=basisInt (homKind 40 29) b := by decide
def polyRep40_30_0 : PolyHom 40 30 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep40_30_1 : PolyHom 40 30 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_30 (b : Fin 3) : PolyHom 40 30 :=
  ![polyRep40_30_0,polyRep40_30_1,PolyHom.zero 40 30] b
theorem polyLiftFree40_30 : ∀ b : Fin 3, (polyLift40_30 b).freeBlock=basisInt (homKind 40 30) b := by decide
def polyRep40_31_0 : PolyHom 40 31 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_31 (b : Fin 3) : PolyHom 40 31 :=
  ![polyRep40_31_0,PolyHom.zero 40 31,PolyHom.zero 40 31] b
theorem polyLiftFree40_31 : ∀ b : Fin 3, (polyLift40_31 b).freeBlock=basisInt (homKind 40 31) b := by decide
def polyRep40_32_0 : PolyHom 40 32 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_32 (b : Fin 3) : PolyHom 40 32 :=
  ![polyRep40_32_0,PolyHom.zero 40 32,PolyHom.zero 40 32] b
theorem polyLiftFree40_32 : ∀ b : Fin 3, (polyLift40_32 b).freeBlock=basisInt (homKind 40 32) b := by decide
def polyRep40_33_0 : PolyHom 40 33 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_33 (b : Fin 3) : PolyHom 40 33 :=
  ![polyRep40_33_0,PolyHom.zero 40 33,PolyHom.zero 40 33] b
theorem polyLiftFree40_33 : ∀ b : Fin 3, (polyLift40_33 b).freeBlock=basisInt (homKind 40 33) b := by decide
def polyRep40_34_0 : PolyHom 40 34 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_34 (b : Fin 3) : PolyHom 40 34 :=
  ![polyRep40_34_0,PolyHom.zero 40 34,PolyHom.zero 40 34] b
theorem polyLiftFree40_34 : ∀ b : Fin 3, (polyLift40_34 b).freeBlock=basisInt (homKind 40 34) b := by decide
def polyRep40_35_0 : PolyHom 40 35 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_35 (b : Fin 3) : PolyHom 40 35 :=
  ![polyRep40_35_0,PolyHom.zero 40 35,PolyHom.zero 40 35] b
theorem polyLiftFree40_35 : ∀ b : Fin 3, (polyLift40_35 b).freeBlock=basisInt (homKind 40 35) b := by decide
def polyRep40_36_0 : PolyHom 40 36 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_36 (b : Fin 3) : PolyHom 40 36 :=
  ![polyRep40_36_0,PolyHom.zero 40 36,PolyHom.zero 40 36] b
theorem polyLiftFree40_36 : ∀ b : Fin 3, (polyLift40_36 b).freeBlock=basisInt (homKind 40 36) b := by decide
def polyRep40_37_0 : PolyHom 40 37 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_37 (b : Fin 3) : PolyHom 40 37 :=
  ![polyRep40_37_0,PolyHom.zero 40 37,PolyHom.zero 40 37] b
theorem polyLiftFree40_37 : ∀ b : Fin 3, (polyLift40_37 b).freeBlock=basisInt (homKind 40 37) b := by decide
def polyRep40_38_0 : PolyHom 40 38 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1)]
  U := !![0,0;(mono6 (1) 1),(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_38 (b : Fin 3) : PolyHom 40 38 :=
  ![polyRep40_38_0,PolyHom.zero 40 38,PolyHom.zero 40 38] b
theorem polyLiftFree40_38 : ∀ b : Fin 3, (polyLift40_38 b).freeBlock=basisInt (homKind 40 38) b := by decide
def polyRep40_39_0 : PolyHom 40 39 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_39 (b : Fin 3) : PolyHom 40 39 :=
  ![polyRep40_39_0,PolyHom.zero 40 39,PolyHom.zero 40 39] b
theorem polyLiftFree40_39 : ∀ b : Fin 3, (polyLift40_39 b).freeBlock=basisInt (homKind 40 39) b := by decide
def polyRep40_40_0 : PolyHom 40 40 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,(mono6 (1) 0)]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep40_40_1 : PolyHom 40 40 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_40 (b : Fin 3) : PolyHom 40 40 :=
  ![polyRep40_40_0,polyRep40_40_1,PolyHom.zero 40 40] b
theorem polyLiftFree40_40 : ∀ b : Fin 3, (polyLift40_40 b).freeBlock=basisInt (homKind 40 40) b := by decide
def polyRep40_41_0 : PolyHom 40 41 where
  M := !![(mono6 (1) 0),0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_41 (b : Fin 3) : PolyHom 40 41 :=
  ![polyRep40_41_0,PolyHom.zero 40 41,PolyHom.zero 40 41] b
theorem polyLiftFree40_41 : ∀ b : Fin 3, (polyLift40_41 b).freeBlock=basisInt (homKind 40 41) b := by decide
def polyRep40_42_0 : PolyHom 40 42 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep40_42_1 : PolyHom 40 42 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep40_42_2 : PolyHom 40 42 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,(mono6 (1) 0)]
  U := !![0,0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_42 (b : Fin 3) : PolyHom 40 42 :=
  ![polyRep40_42_0,polyRep40_42_1,polyRep40_42_2] b
theorem polyLiftFree40_42 : ∀ b : Fin 3, (polyLift40_42 b).freeBlock=basisInt (homKind 40 42) b := by decide
def polyRep40_43_0 : PolyHom 40 43 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep40_43_1 : PolyHom 40 43 where
  M := !![0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,(mono6 (1) 0)]
  U := !![0,0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_43 (b : Fin 3) : PolyHom 40 43 :=
  ![polyRep40_43_0,polyRep40_43_1,PolyHom.zero 40 43] b
theorem polyLiftFree40_43 : ∀ b : Fin 3, (polyLift40_43 b).freeBlock=basisInt (homKind 40 43) b := by decide
def polyRep40_44_0 : PolyHom 40 44 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep40_44_1 : PolyHom 40 44 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep40_44_2 : PolyHom 40 44 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,(mono6 (1) 0)]
  U := !![0,0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_44 (b : Fin 3) : PolyHom 40 44 :=
  ![polyRep40_44_0,polyRep40_44_1,polyRep40_44_2] b
theorem polyLiftFree40_44 : ∀ b : Fin 3, (polyLift40_44 b).freeBlock=basisInt (homKind 40 44) b := by decide
def polyRep40_45_0 : PolyHom 40 45 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep40_45_1 : PolyHom 40 45 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift40_45 (b : Fin 3) : PolyHom 40 45 :=
  ![polyRep40_45_0,polyRep40_45_1,PolyHom.zero 40 45] b
theorem polyLiftFree40_45 : ∀ b : Fin 3, (polyLift40_45 b).freeBlock=basisInt (homKind 40 45) b := by decide
def polyLift40_46 (b : Fin 3) : PolyHom 40 46 :=
  ![PolyHom.zero 40 46,PolyHom.zero 40 46,PolyHom.zero 40 46] b
theorem polyLiftFree40_46 : ∀ b : Fin 3, (polyLift40_46 b).freeBlock=basisInt (homKind 40 46) b := by decide
def polyLiftRow40 (j : Fin 47) (b : Fin 3) : PolyHom 40 j :=
  match j with
  | ⟨0,_⟩ => polyLift40_0 b
  | ⟨1,_⟩ => polyLift40_1 b
  | ⟨2,_⟩ => polyLift40_2 b
  | ⟨3,_⟩ => polyLift40_3 b
  | ⟨4,_⟩ => polyLift40_4 b
  | ⟨5,_⟩ => polyLift40_5 b
  | ⟨6,_⟩ => polyLift40_6 b
  | ⟨7,_⟩ => polyLift40_7 b
  | ⟨8,_⟩ => polyLift40_8 b
  | ⟨9,_⟩ => polyLift40_9 b
  | ⟨10,_⟩ => polyLift40_10 b
  | ⟨11,_⟩ => polyLift40_11 b
  | ⟨12,_⟩ => polyLift40_12 b
  | ⟨13,_⟩ => polyLift40_13 b
  | ⟨14,_⟩ => polyLift40_14 b
  | ⟨15,_⟩ => polyLift40_15 b
  | ⟨16,_⟩ => polyLift40_16 b
  | ⟨17,_⟩ => polyLift40_17 b
  | ⟨18,_⟩ => polyLift40_18 b
  | ⟨19,_⟩ => polyLift40_19 b
  | ⟨20,_⟩ => polyLift40_20 b
  | ⟨21,_⟩ => polyLift40_21 b
  | ⟨22,_⟩ => polyLift40_22 b
  | ⟨23,_⟩ => polyLift40_23 b
  | ⟨24,_⟩ => polyLift40_24 b
  | ⟨25,_⟩ => polyLift40_25 b
  | ⟨26,_⟩ => polyLift40_26 b
  | ⟨27,_⟩ => polyLift40_27 b
  | ⟨28,_⟩ => polyLift40_28 b
  | ⟨29,_⟩ => polyLift40_29 b
  | ⟨30,_⟩ => polyLift40_30 b
  | ⟨31,_⟩ => polyLift40_31 b
  | ⟨32,_⟩ => polyLift40_32 b
  | ⟨33,_⟩ => polyLift40_33 b
  | ⟨34,_⟩ => polyLift40_34 b
  | ⟨35,_⟩ => polyLift40_35 b
  | ⟨36,_⟩ => polyLift40_36 b
  | ⟨37,_⟩ => polyLift40_37 b
  | ⟨38,_⟩ => polyLift40_38 b
  | ⟨39,_⟩ => polyLift40_39 b
  | ⟨40,_⟩ => polyLift40_40 b
  | ⟨41,_⟩ => polyLift40_41 b
  | ⟨42,_⟩ => polyLift40_42 b
  | ⟨43,_⟩ => polyLift40_43 b
  | ⟨44,_⟩ => polyLift40_44 b
  | ⟨45,_⟩ => polyLift40_45 b
  | ⟨46,_⟩ => polyLift40_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree40 (j : Fin 47) (b : Fin 3) : (polyLiftRow40 j b).freeBlock=basisInt (homKind 40 j) b := by
  fin_cases j
  · exact polyLiftFree40_0 b
  · exact polyLiftFree40_1 b
  · exact polyLiftFree40_2 b
  · exact polyLiftFree40_3 b
  · exact polyLiftFree40_4 b
  · exact polyLiftFree40_5 b
  · exact polyLiftFree40_6 b
  · exact polyLiftFree40_7 b
  · exact polyLiftFree40_8 b
  · exact polyLiftFree40_9 b
  · exact polyLiftFree40_10 b
  · exact polyLiftFree40_11 b
  · exact polyLiftFree40_12 b
  · exact polyLiftFree40_13 b
  · exact polyLiftFree40_14 b
  · exact polyLiftFree40_15 b
  · exact polyLiftFree40_16 b
  · exact polyLiftFree40_17 b
  · exact polyLiftFree40_18 b
  · exact polyLiftFree40_19 b
  · exact polyLiftFree40_20 b
  · exact polyLiftFree40_21 b
  · exact polyLiftFree40_22 b
  · exact polyLiftFree40_23 b
  · exact polyLiftFree40_24 b
  · exact polyLiftFree40_25 b
  · exact polyLiftFree40_26 b
  · exact polyLiftFree40_27 b
  · exact polyLiftFree40_28 b
  · exact polyLiftFree40_29 b
  · exact polyLiftFree40_30 b
  · exact polyLiftFree40_31 b
  · exact polyLiftFree40_32 b
  · exact polyLiftFree40_33 b
  · exact polyLiftFree40_34 b
  · exact polyLiftFree40_35 b
  · exact polyLiftFree40_36 b
  · exact polyLiftFree40_37 b
  · exact polyLiftFree40_38 b
  · exact polyLiftFree40_39 b
  · exact polyLiftFree40_40 b
  · exact polyLiftFree40_41 b
  · exact polyLiftFree40_42 b
  · exact polyLiftFree40_43 b
  · exact polyLiftFree40_44 b
  · exact polyLiftFree40_45 b
  · exact polyLiftFree40_46 b
end UniserialComputations.N6
