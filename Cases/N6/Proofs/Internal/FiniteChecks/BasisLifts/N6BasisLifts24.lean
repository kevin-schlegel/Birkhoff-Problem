import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift24_0 (b : Fin 3) : PolyHom 24 0 :=
  ![PolyHom.zero 24 0,PolyHom.zero 24 0,PolyHom.zero 24 0] b
theorem polyLiftFree24_0 : ∀ b : Fin 3, (polyLift24_0 b).freeBlock=basisInt (homKind 24 0) b := by decide
def polyRep24_1_0 : PolyHom 24 1 where
  M := !![0,0,0,0;(mono6 (-1) 2),0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![(mono6 (-1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_1 (b : Fin 3) : PolyHom 24 1 :=
  ![polyRep24_1_0,PolyHom.zero 24 1,PolyHom.zero 24 1] b
theorem polyLiftFree24_1 : ∀ b : Fin 3, (polyLift24_1 b).freeBlock=basisInt (homKind 24 1) b := by decide
def polyLift24_2 (b : Fin 3) : PolyHom 24 2 :=
  ![PolyHom.zero 24 2,PolyHom.zero 24 2,PolyHom.zero 24 2] b
theorem polyLiftFree24_2 : ∀ b : Fin 3, (polyLift24_2 b).freeBlock=basisInt (homKind 24 2) b := by decide
def polyRep24_3_0 : PolyHom 24 3 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_3 (b : Fin 3) : PolyHom 24 3 :=
  ![polyRep24_3_0,PolyHom.zero 24 3,PolyHom.zero 24 3] b
theorem polyLiftFree24_3 : ∀ b : Fin 3, (polyLift24_3 b).freeBlock=basisInt (homKind 24 3) b := by decide
def polyRep24_4_0 : PolyHom 24 4 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_4 (b : Fin 3) : PolyHom 24 4 :=
  ![polyRep24_4_0,PolyHom.zero 24 4,PolyHom.zero 24 4] b
theorem polyLiftFree24_4 : ∀ b : Fin 3, (polyLift24_4 b).freeBlock=basisInt (homKind 24 4) b := by decide
def polyRep24_5_0 : PolyHom 24 5 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_5 (b : Fin 3) : PolyHom 24 5 :=
  ![polyRep24_5_0,PolyHom.zero 24 5,PolyHom.zero 24 5] b
theorem polyLiftFree24_5 : ∀ b : Fin 3, (polyLift24_5 b).freeBlock=basisInt (homKind 24 5) b := by decide
def polyRep24_6_0 : PolyHom 24 6 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_6 (b : Fin 3) : PolyHom 24 6 :=
  ![polyRep24_6_0,PolyHom.zero 24 6,PolyHom.zero 24 6] b
theorem polyLiftFree24_6 : ∀ b : Fin 3, (polyLift24_6 b).freeBlock=basisInt (homKind 24 6) b := by decide
def polyRep24_7_0 : PolyHom 24 7 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_7 (b : Fin 3) : PolyHom 24 7 :=
  ![polyRep24_7_0,PolyHom.zero 24 7,PolyHom.zero 24 7] b
theorem polyLiftFree24_7 : ∀ b : Fin 3, (polyLift24_7 b).freeBlock=basisInt (homKind 24 7) b := by decide
def polyRep24_8_0 : PolyHom 24 8 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_8 (b : Fin 3) : PolyHom 24 8 :=
  ![polyRep24_8_0,PolyHom.zero 24 8,PolyHom.zero 24 8] b
theorem polyLiftFree24_8 : ∀ b : Fin 3, (polyLift24_8 b).freeBlock=basisInt (homKind 24 8) b := by decide
def polyRep24_9_0 : PolyHom 24 9 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_9 (b : Fin 3) : PolyHom 24 9 :=
  ![polyRep24_9_0,PolyHom.zero 24 9,PolyHom.zero 24 9] b
theorem polyLiftFree24_9 : ∀ b : Fin 3, (polyLift24_9 b).freeBlock=basisInt (homKind 24 9) b := by decide
def polyRep24_10_0 : PolyHom 24 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep24_10_1 : PolyHom 24 10 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 4),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_10 (b : Fin 3) : PolyHom 24 10 :=
  ![polyRep24_10_0,polyRep24_10_1,PolyHom.zero 24 10] b
theorem polyLiftFree24_10 : ∀ b : Fin 3, (polyLift24_10 b).freeBlock=basisInt (homKind 24 10) b := by decide
def polyRep24_11_0 : PolyHom 24 11 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep24_11_1 : PolyHom 24 11 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_11 (b : Fin 3) : PolyHom 24 11 :=
  ![polyRep24_11_0,polyRep24_11_1,PolyHom.zero 24 11] b
theorem polyLiftFree24_11 : ∀ b : Fin 3, (polyLift24_11 b).freeBlock=basisInt (homKind 24 11) b := by decide
def polyRep24_12_0 : PolyHom 24 12 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_12 (b : Fin 3) : PolyHom 24 12 :=
  ![polyRep24_12_0,PolyHom.zero 24 12,PolyHom.zero 24 12] b
theorem polyLiftFree24_12 : ∀ b : Fin 3, (polyLift24_12 b).freeBlock=basisInt (homKind 24 12) b := by decide
def polyRep24_13_0 : PolyHom 24 13 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_13 (b : Fin 3) : PolyHom 24 13 :=
  ![polyRep24_13_0,PolyHom.zero 24 13,PolyHom.zero 24 13] b
theorem polyLiftFree24_13 : ∀ b : Fin 3, (polyLift24_13 b).freeBlock=basisInt (homKind 24 13) b := by decide
def polyRep24_14_0 : PolyHom 24 14 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_14 (b : Fin 3) : PolyHom 24 14 :=
  ![polyRep24_14_0,PolyHom.zero 24 14,PolyHom.zero 24 14] b
theorem polyLiftFree24_14 : ∀ b : Fin 3, (polyLift24_14 b).freeBlock=basisInt (homKind 24 14) b := by decide
def polyRep24_15_0 : PolyHom 24 15 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_15 (b : Fin 3) : PolyHom 24 15 :=
  ![polyRep24_15_0,PolyHom.zero 24 15,PolyHom.zero 24 15] b
theorem polyLiftFree24_15 : ∀ b : Fin 3, (polyLift24_15 b).freeBlock=basisInt (homKind 24 15) b := by decide
def polyRep24_16_0 : PolyHom 24 16 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_16 (b : Fin 3) : PolyHom 24 16 :=
  ![polyRep24_16_0,PolyHom.zero 24 16,PolyHom.zero 24 16] b
theorem polyLiftFree24_16 : ∀ b : Fin 3, (polyLift24_16 b).freeBlock=basisInt (homKind 24 16) b := by decide
def polyRep24_17_0 : PolyHom 24 17 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_17 (b : Fin 3) : PolyHom 24 17 :=
  ![polyRep24_17_0,PolyHom.zero 24 17,PolyHom.zero 24 17] b
theorem polyLiftFree24_17 : ∀ b : Fin 3, (polyLift24_17 b).freeBlock=basisInt (homKind 24 17) b := by decide
def polyRep24_18_0 : PolyHom 24 18 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep24_18_1 : PolyHom 24 18 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_18 (b : Fin 3) : PolyHom 24 18 :=
  ![polyRep24_18_0,polyRep24_18_1,PolyHom.zero 24 18] b
theorem polyLiftFree24_18 : ∀ b : Fin 3, (polyLift24_18 b).freeBlock=basisInt (homKind 24 18) b := by decide
def polyRep24_19_0 : PolyHom 24 19 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_19 (b : Fin 3) : PolyHom 24 19 :=
  ![polyRep24_19_0,PolyHom.zero 24 19,PolyHom.zero 24 19] b
theorem polyLiftFree24_19 : ∀ b : Fin 3, (polyLift24_19 b).freeBlock=basisInt (homKind 24 19) b := by decide
def polyRep24_20_0 : PolyHom 24 20 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_20 (b : Fin 3) : PolyHom 24 20 :=
  ![polyRep24_20_0,PolyHom.zero 24 20,PolyHom.zero 24 20] b
theorem polyLiftFree24_20 : ∀ b : Fin 3, (polyLift24_20 b).freeBlock=basisInt (homKind 24 20) b := by decide
def polyRep24_21_0 : PolyHom 24 21 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep24_21_1 : PolyHom 24 21 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_21 (b : Fin 3) : PolyHom 24 21 :=
  ![polyRep24_21_0,polyRep24_21_1,PolyHom.zero 24 21] b
theorem polyLiftFree24_21 : ∀ b : Fin 3, (polyLift24_21 b).freeBlock=basisInt (homKind 24 21) b := by decide
def polyRep24_22_0 : PolyHom 24 22 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_22 (b : Fin 3) : PolyHom 24 22 :=
  ![polyRep24_22_0,PolyHom.zero 24 22,PolyHom.zero 24 22] b
theorem polyLiftFree24_22 : ∀ b : Fin 3, (polyLift24_22 b).freeBlock=basisInt (homKind 24 22) b := by decide
def polyRep24_23_0 : PolyHom 24 23 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_23 (b : Fin 3) : PolyHom 24 23 :=
  ![polyRep24_23_0,PolyHom.zero 24 23,PolyHom.zero 24 23] b
theorem polyLiftFree24_23 : ∀ b : Fin 3, (polyLift24_23 b).freeBlock=basisInt (homKind 24 23) b := by decide
def polyRep24_24_0 : PolyHom 24 24 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep24_24_1 : PolyHom 24 24 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_24 (b : Fin 3) : PolyHom 24 24 :=
  ![polyRep24_24_0,polyRep24_24_1,PolyHom.zero 24 24] b
theorem polyLiftFree24_24 : ∀ b : Fin 3, (polyLift24_24 b).freeBlock=basisInt (homKind 24 24) b := by decide
def polyRep24_25_0 : PolyHom 24 25 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_25 (b : Fin 3) : PolyHom 24 25 :=
  ![polyRep24_25_0,PolyHom.zero 24 25,PolyHom.zero 24 25] b
theorem polyLiftFree24_25 : ∀ b : Fin 3, (polyLift24_25 b).freeBlock=basisInt (homKind 24 25) b := by decide
def polyRep24_26_0 : PolyHom 24 26 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep24_26_1 : PolyHom 24 26 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_26 (b : Fin 3) : PolyHom 24 26 :=
  ![polyRep24_26_0,polyRep24_26_1,PolyHom.zero 24 26] b
theorem polyLiftFree24_26 : ∀ b : Fin 3, (polyLift24_26 b).freeBlock=basisInt (homKind 24 26) b := by decide
def polyRep24_27_0 : PolyHom 24 27 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_27 (b : Fin 3) : PolyHom 24 27 :=
  ![polyRep24_27_0,PolyHom.zero 24 27,PolyHom.zero 24 27] b
theorem polyLiftFree24_27 : ∀ b : Fin 3, (polyLift24_27 b).freeBlock=basisInt (homKind 24 27) b := by decide
def polyRep24_28_0 : PolyHom 24 28 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_28 (b : Fin 3) : PolyHom 24 28 :=
  ![polyRep24_28_0,PolyHom.zero 24 28,PolyHom.zero 24 28] b
theorem polyLiftFree24_28 : ∀ b : Fin 3, (polyLift24_28 b).freeBlock=basisInt (homKind 24 28) b := by decide
def polyRep24_29_0 : PolyHom 24 29 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_29 (b : Fin 3) : PolyHom 24 29 :=
  ![polyRep24_29_0,PolyHom.zero 24 29,PolyHom.zero 24 29] b
theorem polyLiftFree24_29 : ∀ b : Fin 3, (polyLift24_29 b).freeBlock=basisInt (homKind 24 29) b := by decide
def polyRep24_30_0 : PolyHom 24 30 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep24_30_1 : PolyHom 24 30 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_30 (b : Fin 3) : PolyHom 24 30 :=
  ![polyRep24_30_0,polyRep24_30_1,PolyHom.zero 24 30] b
theorem polyLiftFree24_30 : ∀ b : Fin 3, (polyLift24_30 b).freeBlock=basisInt (homKind 24 30) b := by decide
def polyRep24_31_0 : PolyHom 24 31 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep24_31_1 : PolyHom 24 31 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_31 (b : Fin 3) : PolyHom 24 31 :=
  ![polyRep24_31_0,polyRep24_31_1,PolyHom.zero 24 31] b
theorem polyLiftFree24_31 : ∀ b : Fin 3, (polyLift24_31 b).freeBlock=basisInt (homKind 24 31) b := by decide
def polyRep24_32_0 : PolyHom 24 32 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep24_32_1 : PolyHom 24 32 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_32 (b : Fin 3) : PolyHom 24 32 :=
  ![polyRep24_32_0,polyRep24_32_1,PolyHom.zero 24 32] b
theorem polyLiftFree24_32 : ∀ b : Fin 3, (polyLift24_32 b).freeBlock=basisInt (homKind 24 32) b := by decide
def polyRep24_33_0 : PolyHom 24 33 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_33 (b : Fin 3) : PolyHom 24 33 :=
  ![polyRep24_33_0,PolyHom.zero 24 33,PolyHom.zero 24 33] b
theorem polyLiftFree24_33 : ∀ b : Fin 3, (polyLift24_33 b).freeBlock=basisInt (homKind 24 33) b := by decide
def polyRep24_34_0 : PolyHom 24 34 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_34 (b : Fin 3) : PolyHom 24 34 :=
  ![polyRep24_34_0,PolyHom.zero 24 34,PolyHom.zero 24 34] b
theorem polyLiftFree24_34 : ∀ b : Fin 3, (polyLift24_34 b).freeBlock=basisInt (homKind 24 34) b := by decide
def polyRep24_35_0 : PolyHom 24 35 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_35 (b : Fin 3) : PolyHom 24 35 :=
  ![polyRep24_35_0,PolyHom.zero 24 35,PolyHom.zero 24 35] b
theorem polyLiftFree24_35 : ∀ b : Fin 3, (polyLift24_35 b).freeBlock=basisInt (homKind 24 35) b := by decide
def polyRep24_36_0 : PolyHom 24 36 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_36 (b : Fin 3) : PolyHom 24 36 :=
  ![polyRep24_36_0,PolyHom.zero 24 36,PolyHom.zero 24 36] b
theorem polyLiftFree24_36 : ∀ b : Fin 3, (polyLift24_36 b).freeBlock=basisInt (homKind 24 36) b := by decide
def polyRep24_37_0 : PolyHom 24 37 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep24_37_1 : PolyHom 24 37 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_37 (b : Fin 3) : PolyHom 24 37 :=
  ![polyRep24_37_0,polyRep24_37_1,PolyHom.zero 24 37] b
theorem polyLiftFree24_37 : ∀ b : Fin 3, (polyLift24_37 b).freeBlock=basisInt (homKind 24 37) b := by decide
def polyRep24_38_0 : PolyHom 24 38 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep24_38_1 : PolyHom 24 38 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_38 (b : Fin 3) : PolyHom 24 38 :=
  ![polyRep24_38_0,polyRep24_38_1,PolyHom.zero 24 38] b
theorem polyLiftFree24_38 : ∀ b : Fin 3, (polyLift24_38 b).freeBlock=basisInt (homKind 24 38) b := by decide
def polyRep24_39_0 : PolyHom 24 39 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep24_39_1 : PolyHom 24 39 where
  M := !![(mono6 (1) 0),(mono6 (1) 0),0,0;0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_39 (b : Fin 3) : PolyHom 24 39 :=
  ![polyRep24_39_0,polyRep24_39_1,PolyHom.zero 24 39] b
theorem polyLiftFree24_39 : ∀ b : Fin 3, (polyLift24_39 b).freeBlock=basisInt (homKind 24 39) b := by decide
def polyRep24_40_0 : PolyHom 24 40 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep24_40_1 : PolyHom 24 40 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_40 (b : Fin 3) : PolyHom 24 40 :=
  ![polyRep24_40_0,polyRep24_40_1,PolyHom.zero 24 40] b
theorem polyLiftFree24_40 : ∀ b : Fin 3, (polyLift24_40 b).freeBlock=basisInt (homKind 24 40) b := by decide
def polyRep24_41_0 : PolyHom 24 41 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep24_41_1 : PolyHom 24 41 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,(mono6 (1) 1),0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_41 (b : Fin 3) : PolyHom 24 41 :=
  ![polyRep24_41_0,polyRep24_41_1,PolyHom.zero 24 41] b
theorem polyLiftFree24_41 : ∀ b : Fin 3, (polyLift24_41 b).freeBlock=basisInt (homKind 24 41) b := by decide
def polyRep24_42_0 : PolyHom 24 42 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep24_42_1 : PolyHom 24 42 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_42 (b : Fin 3) : PolyHom 24 42 :=
  ![polyRep24_42_0,polyRep24_42_1,PolyHom.zero 24 42] b
theorem polyLiftFree24_42 : ∀ b : Fin 3, (polyLift24_42 b).freeBlock=basisInt (homKind 24 42) b := by decide
def polyRep24_43_0 : PolyHom 24 43 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep24_43_1 : PolyHom 24 43 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_43 (b : Fin 3) : PolyHom 24 43 :=
  ![polyRep24_43_0,polyRep24_43_1,PolyHom.zero 24 43] b
theorem polyLiftFree24_43 : ∀ b : Fin 3, (polyLift24_43 b).freeBlock=basisInt (homKind 24 43) b := by decide
def polyRep24_44_0 : PolyHom 24 44 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep24_44_1 : PolyHom 24 44 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_44 (b : Fin 3) : PolyHom 24 44 :=
  ![polyRep24_44_0,polyRep24_44_1,PolyHom.zero 24 44] b
theorem polyLiftFree24_44 : ∀ b : Fin 3, (polyLift24_44 b).freeBlock=basisInt (homKind 24 44) b := by decide
def polyRep24_45_0 : PolyHom 24 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep24_45_1 : PolyHom 24 45 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift24_45 (b : Fin 3) : PolyHom 24 45 :=
  ![polyRep24_45_0,polyRep24_45_1,PolyHom.zero 24 45] b
theorem polyLiftFree24_45 : ∀ b : Fin 3, (polyLift24_45 b).freeBlock=basisInt (homKind 24 45) b := by decide
def polyLift24_46 (b : Fin 3) : PolyHom 24 46 :=
  ![PolyHom.zero 24 46,PolyHom.zero 24 46,PolyHom.zero 24 46] b
theorem polyLiftFree24_46 : ∀ b : Fin 3, (polyLift24_46 b).freeBlock=basisInt (homKind 24 46) b := by decide
def polyLiftRow24 (j : Fin 47) (b : Fin 3) : PolyHom 24 j :=
  match j with
  | ⟨0,_⟩ => polyLift24_0 b
  | ⟨1,_⟩ => polyLift24_1 b
  | ⟨2,_⟩ => polyLift24_2 b
  | ⟨3,_⟩ => polyLift24_3 b
  | ⟨4,_⟩ => polyLift24_4 b
  | ⟨5,_⟩ => polyLift24_5 b
  | ⟨6,_⟩ => polyLift24_6 b
  | ⟨7,_⟩ => polyLift24_7 b
  | ⟨8,_⟩ => polyLift24_8 b
  | ⟨9,_⟩ => polyLift24_9 b
  | ⟨10,_⟩ => polyLift24_10 b
  | ⟨11,_⟩ => polyLift24_11 b
  | ⟨12,_⟩ => polyLift24_12 b
  | ⟨13,_⟩ => polyLift24_13 b
  | ⟨14,_⟩ => polyLift24_14 b
  | ⟨15,_⟩ => polyLift24_15 b
  | ⟨16,_⟩ => polyLift24_16 b
  | ⟨17,_⟩ => polyLift24_17 b
  | ⟨18,_⟩ => polyLift24_18 b
  | ⟨19,_⟩ => polyLift24_19 b
  | ⟨20,_⟩ => polyLift24_20 b
  | ⟨21,_⟩ => polyLift24_21 b
  | ⟨22,_⟩ => polyLift24_22 b
  | ⟨23,_⟩ => polyLift24_23 b
  | ⟨24,_⟩ => polyLift24_24 b
  | ⟨25,_⟩ => polyLift24_25 b
  | ⟨26,_⟩ => polyLift24_26 b
  | ⟨27,_⟩ => polyLift24_27 b
  | ⟨28,_⟩ => polyLift24_28 b
  | ⟨29,_⟩ => polyLift24_29 b
  | ⟨30,_⟩ => polyLift24_30 b
  | ⟨31,_⟩ => polyLift24_31 b
  | ⟨32,_⟩ => polyLift24_32 b
  | ⟨33,_⟩ => polyLift24_33 b
  | ⟨34,_⟩ => polyLift24_34 b
  | ⟨35,_⟩ => polyLift24_35 b
  | ⟨36,_⟩ => polyLift24_36 b
  | ⟨37,_⟩ => polyLift24_37 b
  | ⟨38,_⟩ => polyLift24_38 b
  | ⟨39,_⟩ => polyLift24_39 b
  | ⟨40,_⟩ => polyLift24_40 b
  | ⟨41,_⟩ => polyLift24_41 b
  | ⟨42,_⟩ => polyLift24_42 b
  | ⟨43,_⟩ => polyLift24_43 b
  | ⟨44,_⟩ => polyLift24_44 b
  | ⟨45,_⟩ => polyLift24_45 b
  | ⟨46,_⟩ => polyLift24_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree24 (j : Fin 47) (b : Fin 3) : (polyLiftRow24 j b).freeBlock=basisInt (homKind 24 j) b := by
  fin_cases j
  · exact polyLiftFree24_0 b
  · exact polyLiftFree24_1 b
  · exact polyLiftFree24_2 b
  · exact polyLiftFree24_3 b
  · exact polyLiftFree24_4 b
  · exact polyLiftFree24_5 b
  · exact polyLiftFree24_6 b
  · exact polyLiftFree24_7 b
  · exact polyLiftFree24_8 b
  · exact polyLiftFree24_9 b
  · exact polyLiftFree24_10 b
  · exact polyLiftFree24_11 b
  · exact polyLiftFree24_12 b
  · exact polyLiftFree24_13 b
  · exact polyLiftFree24_14 b
  · exact polyLiftFree24_15 b
  · exact polyLiftFree24_16 b
  · exact polyLiftFree24_17 b
  · exact polyLiftFree24_18 b
  · exact polyLiftFree24_19 b
  · exact polyLiftFree24_20 b
  · exact polyLiftFree24_21 b
  · exact polyLiftFree24_22 b
  · exact polyLiftFree24_23 b
  · exact polyLiftFree24_24 b
  · exact polyLiftFree24_25 b
  · exact polyLiftFree24_26 b
  · exact polyLiftFree24_27 b
  · exact polyLiftFree24_28 b
  · exact polyLiftFree24_29 b
  · exact polyLiftFree24_30 b
  · exact polyLiftFree24_31 b
  · exact polyLiftFree24_32 b
  · exact polyLiftFree24_33 b
  · exact polyLiftFree24_34 b
  · exact polyLiftFree24_35 b
  · exact polyLiftFree24_36 b
  · exact polyLiftFree24_37 b
  · exact polyLiftFree24_38 b
  · exact polyLiftFree24_39 b
  · exact polyLiftFree24_40 b
  · exact polyLiftFree24_41 b
  · exact polyLiftFree24_42 b
  · exact polyLiftFree24_43 b
  · exact polyLiftFree24_44 b
  · exact polyLiftFree24_45 b
  · exact polyLiftFree24_46 b
end UniserialComputations.N6
