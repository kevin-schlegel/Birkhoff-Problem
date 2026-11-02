import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift37_0 (b : Fin 3) : PolyHom 37 0 :=
  ![PolyHom.zero 37 0,PolyHom.zero 37 0,PolyHom.zero 37 0] b
theorem polyLiftFree37_0 : ∀ b : Fin 3, (polyLift37_0 b).freeBlock=basisInt (homKind 37 0) b := by decide
def polyLift37_1 (b : Fin 3) : PolyHom 37 1 :=
  ![PolyHom.zero 37 1,PolyHom.zero 37 1,PolyHom.zero 37 1] b
theorem polyLiftFree37_1 : ∀ b : Fin 3, (polyLift37_1 b).freeBlock=basisInt (homKind 37 1) b := by decide
def polyLift37_2 (b : Fin 3) : PolyHom 37 2 :=
  ![PolyHom.zero 37 2,PolyHom.zero 37 2,PolyHom.zero 37 2] b
theorem polyLiftFree37_2 : ∀ b : Fin 3, (polyLift37_2 b).freeBlock=basisInt (homKind 37 2) b := by decide
def polyRep37_3_0 : PolyHom 37 3 where
  M := !![0,0,0,0;(mono6 (-1) 1),0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![(mono6 (-1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_3 (b : Fin 3) : PolyHom 37 3 :=
  ![polyRep37_3_0,PolyHom.zero 37 3,PolyHom.zero 37 3] b
theorem polyLiftFree37_3 : ∀ b : Fin 3, (polyLift37_3 b).freeBlock=basisInt (homKind 37 3) b := by decide
def polyLift37_4 (b : Fin 3) : PolyHom 37 4 :=
  ![PolyHom.zero 37 4,PolyHom.zero 37 4,PolyHom.zero 37 4] b
theorem polyLiftFree37_4 : ∀ b : Fin 3, (polyLift37_4 b).freeBlock=basisInt (homKind 37 4) b := by decide
def polyLift37_5 (b : Fin 3) : PolyHom 37 5 :=
  ![PolyHom.zero 37 5,PolyHom.zero 37 5,PolyHom.zero 37 5] b
theorem polyLiftFree37_5 : ∀ b : Fin 3, (polyLift37_5 b).freeBlock=basisInt (homKind 37 5) b := by decide
def polyRep37_6_0 : PolyHom 37 6 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_6 (b : Fin 3) : PolyHom 37 6 :=
  ![polyRep37_6_0,PolyHom.zero 37 6,PolyHom.zero 37 6] b
theorem polyLiftFree37_6 : ∀ b : Fin 3, (polyLift37_6 b).freeBlock=basisInt (homKind 37 6) b := by decide
def polyRep37_7_0 : PolyHom 37 7 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_7 (b : Fin 3) : PolyHom 37 7 :=
  ![polyRep37_7_0,PolyHom.zero 37 7,PolyHom.zero 37 7] b
theorem polyLiftFree37_7 : ∀ b : Fin 3, (polyLift37_7 b).freeBlock=basisInt (homKind 37 7) b := by decide
def polyRep37_8_0 : PolyHom 37 8 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_8 (b : Fin 3) : PolyHom 37 8 :=
  ![polyRep37_8_0,PolyHom.zero 37 8,PolyHom.zero 37 8] b
theorem polyLiftFree37_8 : ∀ b : Fin 3, (polyLift37_8 b).freeBlock=basisInt (homKind 37 8) b := by decide
def polyLift37_9 (b : Fin 3) : PolyHom 37 9 :=
  ![PolyHom.zero 37 9,PolyHom.zero 37 9,PolyHom.zero 37 9] b
theorem polyLiftFree37_9 : ∀ b : Fin 3, (polyLift37_9 b).freeBlock=basisInt (homKind 37 9) b := by decide
def polyRep37_10_0 : PolyHom 37 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep37_10_1 : PolyHom 37 10 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_10 (b : Fin 3) : PolyHom 37 10 :=
  ![polyRep37_10_0,polyRep37_10_1,PolyHom.zero 37 10] b
theorem polyLiftFree37_10 : ∀ b : Fin 3, (polyLift37_10 b).freeBlock=basisInt (homKind 37 10) b := by decide
def polyRep37_11_0 : PolyHom 37 11 where
  M := !![(mono6 (1) 2),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep37_11_1 : PolyHom 37 11 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_11 (b : Fin 3) : PolyHom 37 11 :=
  ![polyRep37_11_0,polyRep37_11_1,PolyHom.zero 37 11] b
theorem polyLiftFree37_11 : ∀ b : Fin 3, (polyLift37_11 b).freeBlock=basisInt (homKind 37 11) b := by decide
def polyRep37_12_0 : PolyHom 37 12 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_12 (b : Fin 3) : PolyHom 37 12 :=
  ![polyRep37_12_0,PolyHom.zero 37 12,PolyHom.zero 37 12] b
theorem polyLiftFree37_12 : ∀ b : Fin 3, (polyLift37_12 b).freeBlock=basisInt (homKind 37 12) b := by decide
def polyRep37_13_0 : PolyHom 37 13 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_13 (b : Fin 3) : PolyHom 37 13 :=
  ![polyRep37_13_0,PolyHom.zero 37 13,PolyHom.zero 37 13] b
theorem polyLiftFree37_13 : ∀ b : Fin 3, (polyLift37_13 b).freeBlock=basisInt (homKind 37 13) b := by decide
def polyLift37_14 (b : Fin 3) : PolyHom 37 14 :=
  ![PolyHom.zero 37 14,PolyHom.zero 37 14,PolyHom.zero 37 14] b
theorem polyLiftFree37_14 : ∀ b : Fin 3, (polyLift37_14 b).freeBlock=basisInt (homKind 37 14) b := by decide
def polyLift37_15 (b : Fin 3) : PolyHom 37 15 :=
  ![PolyHom.zero 37 15,PolyHom.zero 37 15,PolyHom.zero 37 15] b
theorem polyLiftFree37_15 : ∀ b : Fin 3, (polyLift37_15 b).freeBlock=basisInt (homKind 37 15) b := by decide
def polyRep37_16_0 : PolyHom 37 16 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_16 (b : Fin 3) : PolyHom 37 16 :=
  ![polyRep37_16_0,PolyHom.zero 37 16,PolyHom.zero 37 16] b
theorem polyLiftFree37_16 : ∀ b : Fin 3, (polyLift37_16 b).freeBlock=basisInt (homKind 37 16) b := by decide
def polyRep37_17_0 : PolyHom 37 17 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_17 (b : Fin 3) : PolyHom 37 17 :=
  ![polyRep37_17_0,PolyHom.zero 37 17,PolyHom.zero 37 17] b
theorem polyLiftFree37_17 : ∀ b : Fin 3, (polyLift37_17 b).freeBlock=basisInt (homKind 37 17) b := by decide
def polyRep37_18_0 : PolyHom 37 18 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_18 (b : Fin 3) : PolyHom 37 18 :=
  ![polyRep37_18_0,PolyHom.zero 37 18,PolyHom.zero 37 18] b
theorem polyLiftFree37_18 : ∀ b : Fin 3, (polyLift37_18 b).freeBlock=basisInt (homKind 37 18) b := by decide
def polyRep37_19_0 : PolyHom 37 19 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_19 (b : Fin 3) : PolyHom 37 19 :=
  ![polyRep37_19_0,PolyHom.zero 37 19,PolyHom.zero 37 19] b
theorem polyLiftFree37_19 : ∀ b : Fin 3, (polyLift37_19 b).freeBlock=basisInt (homKind 37 19) b := by decide
def polyRep37_20_0 : PolyHom 37 20 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_20 (b : Fin 3) : PolyHom 37 20 :=
  ![polyRep37_20_0,PolyHom.zero 37 20,PolyHom.zero 37 20] b
theorem polyLiftFree37_20 : ∀ b : Fin 3, (polyLift37_20 b).freeBlock=basisInt (homKind 37 20) b := by decide
def polyRep37_21_0 : PolyHom 37 21 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep37_21_1 : PolyHom 37 21 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_21 (b : Fin 3) : PolyHom 37 21 :=
  ![polyRep37_21_0,polyRep37_21_1,PolyHom.zero 37 21] b
theorem polyLiftFree37_21 : ∀ b : Fin 3, (polyLift37_21 b).freeBlock=basisInt (homKind 37 21) b := by decide
def polyRep37_22_0 : PolyHom 37 22 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_22 (b : Fin 3) : PolyHom 37 22 :=
  ![polyRep37_22_0,PolyHom.zero 37 22,PolyHom.zero 37 22] b
theorem polyLiftFree37_22 : ∀ b : Fin 3, (polyLift37_22 b).freeBlock=basisInt (homKind 37 22) b := by decide
def polyRep37_23_0 : PolyHom 37 23 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_23 (b : Fin 3) : PolyHom 37 23 :=
  ![polyRep37_23_0,PolyHom.zero 37 23,PolyHom.zero 37 23] b
theorem polyLiftFree37_23 : ∀ b : Fin 3, (polyLift37_23 b).freeBlock=basisInt (homKind 37 23) b := by decide
def polyRep37_24_0 : PolyHom 37 24 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep37_24_1 : PolyHom 37 24 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_24 (b : Fin 3) : PolyHom 37 24 :=
  ![polyRep37_24_0,polyRep37_24_1,PolyHom.zero 37 24] b
theorem polyLiftFree37_24 : ∀ b : Fin 3, (polyLift37_24 b).freeBlock=basisInt (homKind 37 24) b := by decide
def polyRep37_25_0 : PolyHom 37 25 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep37_25_1 : PolyHom 37 25 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_25 (b : Fin 3) : PolyHom 37 25 :=
  ![polyRep37_25_0,polyRep37_25_1,PolyHom.zero 37 25] b
theorem polyLiftFree37_25 : ∀ b : Fin 3, (polyLift37_25 b).freeBlock=basisInt (homKind 37 25) b := by decide
def polyRep37_26_0 : PolyHom 37 26 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_26 (b : Fin 3) : PolyHom 37 26 :=
  ![polyRep37_26_0,PolyHom.zero 37 26,PolyHom.zero 37 26] b
theorem polyLiftFree37_26 : ∀ b : Fin 3, (polyLift37_26 b).freeBlock=basisInt (homKind 37 26) b := by decide
def polyRep37_27_0 : PolyHom 37 27 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_27 (b : Fin 3) : PolyHom 37 27 :=
  ![polyRep37_27_0,PolyHom.zero 37 27,PolyHom.zero 37 27] b
theorem polyLiftFree37_27 : ∀ b : Fin 3, (polyLift37_27 b).freeBlock=basisInt (homKind 37 27) b := by decide
def polyRep37_28_0 : PolyHom 37 28 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_28 (b : Fin 3) : PolyHom 37 28 :=
  ![polyRep37_28_0,PolyHom.zero 37 28,PolyHom.zero 37 28] b
theorem polyLiftFree37_28 : ∀ b : Fin 3, (polyLift37_28 b).freeBlock=basisInt (homKind 37 28) b := by decide
def polyRep37_29_0 : PolyHom 37 29 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_29 (b : Fin 3) : PolyHom 37 29 :=
  ![polyRep37_29_0,PolyHom.zero 37 29,PolyHom.zero 37 29] b
theorem polyLiftFree37_29 : ∀ b : Fin 3, (polyLift37_29 b).freeBlock=basisInt (homKind 37 29) b := by decide
def polyRep37_30_0 : PolyHom 37 30 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep37_30_1 : PolyHom 37 30 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_30 (b : Fin 3) : PolyHom 37 30 :=
  ![polyRep37_30_0,polyRep37_30_1,PolyHom.zero 37 30] b
theorem polyLiftFree37_30 : ∀ b : Fin 3, (polyLift37_30 b).freeBlock=basisInt (homKind 37 30) b := by decide
def polyRep37_31_0 : PolyHom 37 31 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_31 (b : Fin 3) : PolyHom 37 31 :=
  ![polyRep37_31_0,PolyHom.zero 37 31,PolyHom.zero 37 31] b
theorem polyLiftFree37_31 : ∀ b : Fin 3, (polyLift37_31 b).freeBlock=basisInt (homKind 37 31) b := by decide
def polyRep37_32_0 : PolyHom 37 32 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_32 (b : Fin 3) : PolyHom 37 32 :=
  ![polyRep37_32_0,PolyHom.zero 37 32,PolyHom.zero 37 32] b
theorem polyLiftFree37_32 : ∀ b : Fin 3, (polyLift37_32 b).freeBlock=basisInt (homKind 37 32) b := by decide
def polyRep37_33_0 : PolyHom 37 33 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_33 (b : Fin 3) : PolyHom 37 33 :=
  ![polyRep37_33_0,PolyHom.zero 37 33,PolyHom.zero 37 33] b
theorem polyLiftFree37_33 : ∀ b : Fin 3, (polyLift37_33 b).freeBlock=basisInt (homKind 37 33) b := by decide
def polyRep37_34_0 : PolyHom 37 34 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_34 (b : Fin 3) : PolyHom 37 34 :=
  ![polyRep37_34_0,PolyHom.zero 37 34,PolyHom.zero 37 34] b
theorem polyLiftFree37_34 : ∀ b : Fin 3, (polyLift37_34 b).freeBlock=basisInt (homKind 37 34) b := by decide
def polyRep37_35_0 : PolyHom 37 35 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_35 (b : Fin 3) : PolyHom 37 35 :=
  ![polyRep37_35_0,PolyHom.zero 37 35,PolyHom.zero 37 35] b
theorem polyLiftFree37_35 : ∀ b : Fin 3, (polyLift37_35 b).freeBlock=basisInt (homKind 37 35) b := by decide
def polyRep37_36_0 : PolyHom 37 36 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_36 (b : Fin 3) : PolyHom 37 36 :=
  ![polyRep37_36_0,PolyHom.zero 37 36,PolyHom.zero 37 36] b
theorem polyLiftFree37_36 : ∀ b : Fin 3, (polyLift37_36 b).freeBlock=basisInt (homKind 37 36) b := by decide
def polyRep37_37_0 : PolyHom 37 37 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep37_37_1 : PolyHom 37 37 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_37 (b : Fin 3) : PolyHom 37 37 :=
  ![polyRep37_37_0,polyRep37_37_1,PolyHom.zero 37 37] b
theorem polyLiftFree37_37 : ∀ b : Fin 3, (polyLift37_37 b).freeBlock=basisInt (homKind 37 37) b := by decide
def polyRep37_38_0 : PolyHom 37 38 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0]
  U := !![0,0;(mono6 (1) 1),(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_38 (b : Fin 3) : PolyHom 37 38 :=
  ![polyRep37_38_0,PolyHom.zero 37 38,PolyHom.zero 37 38] b
theorem polyLiftFree37_38 : ∀ b : Fin 3, (polyLift37_38 b).freeBlock=basisInt (homKind 37 38) b := by decide
def polyRep37_39_0 : PolyHom 37 39 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_39 (b : Fin 3) : PolyHom 37 39 :=
  ![polyRep37_39_0,PolyHom.zero 37 39,PolyHom.zero 37 39] b
theorem polyLiftFree37_39 : ∀ b : Fin 3, (polyLift37_39 b).freeBlock=basisInt (homKind 37 39) b := by decide
def polyRep37_40_0 : PolyHom 37 40 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep37_40_1 : PolyHom 37 40 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_40 (b : Fin 3) : PolyHom 37 40 :=
  ![polyRep37_40_0,polyRep37_40_1,PolyHom.zero 37 40] b
theorem polyLiftFree37_40 : ∀ b : Fin 3, (polyLift37_40 b).freeBlock=basisInt (homKind 37 40) b := by decide
def polyRep37_41_0 : PolyHom 37 41 where
  M := !![(mono6 (1) 0),0,0,(mono6 (1) 0);0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_41 (b : Fin 3) : PolyHom 37 41 :=
  ![polyRep37_41_0,PolyHom.zero 37 41,PolyHom.zero 37 41] b
theorem polyLiftFree37_41 : ∀ b : Fin 3, (polyLift37_41 b).freeBlock=basisInt (homKind 37 41) b := by decide
def polyRep37_42_0 : PolyHom 37 42 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep37_42_1 : PolyHom 37 42 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep37_42_2 : PolyHom 37 42 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_42 (b : Fin 3) : PolyHom 37 42 :=
  ![polyRep37_42_0,polyRep37_42_1,polyRep37_42_2] b
theorem polyLiftFree37_42 : ∀ b : Fin 3, (polyLift37_42 b).freeBlock=basisInt (homKind 37 42) b := by decide
def polyRep37_43_0 : PolyHom 37 43 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep37_43_1 : PolyHom 37 43 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_43 (b : Fin 3) : PolyHom 37 43 :=
  ![polyRep37_43_0,polyRep37_43_1,PolyHom.zero 37 43] b
theorem polyLiftFree37_43 : ∀ b : Fin 3, (polyLift37_43 b).freeBlock=basisInt (homKind 37 43) b := by decide
def polyRep37_44_0 : PolyHom 37 44 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep37_44_1 : PolyHom 37 44 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep37_44_2 : PolyHom 37 44 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_44 (b : Fin 3) : PolyHom 37 44 :=
  ![polyRep37_44_0,polyRep37_44_1,polyRep37_44_2] b
theorem polyLiftFree37_44 : ∀ b : Fin 3, (polyLift37_44 b).freeBlock=basisInt (homKind 37 44) b := by decide
def polyRep37_45_0 : PolyHom 37 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep37_45_1 : PolyHom 37 45 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift37_45 (b : Fin 3) : PolyHom 37 45 :=
  ![polyRep37_45_0,polyRep37_45_1,PolyHom.zero 37 45] b
theorem polyLiftFree37_45 : ∀ b : Fin 3, (polyLift37_45 b).freeBlock=basisInt (homKind 37 45) b := by decide
def polyLift37_46 (b : Fin 3) : PolyHom 37 46 :=
  ![PolyHom.zero 37 46,PolyHom.zero 37 46,PolyHom.zero 37 46] b
theorem polyLiftFree37_46 : ∀ b : Fin 3, (polyLift37_46 b).freeBlock=basisInt (homKind 37 46) b := by decide
def polyLiftRow37 (j : Fin 47) (b : Fin 3) : PolyHom 37 j :=
  match j with
  | ⟨0,_⟩ => polyLift37_0 b
  | ⟨1,_⟩ => polyLift37_1 b
  | ⟨2,_⟩ => polyLift37_2 b
  | ⟨3,_⟩ => polyLift37_3 b
  | ⟨4,_⟩ => polyLift37_4 b
  | ⟨5,_⟩ => polyLift37_5 b
  | ⟨6,_⟩ => polyLift37_6 b
  | ⟨7,_⟩ => polyLift37_7 b
  | ⟨8,_⟩ => polyLift37_8 b
  | ⟨9,_⟩ => polyLift37_9 b
  | ⟨10,_⟩ => polyLift37_10 b
  | ⟨11,_⟩ => polyLift37_11 b
  | ⟨12,_⟩ => polyLift37_12 b
  | ⟨13,_⟩ => polyLift37_13 b
  | ⟨14,_⟩ => polyLift37_14 b
  | ⟨15,_⟩ => polyLift37_15 b
  | ⟨16,_⟩ => polyLift37_16 b
  | ⟨17,_⟩ => polyLift37_17 b
  | ⟨18,_⟩ => polyLift37_18 b
  | ⟨19,_⟩ => polyLift37_19 b
  | ⟨20,_⟩ => polyLift37_20 b
  | ⟨21,_⟩ => polyLift37_21 b
  | ⟨22,_⟩ => polyLift37_22 b
  | ⟨23,_⟩ => polyLift37_23 b
  | ⟨24,_⟩ => polyLift37_24 b
  | ⟨25,_⟩ => polyLift37_25 b
  | ⟨26,_⟩ => polyLift37_26 b
  | ⟨27,_⟩ => polyLift37_27 b
  | ⟨28,_⟩ => polyLift37_28 b
  | ⟨29,_⟩ => polyLift37_29 b
  | ⟨30,_⟩ => polyLift37_30 b
  | ⟨31,_⟩ => polyLift37_31 b
  | ⟨32,_⟩ => polyLift37_32 b
  | ⟨33,_⟩ => polyLift37_33 b
  | ⟨34,_⟩ => polyLift37_34 b
  | ⟨35,_⟩ => polyLift37_35 b
  | ⟨36,_⟩ => polyLift37_36 b
  | ⟨37,_⟩ => polyLift37_37 b
  | ⟨38,_⟩ => polyLift37_38 b
  | ⟨39,_⟩ => polyLift37_39 b
  | ⟨40,_⟩ => polyLift37_40 b
  | ⟨41,_⟩ => polyLift37_41 b
  | ⟨42,_⟩ => polyLift37_42 b
  | ⟨43,_⟩ => polyLift37_43 b
  | ⟨44,_⟩ => polyLift37_44 b
  | ⟨45,_⟩ => polyLift37_45 b
  | ⟨46,_⟩ => polyLift37_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree37 (j : Fin 47) (b : Fin 3) : (polyLiftRow37 j b).freeBlock=basisInt (homKind 37 j) b := by
  fin_cases j
  · exact polyLiftFree37_0 b
  · exact polyLiftFree37_1 b
  · exact polyLiftFree37_2 b
  · exact polyLiftFree37_3 b
  · exact polyLiftFree37_4 b
  · exact polyLiftFree37_5 b
  · exact polyLiftFree37_6 b
  · exact polyLiftFree37_7 b
  · exact polyLiftFree37_8 b
  · exact polyLiftFree37_9 b
  · exact polyLiftFree37_10 b
  · exact polyLiftFree37_11 b
  · exact polyLiftFree37_12 b
  · exact polyLiftFree37_13 b
  · exact polyLiftFree37_14 b
  · exact polyLiftFree37_15 b
  · exact polyLiftFree37_16 b
  · exact polyLiftFree37_17 b
  · exact polyLiftFree37_18 b
  · exact polyLiftFree37_19 b
  · exact polyLiftFree37_20 b
  · exact polyLiftFree37_21 b
  · exact polyLiftFree37_22 b
  · exact polyLiftFree37_23 b
  · exact polyLiftFree37_24 b
  · exact polyLiftFree37_25 b
  · exact polyLiftFree37_26 b
  · exact polyLiftFree37_27 b
  · exact polyLiftFree37_28 b
  · exact polyLiftFree37_29 b
  · exact polyLiftFree37_30 b
  · exact polyLiftFree37_31 b
  · exact polyLiftFree37_32 b
  · exact polyLiftFree37_33 b
  · exact polyLiftFree37_34 b
  · exact polyLiftFree37_35 b
  · exact polyLiftFree37_36 b
  · exact polyLiftFree37_37 b
  · exact polyLiftFree37_38 b
  · exact polyLiftFree37_39 b
  · exact polyLiftFree37_40 b
  · exact polyLiftFree37_41 b
  · exact polyLiftFree37_42 b
  · exact polyLiftFree37_43 b
  · exact polyLiftFree37_44 b
  · exact polyLiftFree37_45 b
  · exact polyLiftFree37_46 b
end UniserialComputations.N6
