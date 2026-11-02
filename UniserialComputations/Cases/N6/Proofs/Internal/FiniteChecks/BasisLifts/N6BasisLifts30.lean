import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift30_0 (b : Fin 3) : PolyHom 30 0 :=
  ![PolyHom.zero 30 0,PolyHom.zero 30 0,PolyHom.zero 30 0] b
theorem polyLiftFree30_0 : ∀ b : Fin 3, (polyLift30_0 b).freeBlock=basisInt (homKind 30 0) b := by decide
def polyLift30_1 (b : Fin 3) : PolyHom 30 1 :=
  ![PolyHom.zero 30 1,PolyHom.zero 30 1,PolyHom.zero 30 1] b
theorem polyLiftFree30_1 : ∀ b : Fin 3, (polyLift30_1 b).freeBlock=basisInt (homKind 30 1) b := by decide
def polyLift30_2 (b : Fin 3) : PolyHom 30 2 :=
  ![PolyHom.zero 30 2,PolyHom.zero 30 2,PolyHom.zero 30 2] b
theorem polyLiftFree30_2 : ∀ b : Fin 3, (polyLift30_2 b).freeBlock=basisInt (homKind 30 2) b := by decide
def polyRep30_3_0 : PolyHom 30 3 where
  M := !![0,0,0,0;(mono6 (-1) 1),0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![(mono6 (-1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_3 (b : Fin 3) : PolyHom 30 3 :=
  ![polyRep30_3_0,PolyHom.zero 30 3,PolyHom.zero 30 3] b
theorem polyLiftFree30_3 : ∀ b : Fin 3, (polyLift30_3 b).freeBlock=basisInt (homKind 30 3) b := by decide
def polyLift30_4 (b : Fin 3) : PolyHom 30 4 :=
  ![PolyHom.zero 30 4,PolyHom.zero 30 4,PolyHom.zero 30 4] b
theorem polyLiftFree30_4 : ∀ b : Fin 3, (polyLift30_4 b).freeBlock=basisInt (homKind 30 4) b := by decide
def polyLift30_5 (b : Fin 3) : PolyHom 30 5 :=
  ![PolyHom.zero 30 5,PolyHom.zero 30 5,PolyHom.zero 30 5] b
theorem polyLiftFree30_5 : ∀ b : Fin 3, (polyLift30_5 b).freeBlock=basisInt (homKind 30 5) b := by decide
def polyRep30_6_0 : PolyHom 30 6 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_6 (b : Fin 3) : PolyHom 30 6 :=
  ![polyRep30_6_0,PolyHom.zero 30 6,PolyHom.zero 30 6] b
theorem polyLiftFree30_6 : ∀ b : Fin 3, (polyLift30_6 b).freeBlock=basisInt (homKind 30 6) b := by decide
def polyRep30_7_0 : PolyHom 30 7 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_7 (b : Fin 3) : PolyHom 30 7 :=
  ![polyRep30_7_0,PolyHom.zero 30 7,PolyHom.zero 30 7] b
theorem polyLiftFree30_7 : ∀ b : Fin 3, (polyLift30_7 b).freeBlock=basisInt (homKind 30 7) b := by decide
def polyRep30_8_0 : PolyHom 30 8 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_8 (b : Fin 3) : PolyHom 30 8 :=
  ![polyRep30_8_0,PolyHom.zero 30 8,PolyHom.zero 30 8] b
theorem polyLiftFree30_8 : ∀ b : Fin 3, (polyLift30_8 b).freeBlock=basisInt (homKind 30 8) b := by decide
def polyLift30_9 (b : Fin 3) : PolyHom 30 9 :=
  ![PolyHom.zero 30 9,PolyHom.zero 30 9,PolyHom.zero 30 9] b
theorem polyLiftFree30_9 : ∀ b : Fin 3, (polyLift30_9 b).freeBlock=basisInt (homKind 30 9) b := by decide
def polyRep30_10_0 : PolyHom 30 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep30_10_1 : PolyHom 30 10 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_10 (b : Fin 3) : PolyHom 30 10 :=
  ![polyRep30_10_0,polyRep30_10_1,PolyHom.zero 30 10] b
theorem polyLiftFree30_10 : ∀ b : Fin 3, (polyLift30_10 b).freeBlock=basisInt (homKind 30 10) b := by decide
def polyRep30_11_0 : PolyHom 30 11 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep30_11_1 : PolyHom 30 11 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_11 (b : Fin 3) : PolyHom 30 11 :=
  ![polyRep30_11_0,polyRep30_11_1,PolyHom.zero 30 11] b
theorem polyLiftFree30_11 : ∀ b : Fin 3, (polyLift30_11 b).freeBlock=basisInt (homKind 30 11) b := by decide
def polyRep30_12_0 : PolyHom 30 12 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_12 (b : Fin 3) : PolyHom 30 12 :=
  ![polyRep30_12_0,PolyHom.zero 30 12,PolyHom.zero 30 12] b
theorem polyLiftFree30_12 : ∀ b : Fin 3, (polyLift30_12 b).freeBlock=basisInt (homKind 30 12) b := by decide
def polyRep30_13_0 : PolyHom 30 13 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_13 (b : Fin 3) : PolyHom 30 13 :=
  ![polyRep30_13_0,PolyHom.zero 30 13,PolyHom.zero 30 13] b
theorem polyLiftFree30_13 : ∀ b : Fin 3, (polyLift30_13 b).freeBlock=basisInt (homKind 30 13) b := by decide
def polyLift30_14 (b : Fin 3) : PolyHom 30 14 :=
  ![PolyHom.zero 30 14,PolyHom.zero 30 14,PolyHom.zero 30 14] b
theorem polyLiftFree30_14 : ∀ b : Fin 3, (polyLift30_14 b).freeBlock=basisInt (homKind 30 14) b := by decide
def polyLift30_15 (b : Fin 3) : PolyHom 30 15 :=
  ![PolyHom.zero 30 15,PolyHom.zero 30 15,PolyHom.zero 30 15] b
theorem polyLiftFree30_15 : ∀ b : Fin 3, (polyLift30_15 b).freeBlock=basisInt (homKind 30 15) b := by decide
def polyRep30_16_0 : PolyHom 30 16 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_16 (b : Fin 3) : PolyHom 30 16 :=
  ![polyRep30_16_0,PolyHom.zero 30 16,PolyHom.zero 30 16] b
theorem polyLiftFree30_16 : ∀ b : Fin 3, (polyLift30_16 b).freeBlock=basisInt (homKind 30 16) b := by decide
def polyLift30_17 (b : Fin 3) : PolyHom 30 17 :=
  ![PolyHom.zero 30 17,PolyHom.zero 30 17,PolyHom.zero 30 17] b
theorem polyLiftFree30_17 : ∀ b : Fin 3, (polyLift30_17 b).freeBlock=basisInt (homKind 30 17) b := by decide
def polyRep30_18_0 : PolyHom 30 18 where
  M := !![0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (-1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_18 (b : Fin 3) : PolyHom 30 18 :=
  ![polyRep30_18_0,PolyHom.zero 30 18,PolyHom.zero 30 18] b
theorem polyLiftFree30_18 : ∀ b : Fin 3, (polyLift30_18 b).freeBlock=basisInt (homKind 30 18) b := by decide
def polyRep30_19_0 : PolyHom 30 19 where
  M := !![0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (-1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_19 (b : Fin 3) : PolyHom 30 19 :=
  ![polyRep30_19_0,PolyHom.zero 30 19,PolyHom.zero 30 19] b
theorem polyLiftFree30_19 : ∀ b : Fin 3, (polyLift30_19 b).freeBlock=basisInt (homKind 30 19) b := by decide
def polyLift30_20 (b : Fin 3) : PolyHom 30 20 :=
  ![PolyHom.zero 30 20,PolyHom.zero 30 20,PolyHom.zero 30 20] b
theorem polyLiftFree30_20 : ∀ b : Fin 3, (polyLift30_20 b).freeBlock=basisInt (homKind 30 20) b := by decide
def polyRep30_21_0 : PolyHom 30 21 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep30_21_1 : PolyHom 30 21 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_21 (b : Fin 3) : PolyHom 30 21 :=
  ![polyRep30_21_0,polyRep30_21_1,PolyHom.zero 30 21] b
theorem polyLiftFree30_21 : ∀ b : Fin 3, (polyLift30_21 b).freeBlock=basisInt (homKind 30 21) b := by decide
def polyRep30_22_0 : PolyHom 30 22 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_22 (b : Fin 3) : PolyHom 30 22 :=
  ![polyRep30_22_0,PolyHom.zero 30 22,PolyHom.zero 30 22] b
theorem polyLiftFree30_22 : ∀ b : Fin 3, (polyLift30_22 b).freeBlock=basisInt (homKind 30 22) b := by decide
def polyLift30_23 (b : Fin 3) : PolyHom 30 23 :=
  ![PolyHom.zero 30 23,PolyHom.zero 30 23,PolyHom.zero 30 23] b
theorem polyLiftFree30_23 : ∀ b : Fin 3, (polyLift30_23 b).freeBlock=basisInt (homKind 30 23) b := by decide
def polyRep30_24_0 : PolyHom 30 24 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 1),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep30_24_1 : PolyHom 30 24 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_24 (b : Fin 3) : PolyHom 30 24 :=
  ![polyRep30_24_0,polyRep30_24_1,PolyHom.zero 30 24] b
theorem polyLiftFree30_24 : ∀ b : Fin 3, (polyLift30_24 b).freeBlock=basisInt (homKind 30 24) b := by decide
def polyRep30_25_0 : PolyHom 30 25 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_25 (b : Fin 3) : PolyHom 30 25 :=
  ![polyRep30_25_0,PolyHom.zero 30 25,PolyHom.zero 30 25] b
theorem polyLiftFree30_25 : ∀ b : Fin 3, (polyLift30_25 b).freeBlock=basisInt (homKind 30 25) b := by decide
def polyRep30_26_0 : PolyHom 30 26 where
  M := !![0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (-1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_26 (b : Fin 3) : PolyHom 30 26 :=
  ![polyRep30_26_0,PolyHom.zero 30 26,PolyHom.zero 30 26] b
theorem polyLiftFree30_26 : ∀ b : Fin 3, (polyLift30_26 b).freeBlock=basisInt (homKind 30 26) b := by decide
def polyRep30_27_0 : PolyHom 30 27 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_27 (b : Fin 3) : PolyHom 30 27 :=
  ![polyRep30_27_0,PolyHom.zero 30 27,PolyHom.zero 30 27] b
theorem polyLiftFree30_27 : ∀ b : Fin 3, (polyLift30_27 b).freeBlock=basisInt (homKind 30 27) b := by decide
def polyRep30_28_0 : PolyHom 30 28 where
  M := !![0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (-1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_28 (b : Fin 3) : PolyHom 30 28 :=
  ![polyRep30_28_0,PolyHom.zero 30 28,PolyHom.zero 30 28] b
theorem polyLiftFree30_28 : ∀ b : Fin 3, (polyLift30_28 b).freeBlock=basisInt (homKind 30 28) b := by decide
def polyLift30_29 (b : Fin 3) : PolyHom 30 29 :=
  ![PolyHom.zero 30 29,PolyHom.zero 30 29,PolyHom.zero 30 29] b
theorem polyLiftFree30_29 : ∀ b : Fin 3, (polyLift30_29 b).freeBlock=basisInt (homKind 30 29) b := by decide
def polyRep30_30_0 : PolyHom 30 30 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep30_30_1 : PolyHom 30 30 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_30 (b : Fin 3) : PolyHom 30 30 :=
  ![polyRep30_30_0,polyRep30_30_1,PolyHom.zero 30 30] b
theorem polyLiftFree30_30 : ∀ b : Fin 3, (polyLift30_30 b).freeBlock=basisInt (homKind 30 30) b := by decide
def polyRep30_31_0 : PolyHom 30 31 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_31 (b : Fin 3) : PolyHom 30 31 :=
  ![polyRep30_31_0,PolyHom.zero 30 31,PolyHom.zero 30 31] b
theorem polyLiftFree30_31 : ∀ b : Fin 3, (polyLift30_31 b).freeBlock=basisInt (homKind 30 31) b := by decide
def polyRep30_32_0 : PolyHom 30 32 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_32 (b : Fin 3) : PolyHom 30 32 :=
  ![polyRep30_32_0,PolyHom.zero 30 32,PolyHom.zero 30 32] b
theorem polyLiftFree30_32 : ∀ b : Fin 3, (polyLift30_32 b).freeBlock=basisInt (homKind 30 32) b := by decide
def polyRep30_33_0 : PolyHom 30 33 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_33 (b : Fin 3) : PolyHom 30 33 :=
  ![polyRep30_33_0,PolyHom.zero 30 33,PolyHom.zero 30 33] b
theorem polyLiftFree30_33 : ∀ b : Fin 3, (polyLift30_33 b).freeBlock=basisInt (homKind 30 33) b := by decide
def polyRep30_34_0 : PolyHom 30 34 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_34 (b : Fin 3) : PolyHom 30 34 :=
  ![polyRep30_34_0,PolyHom.zero 30 34,PolyHom.zero 30 34] b
theorem polyLiftFree30_34 : ∀ b : Fin 3, (polyLift30_34 b).freeBlock=basisInt (homKind 30 34) b := by decide
def polyRep30_35_0 : PolyHom 30 35 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_35 (b : Fin 3) : PolyHom 30 35 :=
  ![polyRep30_35_0,PolyHom.zero 30 35,PolyHom.zero 30 35] b
theorem polyLiftFree30_35 : ∀ b : Fin 3, (polyLift30_35 b).freeBlock=basisInt (homKind 30 35) b := by decide
def polyRep30_36_0 : PolyHom 30 36 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_36 (b : Fin 3) : PolyHom 30 36 :=
  ![polyRep30_36_0,PolyHom.zero 30 36,PolyHom.zero 30 36] b
theorem polyLiftFree30_36 : ∀ b : Fin 3, (polyLift30_36 b).freeBlock=basisInt (homKind 30 36) b := by decide
def polyRep30_37_0 : PolyHom 30 37 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_37 (b : Fin 3) : PolyHom 30 37 :=
  ![polyRep30_37_0,PolyHom.zero 30 37,PolyHom.zero 30 37] b
theorem polyLiftFree30_37 : ∀ b : Fin 3, (polyLift30_37 b).freeBlock=basisInt (homKind 30 37) b := by decide
def polyRep30_38_0 : PolyHom 30 38 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0]
  U := !![0,0;(mono6 (1) 1),(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_38 (b : Fin 3) : PolyHom 30 38 :=
  ![polyRep30_38_0,PolyHom.zero 30 38,PolyHom.zero 30 38] b
theorem polyLiftFree30_38 : ∀ b : Fin 3, (polyLift30_38 b).freeBlock=basisInt (homKind 30 38) b := by decide
def polyRep30_39_0 : PolyHom 30 39 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_39 (b : Fin 3) : PolyHom 30 39 :=
  ![polyRep30_39_0,PolyHom.zero 30 39,PolyHom.zero 30 39] b
theorem polyLiftFree30_39 : ∀ b : Fin 3, (polyLift30_39 b).freeBlock=basisInt (homKind 30 39) b := by decide
def polyRep30_40_0 : PolyHom 30 40 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_40 (b : Fin 3) : PolyHom 30 40 :=
  ![polyRep30_40_0,PolyHom.zero 30 40,PolyHom.zero 30 40] b
theorem polyLiftFree30_40 : ∀ b : Fin 3, (polyLift30_40 b).freeBlock=basisInt (homKind 30 40) b := by decide
def polyRep30_41_0 : PolyHom 30 41 where
  M := !![0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (-1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_41 (b : Fin 3) : PolyHom 30 41 :=
  ![polyRep30_41_0,PolyHom.zero 30 41,PolyHom.zero 30 41] b
theorem polyLiftFree30_41 : ∀ b : Fin 3, (polyLift30_41 b).freeBlock=basisInt (homKind 30 41) b := by decide
def polyRep30_42_0 : PolyHom 30 42 where
  M := !![0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,(mono6 (-1) 0);0,0,0,0]
  U := !![(mono6 (1) 0),0;0,(mono6 (-1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep30_42_1 : PolyHom 30 42 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_42 (b : Fin 3) : PolyHom 30 42 :=
  ![polyRep30_42_0,polyRep30_42_1,PolyHom.zero 30 42] b
theorem polyLiftFree30_42 : ∀ b : Fin 3, (polyLift30_42 b).freeBlock=basisInt (homKind 30 42) b := by decide
def polyRep30_43_0 : PolyHom 30 43 where
  M := !![0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (-1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep30_43_1 : PolyHom 30 43 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_43 (b : Fin 3) : PolyHom 30 43 :=
  ![polyRep30_43_0,polyRep30_43_1,PolyHom.zero 30 43] b
theorem polyLiftFree30_43 : ∀ b : Fin 3, (polyLift30_43 b).freeBlock=basisInt (homKind 30 43) b := by decide
def polyRep30_44_0 : PolyHom 30 44 where
  M := !![0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,(mono6 (-1) 0);0,0,0,0]
  U := !![(mono6 (1) 0),0;0,(mono6 (-1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep30_44_1 : PolyHom 30 44 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_44 (b : Fin 3) : PolyHom 30 44 :=
  ![polyRep30_44_0,polyRep30_44_1,PolyHom.zero 30 44] b
theorem polyLiftFree30_44 : ∀ b : Fin 3, (polyLift30_44 b).freeBlock=basisInt (homKind 30 44) b := by decide
def polyRep30_45_0 : PolyHom 30 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep30_45_1 : PolyHom 30 45 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift30_45 (b : Fin 3) : PolyHom 30 45 :=
  ![polyRep30_45_0,polyRep30_45_1,PolyHom.zero 30 45] b
theorem polyLiftFree30_45 : ∀ b : Fin 3, (polyLift30_45 b).freeBlock=basisInt (homKind 30 45) b := by decide
def polyLift30_46 (b : Fin 3) : PolyHom 30 46 :=
  ![PolyHom.zero 30 46,PolyHom.zero 30 46,PolyHom.zero 30 46] b
theorem polyLiftFree30_46 : ∀ b : Fin 3, (polyLift30_46 b).freeBlock=basisInt (homKind 30 46) b := by decide
def polyLiftRow30 (j : Fin 47) (b : Fin 3) : PolyHom 30 j :=
  match j with
  | ⟨0,_⟩ => polyLift30_0 b
  | ⟨1,_⟩ => polyLift30_1 b
  | ⟨2,_⟩ => polyLift30_2 b
  | ⟨3,_⟩ => polyLift30_3 b
  | ⟨4,_⟩ => polyLift30_4 b
  | ⟨5,_⟩ => polyLift30_5 b
  | ⟨6,_⟩ => polyLift30_6 b
  | ⟨7,_⟩ => polyLift30_7 b
  | ⟨8,_⟩ => polyLift30_8 b
  | ⟨9,_⟩ => polyLift30_9 b
  | ⟨10,_⟩ => polyLift30_10 b
  | ⟨11,_⟩ => polyLift30_11 b
  | ⟨12,_⟩ => polyLift30_12 b
  | ⟨13,_⟩ => polyLift30_13 b
  | ⟨14,_⟩ => polyLift30_14 b
  | ⟨15,_⟩ => polyLift30_15 b
  | ⟨16,_⟩ => polyLift30_16 b
  | ⟨17,_⟩ => polyLift30_17 b
  | ⟨18,_⟩ => polyLift30_18 b
  | ⟨19,_⟩ => polyLift30_19 b
  | ⟨20,_⟩ => polyLift30_20 b
  | ⟨21,_⟩ => polyLift30_21 b
  | ⟨22,_⟩ => polyLift30_22 b
  | ⟨23,_⟩ => polyLift30_23 b
  | ⟨24,_⟩ => polyLift30_24 b
  | ⟨25,_⟩ => polyLift30_25 b
  | ⟨26,_⟩ => polyLift30_26 b
  | ⟨27,_⟩ => polyLift30_27 b
  | ⟨28,_⟩ => polyLift30_28 b
  | ⟨29,_⟩ => polyLift30_29 b
  | ⟨30,_⟩ => polyLift30_30 b
  | ⟨31,_⟩ => polyLift30_31 b
  | ⟨32,_⟩ => polyLift30_32 b
  | ⟨33,_⟩ => polyLift30_33 b
  | ⟨34,_⟩ => polyLift30_34 b
  | ⟨35,_⟩ => polyLift30_35 b
  | ⟨36,_⟩ => polyLift30_36 b
  | ⟨37,_⟩ => polyLift30_37 b
  | ⟨38,_⟩ => polyLift30_38 b
  | ⟨39,_⟩ => polyLift30_39 b
  | ⟨40,_⟩ => polyLift30_40 b
  | ⟨41,_⟩ => polyLift30_41 b
  | ⟨42,_⟩ => polyLift30_42 b
  | ⟨43,_⟩ => polyLift30_43 b
  | ⟨44,_⟩ => polyLift30_44 b
  | ⟨45,_⟩ => polyLift30_45 b
  | ⟨46,_⟩ => polyLift30_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree30 (j : Fin 47) (b : Fin 3) : (polyLiftRow30 j b).freeBlock=basisInt (homKind 30 j) b := by
  fin_cases j
  · exact polyLiftFree30_0 b
  · exact polyLiftFree30_1 b
  · exact polyLiftFree30_2 b
  · exact polyLiftFree30_3 b
  · exact polyLiftFree30_4 b
  · exact polyLiftFree30_5 b
  · exact polyLiftFree30_6 b
  · exact polyLiftFree30_7 b
  · exact polyLiftFree30_8 b
  · exact polyLiftFree30_9 b
  · exact polyLiftFree30_10 b
  · exact polyLiftFree30_11 b
  · exact polyLiftFree30_12 b
  · exact polyLiftFree30_13 b
  · exact polyLiftFree30_14 b
  · exact polyLiftFree30_15 b
  · exact polyLiftFree30_16 b
  · exact polyLiftFree30_17 b
  · exact polyLiftFree30_18 b
  · exact polyLiftFree30_19 b
  · exact polyLiftFree30_20 b
  · exact polyLiftFree30_21 b
  · exact polyLiftFree30_22 b
  · exact polyLiftFree30_23 b
  · exact polyLiftFree30_24 b
  · exact polyLiftFree30_25 b
  · exact polyLiftFree30_26 b
  · exact polyLiftFree30_27 b
  · exact polyLiftFree30_28 b
  · exact polyLiftFree30_29 b
  · exact polyLiftFree30_30 b
  · exact polyLiftFree30_31 b
  · exact polyLiftFree30_32 b
  · exact polyLiftFree30_33 b
  · exact polyLiftFree30_34 b
  · exact polyLiftFree30_35 b
  · exact polyLiftFree30_36 b
  · exact polyLiftFree30_37 b
  · exact polyLiftFree30_38 b
  · exact polyLiftFree30_39 b
  · exact polyLiftFree30_40 b
  · exact polyLiftFree30_41 b
  · exact polyLiftFree30_42 b
  · exact polyLiftFree30_43 b
  · exact polyLiftFree30_44 b
  · exact polyLiftFree30_45 b
  · exact polyLiftFree30_46 b
end UniserialComputations.N6
