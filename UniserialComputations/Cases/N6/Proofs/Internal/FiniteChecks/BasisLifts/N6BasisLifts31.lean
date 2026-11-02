import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift31_0 (b : Fin 3) : PolyHom 31 0 :=
  ![PolyHom.zero 31 0,PolyHom.zero 31 0,PolyHom.zero 31 0] b
theorem polyLiftFree31_0 : ∀ b : Fin 3, (polyLift31_0 b).freeBlock=basisInt (homKind 31 0) b := by decide
def polyLift31_1 (b : Fin 3) : PolyHom 31 1 :=
  ![PolyHom.zero 31 1,PolyHom.zero 31 1,PolyHom.zero 31 1] b
theorem polyLiftFree31_1 : ∀ b : Fin 3, (polyLift31_1 b).freeBlock=basisInt (homKind 31 1) b := by decide
def polyLift31_2 (b : Fin 3) : PolyHom 31 2 :=
  ![PolyHom.zero 31 2,PolyHom.zero 31 2,PolyHom.zero 31 2] b
theorem polyLiftFree31_2 : ∀ b : Fin 3, (polyLift31_2 b).freeBlock=basisInt (homKind 31 2) b := by decide
def polyRep31_3_0 : PolyHom 31 3 where
  M := !![0,0,0,0;(mono6 (-1) 1),0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![(mono6 (-1) 0),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_3 (b : Fin 3) : PolyHom 31 3 :=
  ![polyRep31_3_0,PolyHom.zero 31 3,PolyHom.zero 31 3] b
theorem polyLiftFree31_3 : ∀ b : Fin 3, (polyLift31_3 b).freeBlock=basisInt (homKind 31 3) b := by decide
def polyLift31_4 (b : Fin 3) : PolyHom 31 4 :=
  ![PolyHom.zero 31 4,PolyHom.zero 31 4,PolyHom.zero 31 4] b
theorem polyLiftFree31_4 : ∀ b : Fin 3, (polyLift31_4 b).freeBlock=basisInt (homKind 31 4) b := by decide
def polyLift31_5 (b : Fin 3) : PolyHom 31 5 :=
  ![PolyHom.zero 31 5,PolyHom.zero 31 5,PolyHom.zero 31 5] b
theorem polyLiftFree31_5 : ∀ b : Fin 3, (polyLift31_5 b).freeBlock=basisInt (homKind 31 5) b := by decide
def polyRep31_6_0 : PolyHom 31 6 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_6 (b : Fin 3) : PolyHom 31 6 :=
  ![polyRep31_6_0,PolyHom.zero 31 6,PolyHom.zero 31 6] b
theorem polyLiftFree31_6 : ∀ b : Fin 3, (polyLift31_6 b).freeBlock=basisInt (homKind 31 6) b := by decide
def polyRep31_7_0 : PolyHom 31 7 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_7 (b : Fin 3) : PolyHom 31 7 :=
  ![polyRep31_7_0,PolyHom.zero 31 7,PolyHom.zero 31 7] b
theorem polyLiftFree31_7 : ∀ b : Fin 3, (polyLift31_7 b).freeBlock=basisInt (homKind 31 7) b := by decide
def polyRep31_8_0 : PolyHom 31 8 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_8 (b : Fin 3) : PolyHom 31 8 :=
  ![polyRep31_8_0,PolyHom.zero 31 8,PolyHom.zero 31 8] b
theorem polyLiftFree31_8 : ∀ b : Fin 3, (polyLift31_8 b).freeBlock=basisInt (homKind 31 8) b := by decide
def polyRep31_9_0 : PolyHom 31 9 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_9 (b : Fin 3) : PolyHom 31 9 :=
  ![polyRep31_9_0,PolyHom.zero 31 9,PolyHom.zero 31 9] b
theorem polyLiftFree31_9 : ∀ b : Fin 3, (polyLift31_9 b).freeBlock=basisInt (homKind 31 9) b := by decide
def polyRep31_10_0 : PolyHom 31 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep31_10_1 : PolyHom 31 10 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 4),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_10 (b : Fin 3) : PolyHom 31 10 :=
  ![polyRep31_10_0,polyRep31_10_1,PolyHom.zero 31 10] b
theorem polyLiftFree31_10 : ∀ b : Fin 3, (polyLift31_10 b).freeBlock=basisInt (homKind 31 10) b := by decide
def polyRep31_11_0 : PolyHom 31 11 where
  M := !![(mono6 (1) 2),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep31_11_1 : PolyHom 31 11 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_11 (b : Fin 3) : PolyHom 31 11 :=
  ![polyRep31_11_0,polyRep31_11_1,PolyHom.zero 31 11] b
theorem polyLiftFree31_11 : ∀ b : Fin 3, (polyLift31_11 b).freeBlock=basisInt (homKind 31 11) b := by decide
def polyRep31_12_0 : PolyHom 31 12 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_12 (b : Fin 3) : PolyHom 31 12 :=
  ![polyRep31_12_0,PolyHom.zero 31 12,PolyHom.zero 31 12] b
theorem polyLiftFree31_12 : ∀ b : Fin 3, (polyLift31_12 b).freeBlock=basisInt (homKind 31 12) b := by decide
def polyRep31_13_0 : PolyHom 31 13 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_13 (b : Fin 3) : PolyHom 31 13 :=
  ![polyRep31_13_0,PolyHom.zero 31 13,PolyHom.zero 31 13] b
theorem polyLiftFree31_13 : ∀ b : Fin 3, (polyLift31_13 b).freeBlock=basisInt (homKind 31 13) b := by decide
def polyRep31_14_0 : PolyHom 31 14 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_14 (b : Fin 3) : PolyHom 31 14 :=
  ![polyRep31_14_0,PolyHom.zero 31 14,PolyHom.zero 31 14] b
theorem polyLiftFree31_14 : ∀ b : Fin 3, (polyLift31_14 b).freeBlock=basisInt (homKind 31 14) b := by decide
def polyLift31_15 (b : Fin 3) : PolyHom 31 15 :=
  ![PolyHom.zero 31 15,PolyHom.zero 31 15,PolyHom.zero 31 15] b
theorem polyLiftFree31_15 : ∀ b : Fin 3, (polyLift31_15 b).freeBlock=basisInt (homKind 31 15) b := by decide
def polyRep31_16_0 : PolyHom 31 16 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_16 (b : Fin 3) : PolyHom 31 16 :=
  ![polyRep31_16_0,PolyHom.zero 31 16,PolyHom.zero 31 16] b
theorem polyLiftFree31_16 : ∀ b : Fin 3, (polyLift31_16 b).freeBlock=basisInt (homKind 31 16) b := by decide
def polyRep31_17_0 : PolyHom 31 17 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_17 (b : Fin 3) : PolyHom 31 17 :=
  ![polyRep31_17_0,PolyHom.zero 31 17,PolyHom.zero 31 17] b
theorem polyLiftFree31_17 : ∀ b : Fin 3, (polyLift31_17 b).freeBlock=basisInt (homKind 31 17) b := by decide
def polyRep31_18_0 : PolyHom 31 18 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_18 (b : Fin 3) : PolyHom 31 18 :=
  ![polyRep31_18_0,PolyHom.zero 31 18,PolyHom.zero 31 18] b
theorem polyLiftFree31_18 : ∀ b : Fin 3, (polyLift31_18 b).freeBlock=basisInt (homKind 31 18) b := by decide
def polyRep31_19_0 : PolyHom 31 19 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_19 (b : Fin 3) : PolyHom 31 19 :=
  ![polyRep31_19_0,PolyHom.zero 31 19,PolyHom.zero 31 19] b
theorem polyLiftFree31_19 : ∀ b : Fin 3, (polyLift31_19 b).freeBlock=basisInt (homKind 31 19) b := by decide
def polyRep31_20_0 : PolyHom 31 20 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_20 (b : Fin 3) : PolyHom 31 20 :=
  ![polyRep31_20_0,PolyHom.zero 31 20,PolyHom.zero 31 20] b
theorem polyLiftFree31_20 : ∀ b : Fin 3, (polyLift31_20 b).freeBlock=basisInt (homKind 31 20) b := by decide
def polyRep31_21_0 : PolyHom 31 21 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep31_21_1 : PolyHom 31 21 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_21 (b : Fin 3) : PolyHom 31 21 :=
  ![polyRep31_21_0,polyRep31_21_1,PolyHom.zero 31 21] b
theorem polyLiftFree31_21 : ∀ b : Fin 3, (polyLift31_21 b).freeBlock=basisInt (homKind 31 21) b := by decide
def polyRep31_22_0 : PolyHom 31 22 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_22 (b : Fin 3) : PolyHom 31 22 :=
  ![polyRep31_22_0,PolyHom.zero 31 22,PolyHom.zero 31 22] b
theorem polyLiftFree31_22 : ∀ b : Fin 3, (polyLift31_22 b).freeBlock=basisInt (homKind 31 22) b := by decide
def polyRep31_23_0 : PolyHom 31 23 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_23 (b : Fin 3) : PolyHom 31 23 :=
  ![polyRep31_23_0,PolyHom.zero 31 23,PolyHom.zero 31 23] b
theorem polyLiftFree31_23 : ∀ b : Fin 3, (polyLift31_23 b).freeBlock=basisInt (homKind 31 23) b := by decide
def polyRep31_24_0 : PolyHom 31 24 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 1),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep31_24_1 : PolyHom 31 24 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_24 (b : Fin 3) : PolyHom 31 24 :=
  ![polyRep31_24_0,polyRep31_24_1,PolyHom.zero 31 24] b
theorem polyLiftFree31_24 : ∀ b : Fin 3, (polyLift31_24 b).freeBlock=basisInt (homKind 31 24) b := by decide
def polyRep31_25_0 : PolyHom 31 25 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep31_25_1 : PolyHom 31 25 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_25 (b : Fin 3) : PolyHom 31 25 :=
  ![polyRep31_25_0,polyRep31_25_1,PolyHom.zero 31 25] b
theorem polyLiftFree31_25 : ∀ b : Fin 3, (polyLift31_25 b).freeBlock=basisInt (homKind 31 25) b := by decide
def polyRep31_26_0 : PolyHom 31 26 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_26 (b : Fin 3) : PolyHom 31 26 :=
  ![polyRep31_26_0,PolyHom.zero 31 26,PolyHom.zero 31 26] b
theorem polyLiftFree31_26 : ∀ b : Fin 3, (polyLift31_26 b).freeBlock=basisInt (homKind 31 26) b := by decide
def polyRep31_27_0 : PolyHom 31 27 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_27 (b : Fin 3) : PolyHom 31 27 :=
  ![polyRep31_27_0,PolyHom.zero 31 27,PolyHom.zero 31 27] b
theorem polyLiftFree31_27 : ∀ b : Fin 3, (polyLift31_27 b).freeBlock=basisInt (homKind 31 27) b := by decide
def polyRep31_28_0 : PolyHom 31 28 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_28 (b : Fin 3) : PolyHom 31 28 :=
  ![polyRep31_28_0,PolyHom.zero 31 28,PolyHom.zero 31 28] b
theorem polyLiftFree31_28 : ∀ b : Fin 3, (polyLift31_28 b).freeBlock=basisInt (homKind 31 28) b := by decide
def polyRep31_29_0 : PolyHom 31 29 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_29 (b : Fin 3) : PolyHom 31 29 :=
  ![polyRep31_29_0,PolyHom.zero 31 29,PolyHom.zero 31 29] b
theorem polyLiftFree31_29 : ∀ b : Fin 3, (polyLift31_29 b).freeBlock=basisInt (homKind 31 29) b := by decide
def polyRep31_30_0 : PolyHom 31 30 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep31_30_1 : PolyHom 31 30 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_30 (b : Fin 3) : PolyHom 31 30 :=
  ![polyRep31_30_0,polyRep31_30_1,PolyHom.zero 31 30] b
theorem polyLiftFree31_30 : ∀ b : Fin 3, (polyLift31_30 b).freeBlock=basisInt (homKind 31 30) b := by decide
def polyRep31_31_0 : PolyHom 31 31 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep31_31_1 : PolyHom 31 31 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_31 (b : Fin 3) : PolyHom 31 31 :=
  ![polyRep31_31_0,polyRep31_31_1,PolyHom.zero 31 31] b
theorem polyLiftFree31_31 : ∀ b : Fin 3, (polyLift31_31 b).freeBlock=basisInt (homKind 31 31) b := by decide
def polyRep31_32_0 : PolyHom 31 32 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0]
  U := !![0,0;(mono6 (1) 2),(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_32 (b : Fin 3) : PolyHom 31 32 :=
  ![polyRep31_32_0,PolyHom.zero 31 32,PolyHom.zero 31 32] b
theorem polyLiftFree31_32 : ∀ b : Fin 3, (polyLift31_32 b).freeBlock=basisInt (homKind 31 32) b := by decide
def polyRep31_33_0 : PolyHom 31 33 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_33 (b : Fin 3) : PolyHom 31 33 :=
  ![polyRep31_33_0,PolyHom.zero 31 33,PolyHom.zero 31 33] b
theorem polyLiftFree31_33 : ∀ b : Fin 3, (polyLift31_33 b).freeBlock=basisInt (homKind 31 33) b := by decide
def polyRep31_34_0 : PolyHom 31 34 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_34 (b : Fin 3) : PolyHom 31 34 :=
  ![polyRep31_34_0,PolyHom.zero 31 34,PolyHom.zero 31 34] b
theorem polyLiftFree31_34 : ∀ b : Fin 3, (polyLift31_34 b).freeBlock=basisInt (homKind 31 34) b := by decide
def polyRep31_35_0 : PolyHom 31 35 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_35 (b : Fin 3) : PolyHom 31 35 :=
  ![polyRep31_35_0,PolyHom.zero 31 35,PolyHom.zero 31 35] b
theorem polyLiftFree31_35 : ∀ b : Fin 3, (polyLift31_35 b).freeBlock=basisInt (homKind 31 35) b := by decide
def polyRep31_36_0 : PolyHom 31 36 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_36 (b : Fin 3) : PolyHom 31 36 :=
  ![polyRep31_36_0,PolyHom.zero 31 36,PolyHom.zero 31 36] b
theorem polyLiftFree31_36 : ∀ b : Fin 3, (polyLift31_36 b).freeBlock=basisInt (homKind 31 36) b := by decide
def polyRep31_37_0 : PolyHom 31 37 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep31_37_1 : PolyHom 31 37 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_37 (b : Fin 3) : PolyHom 31 37 :=
  ![polyRep31_37_0,polyRep31_37_1,PolyHom.zero 31 37] b
theorem polyLiftFree31_37 : ∀ b : Fin 3, (polyLift31_37 b).freeBlock=basisInt (homKind 31 37) b := by decide
def polyRep31_38_0 : PolyHom 31 38 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0]
  U := !![0,0;(mono6 (1) 2),(mono6 (1) 2)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_38 (b : Fin 3) : PolyHom 31 38 :=
  ![polyRep31_38_0,PolyHom.zero 31 38,PolyHom.zero 31 38] b
theorem polyLiftFree31_38 : ∀ b : Fin 3, (polyLift31_38 b).freeBlock=basisInt (homKind 31 38) b := by decide
def polyRep31_39_0 : PolyHom 31 39 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0]
  U := !![0,0;(mono6 (1) 2),(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_39 (b : Fin 3) : PolyHom 31 39 :=
  ![polyRep31_39_0,PolyHom.zero 31 39,PolyHom.zero 31 39] b
theorem polyLiftFree31_39 : ∀ b : Fin 3, (polyLift31_39 b).freeBlock=basisInt (homKind 31 39) b := by decide
def polyRep31_40_0 : PolyHom 31 40 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep31_40_1 : PolyHom 31 40 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_40 (b : Fin 3) : PolyHom 31 40 :=
  ![polyRep31_40_0,polyRep31_40_1,PolyHom.zero 31 40] b
theorem polyLiftFree31_40 : ∀ b : Fin 3, (polyLift31_40 b).freeBlock=basisInt (homKind 31 40) b := by decide
def polyRep31_41_0 : PolyHom 31 41 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0]
  U := !![0,0;(mono6 (1) 2),(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_41 (b : Fin 3) : PolyHom 31 41 :=
  ![polyRep31_41_0,PolyHom.zero 31 41,PolyHom.zero 31 41] b
theorem polyLiftFree31_41 : ∀ b : Fin 3, (polyLift31_41 b).freeBlock=basisInt (homKind 31 41) b := by decide
def polyRep31_42_0 : PolyHom 31 42 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep31_42_1 : PolyHom 31 42 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep31_42_2 : PolyHom 31 42 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_42 (b : Fin 3) : PolyHom 31 42 :=
  ![polyRep31_42_0,polyRep31_42_1,polyRep31_42_2] b
theorem polyLiftFree31_42 : ∀ b : Fin 3, (polyLift31_42 b).freeBlock=basisInt (homKind 31 42) b := by decide
def polyRep31_43_0 : PolyHom 31 43 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep31_43_1 : PolyHom 31 43 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_43 (b : Fin 3) : PolyHom 31 43 :=
  ![polyRep31_43_0,polyRep31_43_1,PolyHom.zero 31 43] b
theorem polyLiftFree31_43 : ∀ b : Fin 3, (polyLift31_43 b).freeBlock=basisInt (homKind 31 43) b := by decide
def polyRep31_44_0 : PolyHom 31 44 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep31_44_1 : PolyHom 31 44 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep31_44_2 : PolyHom 31 44 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_44 (b : Fin 3) : PolyHom 31 44 :=
  ![polyRep31_44_0,polyRep31_44_1,polyRep31_44_2] b
theorem polyLiftFree31_44 : ∀ b : Fin 3, (polyLift31_44 b).freeBlock=basisInt (homKind 31 44) b := by decide
def polyRep31_45_0 : PolyHom 31 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep31_45_1 : PolyHom 31 45 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift31_45 (b : Fin 3) : PolyHom 31 45 :=
  ![polyRep31_45_0,polyRep31_45_1,PolyHom.zero 31 45] b
theorem polyLiftFree31_45 : ∀ b : Fin 3, (polyLift31_45 b).freeBlock=basisInt (homKind 31 45) b := by decide
def polyLift31_46 (b : Fin 3) : PolyHom 31 46 :=
  ![PolyHom.zero 31 46,PolyHom.zero 31 46,PolyHom.zero 31 46] b
theorem polyLiftFree31_46 : ∀ b : Fin 3, (polyLift31_46 b).freeBlock=basisInt (homKind 31 46) b := by decide
def polyLiftRow31 (j : Fin 47) (b : Fin 3) : PolyHom 31 j :=
  match j with
  | ⟨0,_⟩ => polyLift31_0 b
  | ⟨1,_⟩ => polyLift31_1 b
  | ⟨2,_⟩ => polyLift31_2 b
  | ⟨3,_⟩ => polyLift31_3 b
  | ⟨4,_⟩ => polyLift31_4 b
  | ⟨5,_⟩ => polyLift31_5 b
  | ⟨6,_⟩ => polyLift31_6 b
  | ⟨7,_⟩ => polyLift31_7 b
  | ⟨8,_⟩ => polyLift31_8 b
  | ⟨9,_⟩ => polyLift31_9 b
  | ⟨10,_⟩ => polyLift31_10 b
  | ⟨11,_⟩ => polyLift31_11 b
  | ⟨12,_⟩ => polyLift31_12 b
  | ⟨13,_⟩ => polyLift31_13 b
  | ⟨14,_⟩ => polyLift31_14 b
  | ⟨15,_⟩ => polyLift31_15 b
  | ⟨16,_⟩ => polyLift31_16 b
  | ⟨17,_⟩ => polyLift31_17 b
  | ⟨18,_⟩ => polyLift31_18 b
  | ⟨19,_⟩ => polyLift31_19 b
  | ⟨20,_⟩ => polyLift31_20 b
  | ⟨21,_⟩ => polyLift31_21 b
  | ⟨22,_⟩ => polyLift31_22 b
  | ⟨23,_⟩ => polyLift31_23 b
  | ⟨24,_⟩ => polyLift31_24 b
  | ⟨25,_⟩ => polyLift31_25 b
  | ⟨26,_⟩ => polyLift31_26 b
  | ⟨27,_⟩ => polyLift31_27 b
  | ⟨28,_⟩ => polyLift31_28 b
  | ⟨29,_⟩ => polyLift31_29 b
  | ⟨30,_⟩ => polyLift31_30 b
  | ⟨31,_⟩ => polyLift31_31 b
  | ⟨32,_⟩ => polyLift31_32 b
  | ⟨33,_⟩ => polyLift31_33 b
  | ⟨34,_⟩ => polyLift31_34 b
  | ⟨35,_⟩ => polyLift31_35 b
  | ⟨36,_⟩ => polyLift31_36 b
  | ⟨37,_⟩ => polyLift31_37 b
  | ⟨38,_⟩ => polyLift31_38 b
  | ⟨39,_⟩ => polyLift31_39 b
  | ⟨40,_⟩ => polyLift31_40 b
  | ⟨41,_⟩ => polyLift31_41 b
  | ⟨42,_⟩ => polyLift31_42 b
  | ⟨43,_⟩ => polyLift31_43 b
  | ⟨44,_⟩ => polyLift31_44 b
  | ⟨45,_⟩ => polyLift31_45 b
  | ⟨46,_⟩ => polyLift31_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree31 (j : Fin 47) (b : Fin 3) : (polyLiftRow31 j b).freeBlock=basisInt (homKind 31 j) b := by
  fin_cases j
  · exact polyLiftFree31_0 b
  · exact polyLiftFree31_1 b
  · exact polyLiftFree31_2 b
  · exact polyLiftFree31_3 b
  · exact polyLiftFree31_4 b
  · exact polyLiftFree31_5 b
  · exact polyLiftFree31_6 b
  · exact polyLiftFree31_7 b
  · exact polyLiftFree31_8 b
  · exact polyLiftFree31_9 b
  · exact polyLiftFree31_10 b
  · exact polyLiftFree31_11 b
  · exact polyLiftFree31_12 b
  · exact polyLiftFree31_13 b
  · exact polyLiftFree31_14 b
  · exact polyLiftFree31_15 b
  · exact polyLiftFree31_16 b
  · exact polyLiftFree31_17 b
  · exact polyLiftFree31_18 b
  · exact polyLiftFree31_19 b
  · exact polyLiftFree31_20 b
  · exact polyLiftFree31_21 b
  · exact polyLiftFree31_22 b
  · exact polyLiftFree31_23 b
  · exact polyLiftFree31_24 b
  · exact polyLiftFree31_25 b
  · exact polyLiftFree31_26 b
  · exact polyLiftFree31_27 b
  · exact polyLiftFree31_28 b
  · exact polyLiftFree31_29 b
  · exact polyLiftFree31_30 b
  · exact polyLiftFree31_31 b
  · exact polyLiftFree31_32 b
  · exact polyLiftFree31_33 b
  · exact polyLiftFree31_34 b
  · exact polyLiftFree31_35 b
  · exact polyLiftFree31_36 b
  · exact polyLiftFree31_37 b
  · exact polyLiftFree31_38 b
  · exact polyLiftFree31_39 b
  · exact polyLiftFree31_40 b
  · exact polyLiftFree31_41 b
  · exact polyLiftFree31_42 b
  · exact polyLiftFree31_43 b
  · exact polyLiftFree31_44 b
  · exact polyLiftFree31_45 b
  · exact polyLiftFree31_46 b
end UniserialComputations.N6
