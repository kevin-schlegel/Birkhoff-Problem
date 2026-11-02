import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift43_0 (b : Fin 3) : PolyHom 43 0 :=
  ![PolyHom.zero 43 0,PolyHom.zero 43 0,PolyHom.zero 43 0] b
theorem polyLiftFree43_0 : ∀ b : Fin 3, (polyLift43_0 b).freeBlock=basisInt (homKind 43 0) b := by decide
def polyLift43_1 (b : Fin 3) : PolyHom 43 1 :=
  ![PolyHom.zero 43 1,PolyHom.zero 43 1,PolyHom.zero 43 1] b
theorem polyLiftFree43_1 : ∀ b : Fin 3, (polyLift43_1 b).freeBlock=basisInt (homKind 43 1) b := by decide
def polyLift43_2 (b : Fin 3) : PolyHom 43 2 :=
  ![PolyHom.zero 43 2,PolyHom.zero 43 2,PolyHom.zero 43 2] b
theorem polyLiftFree43_2 : ∀ b : Fin 3, (polyLift43_2 b).freeBlock=basisInt (homKind 43 2) b := by decide
def polyLift43_3 (b : Fin 3) : PolyHom 43 3 :=
  ![PolyHom.zero 43 3,PolyHom.zero 43 3,PolyHom.zero 43 3] b
theorem polyLiftFree43_3 : ∀ b : Fin 3, (polyLift43_3 b).freeBlock=basisInt (homKind 43 3) b := by decide
def polyLift43_4 (b : Fin 3) : PolyHom 43 4 :=
  ![PolyHom.zero 43 4,PolyHom.zero 43 4,PolyHom.zero 43 4] b
theorem polyLiftFree43_4 : ∀ b : Fin 3, (polyLift43_4 b).freeBlock=basisInt (homKind 43 4) b := by decide
def polyLift43_5 (b : Fin 3) : PolyHom 43 5 :=
  ![PolyHom.zero 43 5,PolyHom.zero 43 5,PolyHom.zero 43 5] b
theorem polyLiftFree43_5 : ∀ b : Fin 3, (polyLift43_5 b).freeBlock=basisInt (homKind 43 5) b := by decide
def polyRep43_6_0 : PolyHom 43 6 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;(mono6 (-1) 0),0,0,0]
  U := !![(mono6 (1) 1),0;(mono6 (-1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_6 (b : Fin 3) : PolyHom 43 6 :=
  ![polyRep43_6_0,PolyHom.zero 43 6,PolyHom.zero 43 6] b
theorem polyLiftFree43_6 : ∀ b : Fin 3, (polyLift43_6 b).freeBlock=basisInt (homKind 43 6) b := by decide
def polyRep43_7_0 : PolyHom 43 7 where
  M := !![0,0,0,0;(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,(mono6 (-1) 0),0,0]
  U := !![(mono6 (1) 0),0;(mono6 (-1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_7 (b : Fin 3) : PolyHom 43 7 :=
  ![polyRep43_7_0,PolyHom.zero 43 7,PolyHom.zero 43 7] b
theorem polyLiftFree43_7 : ∀ b : Fin 3, (polyLift43_7 b).freeBlock=basisInt (homKind 43 7) b := by decide
def polyLift43_8 (b : Fin 3) : PolyHom 43 8 :=
  ![PolyHom.zero 43 8,PolyHom.zero 43 8,PolyHom.zero 43 8] b
theorem polyLiftFree43_8 : ∀ b : Fin 3, (polyLift43_8 b).freeBlock=basisInt (homKind 43 8) b := by decide
def polyLift43_9 (b : Fin 3) : PolyHom 43 9 :=
  ![PolyHom.zero 43 9,PolyHom.zero 43 9,PolyHom.zero 43 9] b
theorem polyLiftFree43_9 : ∀ b : Fin 3, (polyLift43_9 b).freeBlock=basisInt (homKind 43 9) b := by decide
def polyRep43_10_0 : PolyHom 43 10 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep43_10_1 : PolyHom 43 10 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_10 (b : Fin 3) : PolyHom 43 10 :=
  ![polyRep43_10_0,polyRep43_10_1,PolyHom.zero 43 10] b
theorem polyLiftFree43_10 : ∀ b : Fin 3, (polyLift43_10 b).freeBlock=basisInt (homKind 43 10) b := by decide
def polyRep43_11_0 : PolyHom 43 11 where
  M := !![(mono6 (1) 3),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep43_11_1 : PolyHom 43 11 where
  M := !![(mono6 (1) 3),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_11 (b : Fin 3) : PolyHom 43 11 :=
  ![polyRep43_11_0,polyRep43_11_1,PolyHom.zero 43 11] b
theorem polyLiftFree43_11 : ∀ b : Fin 3, (polyLift43_11 b).freeBlock=basisInt (homKind 43 11) b := by decide
def polyRep43_12_0 : PolyHom 43 12 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep43_12_1 : PolyHom 43 12 where
  M := !![(mono6 (1) 2),0,0,0;(mono6 (-1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_12 (b : Fin 3) : PolyHom 43 12 :=
  ![polyRep43_12_0,polyRep43_12_1,PolyHom.zero 43 12] b
theorem polyLiftFree43_12 : ∀ b : Fin 3, (polyLift43_12 b).freeBlock=basisInt (homKind 43 12) b := by decide
def polyRep43_13_0 : PolyHom 43 13 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_13 (b : Fin 3) : PolyHom 43 13 :=
  ![polyRep43_13_0,PolyHom.zero 43 13,PolyHom.zero 43 13] b
theorem polyLiftFree43_13 : ∀ b : Fin 3, (polyLift43_13 b).freeBlock=basisInt (homKind 43 13) b := by decide
def polyLift43_14 (b : Fin 3) : PolyHom 43 14 :=
  ![PolyHom.zero 43 14,PolyHom.zero 43 14,PolyHom.zero 43 14] b
theorem polyLiftFree43_14 : ∀ b : Fin 3, (polyLift43_14 b).freeBlock=basisInt (homKind 43 14) b := by decide
def polyLift43_15 (b : Fin 3) : PolyHom 43 15 :=
  ![PolyHom.zero 43 15,PolyHom.zero 43 15,PolyHom.zero 43 15] b
theorem polyLiftFree43_15 : ∀ b : Fin 3, (polyLift43_15 b).freeBlock=basisInt (homKind 43 15) b := by decide
def polyRep43_16_0 : PolyHom 43 16 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,(mono6 (-1) 0),0,0]
  U := !![(mono6 (1) 0),0;(mono6 (-1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_16 (b : Fin 3) : PolyHom 43 16 :=
  ![polyRep43_16_0,PolyHom.zero 43 16,PolyHom.zero 43 16] b
theorem polyLiftFree43_16 : ∀ b : Fin 3, (polyLift43_16 b).freeBlock=basisInt (homKind 43 16) b := by decide
def polyLift43_17 (b : Fin 3) : PolyHom 43 17 :=
  ![PolyHom.zero 43 17,PolyHom.zero 43 17,PolyHom.zero 43 17] b
theorem polyLiftFree43_17 : ∀ b : Fin 3, (polyLift43_17 b).freeBlock=basisInt (homKind 43 17) b := by decide
def polyRep43_18_0 : PolyHom 43 18 where
  M := !![0,0,(mono6 (1) 0),0;(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,(mono6 (-1) 0),(mono6 (-1) 1),0]
  U := !![(mono6 (1) 0),0;(mono6 (-1) 1),(mono6 (-1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_18 (b : Fin 3) : PolyHom 43 18 :=
  ![polyRep43_18_0,PolyHom.zero 43 18,PolyHom.zero 43 18] b
theorem polyLiftFree43_18 : ∀ b : Fin 3, (polyLift43_18 b).freeBlock=basisInt (homKind 43 18) b := by decide
def polyLift43_19 (b : Fin 3) : PolyHom 43 19 :=
  ![PolyHom.zero 43 19,PolyHom.zero 43 19,PolyHom.zero 43 19] b
theorem polyLiftFree43_19 : ∀ b : Fin 3, (polyLift43_19 b).freeBlock=basisInt (homKind 43 19) b := by decide
def polyLift43_20 (b : Fin 3) : PolyHom 43 20 :=
  ![PolyHom.zero 43 20,PolyHom.zero 43 20,PolyHom.zero 43 20] b
theorem polyLiftFree43_20 : ∀ b : Fin 3, (polyLift43_20 b).freeBlock=basisInt (homKind 43 20) b := by decide
def polyRep43_21_0 : PolyHom 43 21 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep43_21_1 : PolyHom 43 21 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_21 (b : Fin 3) : PolyHom 43 21 :=
  ![polyRep43_21_0,polyRep43_21_1,PolyHom.zero 43 21] b
theorem polyLiftFree43_21 : ∀ b : Fin 3, (polyLift43_21 b).freeBlock=basisInt (homKind 43 21) b := by decide
def polyRep43_22_0 : PolyHom 43 22 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep43_22_1 : PolyHom 43 22 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_22 (b : Fin 3) : PolyHom 43 22 :=
  ![polyRep43_22_0,polyRep43_22_1,PolyHom.zero 43 22] b
theorem polyLiftFree43_22 : ∀ b : Fin 3, (polyLift43_22 b).freeBlock=basisInt (homKind 43 22) b := by decide
def polyLift43_23 (b : Fin 3) : PolyHom 43 23 :=
  ![PolyHom.zero 43 23,PolyHom.zero 43 23,PolyHom.zero 43 23] b
theorem polyLiftFree43_23 : ∀ b : Fin 3, (polyLift43_23 b).freeBlock=basisInt (homKind 43 23) b := by decide
def polyRep43_24_0 : PolyHom 43 24 where
  M := !![(mono6 (1) 2),0,(mono6 (1) 1),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep43_24_1 : PolyHom 43 24 where
  M := !![(mono6 (1) 2),0,(mono6 (1) 1),0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_24 (b : Fin 3) : PolyHom 43 24 :=
  ![polyRep43_24_0,polyRep43_24_1,PolyHom.zero 43 24] b
theorem polyLiftFree43_24 : ∀ b : Fin 3, (polyLift43_24 b).freeBlock=basisInt (homKind 43 24) b := by decide
def polyRep43_25_0 : PolyHom 43 25 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep43_25_1 : PolyHom 43 25 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_25 (b : Fin 3) : PolyHom 43 25 :=
  ![polyRep43_25_0,polyRep43_25_1,PolyHom.zero 43 25] b
theorem polyLiftFree43_25 : ∀ b : Fin 3, (polyLift43_25 b).freeBlock=basisInt (homKind 43 25) b := by decide
def polyRep43_26_0 : PolyHom 43 26 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep43_26_1 : PolyHom 43 26 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0]
  U := !![0,0;(mono6 (1) 1),(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_26 (b : Fin 3) : PolyHom 43 26 :=
  ![polyRep43_26_0,polyRep43_26_1,PolyHom.zero 43 26] b
theorem polyLiftFree43_26 : ∀ b : Fin 3, (polyLift43_26 b).freeBlock=basisInt (homKind 43 26) b := by decide
def polyRep43_27_0 : PolyHom 43 27 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep43_27_1 : PolyHom 43 27 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_27 (b : Fin 3) : PolyHom 43 27 :=
  ![polyRep43_27_0,polyRep43_27_1,PolyHom.zero 43 27] b
theorem polyLiftFree43_27 : ∀ b : Fin 3, (polyLift43_27 b).freeBlock=basisInt (homKind 43 27) b := by decide
def polyRep43_28_0 : PolyHom 43 28 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_28 (b : Fin 3) : PolyHom 43 28 :=
  ![polyRep43_28_0,PolyHom.zero 43 28,PolyHom.zero 43 28] b
theorem polyLiftFree43_28 : ∀ b : Fin 3, (polyLift43_28 b).freeBlock=basisInt (homKind 43 28) b := by decide
def polyLift43_29 (b : Fin 3) : PolyHom 43 29 :=
  ![PolyHom.zero 43 29,PolyHom.zero 43 29,PolyHom.zero 43 29] b
theorem polyLiftFree43_29 : ∀ b : Fin 3, (polyLift43_29 b).freeBlock=basisInt (homKind 43 29) b := by decide
def polyRep43_30_0 : PolyHom 43 30 where
  M := !![(mono6 (1) 2),0,0,0;(mono6 (-1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 1),0]
  U := !![(mono6 (1) 1),0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep43_30_1 : PolyHom 43 30 where
  M := !![(mono6 (1) 2),0,0,0;(mono6 (-1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0]
  U := !![0,0;(mono6 (1) 2),(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_30 (b : Fin 3) : PolyHom 43 30 :=
  ![polyRep43_30_0,polyRep43_30_1,PolyHom.zero 43 30] b
theorem polyLiftFree43_30 : ∀ b : Fin 3, (polyLift43_30 b).freeBlock=basisInt (homKind 43 30) b := by decide
def polyRep43_31_0 : PolyHom 43 31 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep43_31_1 : PolyHom 43 31 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_31 (b : Fin 3) : PolyHom 43 31 :=
  ![polyRep43_31_0,polyRep43_31_1,PolyHom.zero 43 31] b
theorem polyLiftFree43_31 : ∀ b : Fin 3, (polyLift43_31 b).freeBlock=basisInt (homKind 43 31) b := by decide
def polyRep43_32_0 : PolyHom 43 32 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep43_32_1 : PolyHom 43 32 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,(mono6 (1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_32 (b : Fin 3) : PolyHom 43 32 :=
  ![polyRep43_32_0,polyRep43_32_1,PolyHom.zero 43 32] b
theorem polyLiftFree43_32 : ∀ b : Fin 3, (polyLift43_32 b).freeBlock=basisInt (homKind 43 32) b := by decide
def polyRep43_33_0 : PolyHom 43 33 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep43_33_1 : PolyHom 43 33 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_33 (b : Fin 3) : PolyHom 43 33 :=
  ![polyRep43_33_0,polyRep43_33_1,PolyHom.zero 43 33] b
theorem polyLiftFree43_33 : ∀ b : Fin 3, (polyLift43_33 b).freeBlock=basisInt (homKind 43 33) b := by decide
def polyRep43_34_0 : PolyHom 43 34 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep43_34_1 : PolyHom 43 34 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_34 (b : Fin 3) : PolyHom 43 34 :=
  ![polyRep43_34_0,polyRep43_34_1,PolyHom.zero 43 34] b
theorem polyLiftFree43_34 : ∀ b : Fin 3, (polyLift43_34 b).freeBlock=basisInt (homKind 43 34) b := by decide
def polyRep43_35_0 : PolyHom 43 35 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_35 (b : Fin 3) : PolyHom 43 35 :=
  ![polyRep43_35_0,PolyHom.zero 43 35,PolyHom.zero 43 35] b
theorem polyLiftFree43_35 : ∀ b : Fin 3, (polyLift43_35 b).freeBlock=basisInt (homKind 43 35) b := by decide
def polyRep43_36_0 : PolyHom 43 36 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep43_36_1 : PolyHom 43 36 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_36 (b : Fin 3) : PolyHom 43 36 :=
  ![polyRep43_36_0,polyRep43_36_1,PolyHom.zero 43 36] b
theorem polyLiftFree43_36 : ∀ b : Fin 3, (polyLift43_36 b).freeBlock=basisInt (homKind 43 36) b := by decide
def polyRep43_37_0 : PolyHom 43 37 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 1),0]
  U := !![(mono6 (1) 1),0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep43_37_1 : PolyHom 43 37 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0]
  U := !![0,0;(mono6 (1) 2),(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_37 (b : Fin 3) : PolyHom 43 37 :=
  ![polyRep43_37_0,polyRep43_37_1,PolyHom.zero 43 37] b
theorem polyLiftFree43_37 : ∀ b : Fin 3, (polyLift43_37 b).freeBlock=basisInt (homKind 43 37) b := by decide
def polyRep43_38_0 : PolyHom 43 38 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep43_38_1 : PolyHom 43 38 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,(mono6 (1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_38 (b : Fin 3) : PolyHom 43 38 :=
  ![polyRep43_38_0,polyRep43_38_1,PolyHom.zero 43 38] b
theorem polyLiftFree43_38 : ∀ b : Fin 3, (polyLift43_38 b).freeBlock=basisInt (homKind 43 38) b := by decide
def polyRep43_39_0 : PolyHom 43 39 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep43_39_1 : PolyHom 43 39 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,(mono6 (1) 0),0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_39 (b : Fin 3) : PolyHom 43 39 :=
  ![polyRep43_39_0,polyRep43_39_1,PolyHom.zero 43 39] b
theorem polyLiftFree43_39 : ∀ b : Fin 3, (polyLift43_39 b).freeBlock=basisInt (homKind 43 39) b := by decide
def polyRep43_40_0 : PolyHom 43 40 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep43_40_1 : PolyHom 43 40 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_40 (b : Fin 3) : PolyHom 43 40 :=
  ![polyRep43_40_0,polyRep43_40_1,PolyHom.zero 43 40] b
theorem polyLiftFree43_40 : ∀ b : Fin 3, (polyLift43_40 b).freeBlock=basisInt (homKind 43 40) b := by decide
def polyRep43_41_0 : PolyHom 43 41 where
  M := !![(mono6 (1) 0),0,0,(mono6 (1) 0);0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep43_41_1 : PolyHom 43 41 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1)]
  U := !![0,0;(mono6 (1) 1),(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_41 (b : Fin 3) : PolyHom 43 41 :=
  ![polyRep43_41_0,polyRep43_41_1,PolyHom.zero 43 41] b
theorem polyLiftFree43_41 : ∀ b : Fin 3, (polyLift43_41 b).freeBlock=basisInt (homKind 43 41) b := by decide
def polyRep43_42_0 : PolyHom 43 42 where
  M := !![0,(mono6 (1) 2),0,0;0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,(mono6 (-1) 1)]
  U := !![(mono6 (1) 1),0;0,(mono6 (-1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep43_42_1 : PolyHom 43 42 where
  M := !![0,(mono6 (1) 2),0,0;0,(mono6 (-1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),(mono6 (-1) 1)]
  U := !![0,0;(mono6 (1) 2),(mono6 (-1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_42 (b : Fin 3) : PolyHom 43 42 :=
  ![polyRep43_42_0,polyRep43_42_1,PolyHom.zero 43 42] b
theorem polyLiftFree43_42 : ∀ b : Fin 3, (polyLift43_42 b).freeBlock=basisInt (homKind 43 42) b := by decide
def polyRep43_43_0 : PolyHom 43 43 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,(mono6 (1) 0)]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_43 (b : Fin 3) : PolyHom 43 43 :=
  ![polyRep43_43_0,PolyHom.zero 43 43,PolyHom.zero 43 43] b
theorem polyLiftFree43_43 : ∀ b : Fin 3, (polyLift43_43 b).freeBlock=basisInt (homKind 43 43) b := by decide
def polyRep43_44_0 : PolyHom 43 44 where
  M := !![(mono6 (1) 1),(mono6 (1) 2),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep43_44_1 : PolyHom 43 44 where
  M := !![(mono6 (1) 1),(mono6 (1) 2),0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_44 (b : Fin 3) : PolyHom 43 44 :=
  ![polyRep43_44_0,polyRep43_44_1,PolyHom.zero 43 44] b
theorem polyLiftFree43_44 : ∀ b : Fin 3, (polyLift43_44 b).freeBlock=basisInt (homKind 43 44) b := by decide
def polyRep43_45_0 : PolyHom 43 45 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep43_45_1 : PolyHom 43 45 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift43_45 (b : Fin 3) : PolyHom 43 45 :=
  ![polyRep43_45_0,polyRep43_45_1,PolyHom.zero 43 45] b
theorem polyLiftFree43_45 : ∀ b : Fin 3, (polyLift43_45 b).freeBlock=basisInt (homKind 43 45) b := by decide
def polyLift43_46 (b : Fin 3) : PolyHom 43 46 :=
  ![PolyHom.zero 43 46,PolyHom.zero 43 46,PolyHom.zero 43 46] b
theorem polyLiftFree43_46 : ∀ b : Fin 3, (polyLift43_46 b).freeBlock=basisInt (homKind 43 46) b := by decide
def polyLiftRow43 (j : Fin 47) (b : Fin 3) : PolyHom 43 j :=
  match j with
  | ⟨0,_⟩ => polyLift43_0 b
  | ⟨1,_⟩ => polyLift43_1 b
  | ⟨2,_⟩ => polyLift43_2 b
  | ⟨3,_⟩ => polyLift43_3 b
  | ⟨4,_⟩ => polyLift43_4 b
  | ⟨5,_⟩ => polyLift43_5 b
  | ⟨6,_⟩ => polyLift43_6 b
  | ⟨7,_⟩ => polyLift43_7 b
  | ⟨8,_⟩ => polyLift43_8 b
  | ⟨9,_⟩ => polyLift43_9 b
  | ⟨10,_⟩ => polyLift43_10 b
  | ⟨11,_⟩ => polyLift43_11 b
  | ⟨12,_⟩ => polyLift43_12 b
  | ⟨13,_⟩ => polyLift43_13 b
  | ⟨14,_⟩ => polyLift43_14 b
  | ⟨15,_⟩ => polyLift43_15 b
  | ⟨16,_⟩ => polyLift43_16 b
  | ⟨17,_⟩ => polyLift43_17 b
  | ⟨18,_⟩ => polyLift43_18 b
  | ⟨19,_⟩ => polyLift43_19 b
  | ⟨20,_⟩ => polyLift43_20 b
  | ⟨21,_⟩ => polyLift43_21 b
  | ⟨22,_⟩ => polyLift43_22 b
  | ⟨23,_⟩ => polyLift43_23 b
  | ⟨24,_⟩ => polyLift43_24 b
  | ⟨25,_⟩ => polyLift43_25 b
  | ⟨26,_⟩ => polyLift43_26 b
  | ⟨27,_⟩ => polyLift43_27 b
  | ⟨28,_⟩ => polyLift43_28 b
  | ⟨29,_⟩ => polyLift43_29 b
  | ⟨30,_⟩ => polyLift43_30 b
  | ⟨31,_⟩ => polyLift43_31 b
  | ⟨32,_⟩ => polyLift43_32 b
  | ⟨33,_⟩ => polyLift43_33 b
  | ⟨34,_⟩ => polyLift43_34 b
  | ⟨35,_⟩ => polyLift43_35 b
  | ⟨36,_⟩ => polyLift43_36 b
  | ⟨37,_⟩ => polyLift43_37 b
  | ⟨38,_⟩ => polyLift43_38 b
  | ⟨39,_⟩ => polyLift43_39 b
  | ⟨40,_⟩ => polyLift43_40 b
  | ⟨41,_⟩ => polyLift43_41 b
  | ⟨42,_⟩ => polyLift43_42 b
  | ⟨43,_⟩ => polyLift43_43 b
  | ⟨44,_⟩ => polyLift43_44 b
  | ⟨45,_⟩ => polyLift43_45 b
  | ⟨46,_⟩ => polyLift43_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree43 (j : Fin 47) (b : Fin 3) : (polyLiftRow43 j b).freeBlock=basisInt (homKind 43 j) b := by
  fin_cases j
  · exact polyLiftFree43_0 b
  · exact polyLiftFree43_1 b
  · exact polyLiftFree43_2 b
  · exact polyLiftFree43_3 b
  · exact polyLiftFree43_4 b
  · exact polyLiftFree43_5 b
  · exact polyLiftFree43_6 b
  · exact polyLiftFree43_7 b
  · exact polyLiftFree43_8 b
  · exact polyLiftFree43_9 b
  · exact polyLiftFree43_10 b
  · exact polyLiftFree43_11 b
  · exact polyLiftFree43_12 b
  · exact polyLiftFree43_13 b
  · exact polyLiftFree43_14 b
  · exact polyLiftFree43_15 b
  · exact polyLiftFree43_16 b
  · exact polyLiftFree43_17 b
  · exact polyLiftFree43_18 b
  · exact polyLiftFree43_19 b
  · exact polyLiftFree43_20 b
  · exact polyLiftFree43_21 b
  · exact polyLiftFree43_22 b
  · exact polyLiftFree43_23 b
  · exact polyLiftFree43_24 b
  · exact polyLiftFree43_25 b
  · exact polyLiftFree43_26 b
  · exact polyLiftFree43_27 b
  · exact polyLiftFree43_28 b
  · exact polyLiftFree43_29 b
  · exact polyLiftFree43_30 b
  · exact polyLiftFree43_31 b
  · exact polyLiftFree43_32 b
  · exact polyLiftFree43_33 b
  · exact polyLiftFree43_34 b
  · exact polyLiftFree43_35 b
  · exact polyLiftFree43_36 b
  · exact polyLiftFree43_37 b
  · exact polyLiftFree43_38 b
  · exact polyLiftFree43_39 b
  · exact polyLiftFree43_40 b
  · exact polyLiftFree43_41 b
  · exact polyLiftFree43_42 b
  · exact polyLiftFree43_43 b
  · exact polyLiftFree43_44 b
  · exact polyLiftFree43_45 b
  · exact polyLiftFree43_46 b
end UniserialComputations.N6
