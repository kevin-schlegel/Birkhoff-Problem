import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift32_0 (b : Fin 3) : PolyHom 32 0 :=
  ![PolyHom.zero 32 0,PolyHom.zero 32 0,PolyHom.zero 32 0] b
theorem polyLiftFree32_0 : ∀ b : Fin 3, (polyLift32_0 b).freeBlock=basisInt (homKind 32 0) b := by decide
def polyLift32_1 (b : Fin 3) : PolyHom 32 1 :=
  ![PolyHom.zero 32 1,PolyHom.zero 32 1,PolyHom.zero 32 1] b
theorem polyLiftFree32_1 : ∀ b : Fin 3, (polyLift32_1 b).freeBlock=basisInt (homKind 32 1) b := by decide
def polyLift32_2 (b : Fin 3) : PolyHom 32 2 :=
  ![PolyHom.zero 32 2,PolyHom.zero 32 2,PolyHom.zero 32 2] b
theorem polyLiftFree32_2 : ∀ b : Fin 3, (polyLift32_2 b).freeBlock=basisInt (homKind 32 2) b := by decide
def polyRep32_3_0 : PolyHom 32 3 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (-1) 1),0,0,0;(mono6 (1) 0),0,0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_3 (b : Fin 3) : PolyHom 32 3 :=
  ![polyRep32_3_0,PolyHom.zero 32 3,PolyHom.zero 32 3] b
theorem polyLiftFree32_3 : ∀ b : Fin 3, (polyLift32_3 b).freeBlock=basisInt (homKind 32 3) b := by decide
def polyRep32_4_0 : PolyHom 32 4 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_4 (b : Fin 3) : PolyHom 32 4 :=
  ![polyRep32_4_0,PolyHom.zero 32 4,PolyHom.zero 32 4] b
theorem polyLiftFree32_4 : ∀ b : Fin 3, (polyLift32_4 b).freeBlock=basisInt (homKind 32 4) b := by decide
def polyLift32_5 (b : Fin 3) : PolyHom 32 5 :=
  ![PolyHom.zero 32 5,PolyHom.zero 32 5,PolyHom.zero 32 5] b
theorem polyLiftFree32_5 : ∀ b : Fin 3, (polyLift32_5 b).freeBlock=basisInt (homKind 32 5) b := by decide
def polyRep32_6_0 : PolyHom 32 6 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_6 (b : Fin 3) : PolyHom 32 6 :=
  ![polyRep32_6_0,PolyHom.zero 32 6,PolyHom.zero 32 6] b
theorem polyLiftFree32_6 : ∀ b : Fin 3, (polyLift32_6 b).freeBlock=basisInt (homKind 32 6) b := by decide
def polyRep32_7_0 : PolyHom 32 7 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_7 (b : Fin 3) : PolyHom 32 7 :=
  ![polyRep32_7_0,PolyHom.zero 32 7,PolyHom.zero 32 7] b
theorem polyLiftFree32_7 : ∀ b : Fin 3, (polyLift32_7 b).freeBlock=basisInt (homKind 32 7) b := by decide
def polyRep32_8_0 : PolyHom 32 8 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_8 (b : Fin 3) : PolyHom 32 8 :=
  ![polyRep32_8_0,PolyHom.zero 32 8,PolyHom.zero 32 8] b
theorem polyLiftFree32_8 : ∀ b : Fin 3, (polyLift32_8 b).freeBlock=basisInt (homKind 32 8) b := by decide
def polyRep32_9_0 : PolyHom 32 9 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_9 (b : Fin 3) : PolyHom 32 9 :=
  ![polyRep32_9_0,PolyHom.zero 32 9,PolyHom.zero 32 9] b
theorem polyLiftFree32_9 : ∀ b : Fin 3, (polyLift32_9 b).freeBlock=basisInt (homKind 32 9) b := by decide
def polyRep32_10_0 : PolyHom 32 10 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep32_10_1 : PolyHom 32 10 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0]
  U := !![0,0;(mono6 (1) 4),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_10 (b : Fin 3) : PolyHom 32 10 :=
  ![polyRep32_10_0,polyRep32_10_1,PolyHom.zero 32 10] b
theorem polyLiftFree32_10 : ∀ b : Fin 3, (polyLift32_10 b).freeBlock=basisInt (homKind 32 10) b := by decide
def polyRep32_11_0 : PolyHom 32 11 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep32_11_1 : PolyHom 32 11 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_11 (b : Fin 3) : PolyHom 32 11 :=
  ![polyRep32_11_0,polyRep32_11_1,PolyHom.zero 32 11] b
theorem polyLiftFree32_11 : ∀ b : Fin 3, (polyLift32_11 b).freeBlock=basisInt (homKind 32 11) b := by decide
def polyRep32_12_0 : PolyHom 32 12 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep32_12_1 : PolyHom 32 12 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_12 (b : Fin 3) : PolyHom 32 12 :=
  ![polyRep32_12_0,polyRep32_12_1,PolyHom.zero 32 12] b
theorem polyLiftFree32_12 : ∀ b : Fin 3, (polyLift32_12 b).freeBlock=basisInt (homKind 32 12) b := by decide
def polyRep32_13_0 : PolyHom 32 13 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_13 (b : Fin 3) : PolyHom 32 13 :=
  ![polyRep32_13_0,PolyHom.zero 32 13,PolyHom.zero 32 13] b
theorem polyLiftFree32_13 : ∀ b : Fin 3, (polyLift32_13 b).freeBlock=basisInt (homKind 32 13) b := by decide
def polyRep32_14_0 : PolyHom 32 14 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_14 (b : Fin 3) : PolyHom 32 14 :=
  ![polyRep32_14_0,PolyHom.zero 32 14,PolyHom.zero 32 14] b
theorem polyLiftFree32_14 : ∀ b : Fin 3, (polyLift32_14 b).freeBlock=basisInt (homKind 32 14) b := by decide
def polyLift32_15 (b : Fin 3) : PolyHom 32 15 :=
  ![PolyHom.zero 32 15,PolyHom.zero 32 15,PolyHom.zero 32 15] b
theorem polyLiftFree32_15 : ∀ b : Fin 3, (polyLift32_15 b).freeBlock=basisInt (homKind 32 15) b := by decide
def polyRep32_16_0 : PolyHom 32 16 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_16 (b : Fin 3) : PolyHom 32 16 :=
  ![polyRep32_16_0,PolyHom.zero 32 16,PolyHom.zero 32 16] b
theorem polyLiftFree32_16 : ∀ b : Fin 3, (polyLift32_16 b).freeBlock=basisInt (homKind 32 16) b := by decide
def polyRep32_17_0 : PolyHom 32 17 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_17 (b : Fin 3) : PolyHom 32 17 :=
  ![polyRep32_17_0,PolyHom.zero 32 17,PolyHom.zero 32 17] b
theorem polyLiftFree32_17 : ∀ b : Fin 3, (polyLift32_17 b).freeBlock=basisInt (homKind 32 17) b := by decide
def polyRep32_18_0 : PolyHom 32 18 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_18 (b : Fin 3) : PolyHom 32 18 :=
  ![polyRep32_18_0,PolyHom.zero 32 18,PolyHom.zero 32 18] b
theorem polyLiftFree32_18 : ∀ b : Fin 3, (polyLift32_18 b).freeBlock=basisInt (homKind 32 18) b := by decide
def polyRep32_19_0 : PolyHom 32 19 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_19 (b : Fin 3) : PolyHom 32 19 :=
  ![polyRep32_19_0,PolyHom.zero 32 19,PolyHom.zero 32 19] b
theorem polyLiftFree32_19 : ∀ b : Fin 3, (polyLift32_19 b).freeBlock=basisInt (homKind 32 19) b := by decide
def polyRep32_20_0 : PolyHom 32 20 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_20 (b : Fin 3) : PolyHom 32 20 :=
  ![polyRep32_20_0,PolyHom.zero 32 20,PolyHom.zero 32 20] b
theorem polyLiftFree32_20 : ∀ b : Fin 3, (polyLift32_20 b).freeBlock=basisInt (homKind 32 20) b := by decide
def polyRep32_21_0 : PolyHom 32 21 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep32_21_1 : PolyHom 32 21 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_21 (b : Fin 3) : PolyHom 32 21 :=
  ![polyRep32_21_0,polyRep32_21_1,PolyHom.zero 32 21] b
theorem polyLiftFree32_21 : ∀ b : Fin 3, (polyLift32_21 b).freeBlock=basisInt (homKind 32 21) b := by decide
def polyRep32_22_0 : PolyHom 32 22 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_22 (b : Fin 3) : PolyHom 32 22 :=
  ![polyRep32_22_0,PolyHom.zero 32 22,PolyHom.zero 32 22] b
theorem polyLiftFree32_22 : ∀ b : Fin 3, (polyLift32_22 b).freeBlock=basisInt (homKind 32 22) b := by decide
def polyRep32_23_0 : PolyHom 32 23 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_23 (b : Fin 3) : PolyHom 32 23 :=
  ![polyRep32_23_0,PolyHom.zero 32 23,PolyHom.zero 32 23] b
theorem polyLiftFree32_23 : ∀ b : Fin 3, (polyLift32_23 b).freeBlock=basisInt (homKind 32 23) b := by decide
def polyRep32_24_0 : PolyHom 32 24 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 1),0]
  U := !![(mono6 (1) 1),0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep32_24_1 : PolyHom 32 24 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_24 (b : Fin 3) : PolyHom 32 24 :=
  ![polyRep32_24_0,polyRep32_24_1,PolyHom.zero 32 24] b
theorem polyLiftFree32_24 : ∀ b : Fin 3, (polyLift32_24 b).freeBlock=basisInt (homKind 32 24) b := by decide
def polyRep32_25_0 : PolyHom 32 25 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep32_25_1 : PolyHom 32 25 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_25 (b : Fin 3) : PolyHom 32 25 :=
  ![polyRep32_25_0,polyRep32_25_1,PolyHom.zero 32 25] b
theorem polyLiftFree32_25 : ∀ b : Fin 3, (polyLift32_25 b).freeBlock=basisInt (homKind 32 25) b := by decide
def polyRep32_26_0 : PolyHom 32 26 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_26 (b : Fin 3) : PolyHom 32 26 :=
  ![polyRep32_26_0,PolyHom.zero 32 26,PolyHom.zero 32 26] b
theorem polyLiftFree32_26 : ∀ b : Fin 3, (polyLift32_26 b).freeBlock=basisInt (homKind 32 26) b := by decide
def polyRep32_27_0 : PolyHom 32 27 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep32_27_1 : PolyHom 32 27 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_27 (b : Fin 3) : PolyHom 32 27 :=
  ![polyRep32_27_0,polyRep32_27_1,PolyHom.zero 32 27] b
theorem polyLiftFree32_27 : ∀ b : Fin 3, (polyLift32_27 b).freeBlock=basisInt (homKind 32 27) b := by decide
def polyRep32_28_0 : PolyHom 32 28 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_28 (b : Fin 3) : PolyHom 32 28 :=
  ![polyRep32_28_0,PolyHom.zero 32 28,PolyHom.zero 32 28] b
theorem polyLiftFree32_28 : ∀ b : Fin 3, (polyLift32_28 b).freeBlock=basisInt (homKind 32 28) b := by decide
def polyRep32_29_0 : PolyHom 32 29 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_29 (b : Fin 3) : PolyHom 32 29 :=
  ![polyRep32_29_0,PolyHom.zero 32 29,PolyHom.zero 32 29] b
theorem polyLiftFree32_29 : ∀ b : Fin 3, (polyLift32_29 b).freeBlock=basisInt (homKind 32 29) b := by decide
def polyRep32_30_0 : PolyHom 32 30 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep32_30_1 : PolyHom 32 30 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep32_30_2 : PolyHom 32 30 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![0,(mono6 (-1) 0);0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_30 (b : Fin 3) : PolyHom 32 30 :=
  ![polyRep32_30_0,polyRep32_30_1,polyRep32_30_2] b
theorem polyLiftFree32_30 : ∀ b : Fin 3, (polyLift32_30 b).freeBlock=basisInt (homKind 32 30) b := by decide
def polyRep32_31_0 : PolyHom 32 31 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (1) 1),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep32_31_1 : PolyHom 32 31 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_31 (b : Fin 3) : PolyHom 32 31 :=
  ![polyRep32_31_0,polyRep32_31_1,PolyHom.zero 32 31] b
theorem polyLiftFree32_31 : ∀ b : Fin 3, (polyLift32_31 b).freeBlock=basisInt (homKind 32 31) b := by decide
def polyRep32_32_0 : PolyHom 32 32 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,(mono6 (1) 0)]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep32_32_1 : PolyHom 32 32 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_32 (b : Fin 3) : PolyHom 32 32 :=
  ![polyRep32_32_0,polyRep32_32_1,PolyHom.zero 32 32] b
theorem polyLiftFree32_32 : ∀ b : Fin 3, (polyLift32_32 b).freeBlock=basisInt (homKind 32 32) b := by decide
def polyRep32_33_0 : PolyHom 32 33 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_33 (b : Fin 3) : PolyHom 32 33 :=
  ![polyRep32_33_0,PolyHom.zero 32 33,PolyHom.zero 32 33] b
theorem polyLiftFree32_33 : ∀ b : Fin 3, (polyLift32_33 b).freeBlock=basisInt (homKind 32 33) b := by decide
def polyRep32_34_0 : PolyHom 32 34 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_34 (b : Fin 3) : PolyHom 32 34 :=
  ![polyRep32_34_0,PolyHom.zero 32 34,PolyHom.zero 32 34] b
theorem polyLiftFree32_34 : ∀ b : Fin 3, (polyLift32_34 b).freeBlock=basisInt (homKind 32 34) b := by decide
def polyRep32_35_0 : PolyHom 32 35 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_35 (b : Fin 3) : PolyHom 32 35 :=
  ![polyRep32_35_0,PolyHom.zero 32 35,PolyHom.zero 32 35] b
theorem polyLiftFree32_35 : ∀ b : Fin 3, (polyLift32_35 b).freeBlock=basisInt (homKind 32 35) b := by decide
def polyRep32_36_0 : PolyHom 32 36 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_36 (b : Fin 3) : PolyHom 32 36 :=
  ![polyRep32_36_0,PolyHom.zero 32 36,PolyHom.zero 32 36] b
theorem polyLiftFree32_36 : ∀ b : Fin 3, (polyLift32_36 b).freeBlock=basisInt (homKind 32 36) b := by decide
def polyRep32_37_0 : PolyHom 32 37 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (1) 1),0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep32_37_1 : PolyHom 32 37 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_37 (b : Fin 3) : PolyHom 32 37 :=
  ![polyRep32_37_0,polyRep32_37_1,PolyHom.zero 32 37] b
theorem polyLiftFree32_37 : ∀ b : Fin 3, (polyLift32_37 b).freeBlock=basisInt (homKind 32 37) b := by decide
def polyRep32_38_0 : PolyHom 32 38 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,(mono6 (1) 0)]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep32_38_1 : PolyHom 32 38 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_38 (b : Fin 3) : PolyHom 32 38 :=
  ![polyRep32_38_0,polyRep32_38_1,PolyHom.zero 32 38] b
theorem polyLiftFree32_38 : ∀ b : Fin 3, (polyLift32_38 b).freeBlock=basisInt (homKind 32 38) b := by decide
def polyRep32_39_0 : PolyHom 32 39 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_39 (b : Fin 3) : PolyHom 32 39 :=
  ![polyRep32_39_0,PolyHom.zero 32 39,PolyHom.zero 32 39] b
theorem polyLiftFree32_39 : ∀ b : Fin 3, (polyLift32_39 b).freeBlock=basisInt (homKind 32 39) b := by decide
def polyRep32_40_0 : PolyHom 32 40 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep32_40_1 : PolyHom 32 40 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep32_40_2 : PolyHom 32 40 where
  M := !![0,0,0,0;0,(mono6 (-1) 0),0,0;0,0,0,(mono6 (-1) 1);0,0,0,(mono6 (1) 0)]
  U := !![0,(mono6 (-1) 0);0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_40 (b : Fin 3) : PolyHom 32 40 :=
  ![polyRep32_40_0,polyRep32_40_1,polyRep32_40_2] b
theorem polyLiftFree32_40 : ∀ b : Fin 3, (polyLift32_40 b).freeBlock=basisInt (homKind 32 40) b := by decide
def polyRep32_41_0 : PolyHom 32 41 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_41 (b : Fin 3) : PolyHom 32 41 :=
  ![polyRep32_41_0,PolyHom.zero 32 41,PolyHom.zero 32 41] b
theorem polyLiftFree32_41 : ∀ b : Fin 3, (polyLift32_41 b).freeBlock=basisInt (homKind 32 41) b := by decide
def polyRep32_42_0 : PolyHom 32 42 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep32_42_1 : PolyHom 32 42 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep32_42_2 : PolyHom 32 42 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,(mono6 (1) 0)]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_42 (b : Fin 3) : PolyHom 32 42 :=
  ![polyRep32_42_0,polyRep32_42_1,polyRep32_42_2] b
theorem polyLiftFree32_42 : ∀ b : Fin 3, (polyLift32_42 b).freeBlock=basisInt (homKind 32 42) b := by decide
def polyRep32_43_0 : PolyHom 32 43 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep32_43_1 : PolyHom 32 43 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 1),0;0,0,0,(mono6 (1) 0)]
  U := !![(mono6 (1) 1),0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_43 (b : Fin 3) : PolyHom 32 43 :=
  ![polyRep32_43_0,polyRep32_43_1,PolyHom.zero 32 43] b
theorem polyLiftFree32_43 : ∀ b : Fin 3, (polyLift32_43 b).freeBlock=basisInt (homKind 32 43) b := by decide
def polyRep32_44_0 : PolyHom 32 44 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep32_44_1 : PolyHom 32 44 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep32_44_2 : PolyHom 32 44 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,(mono6 (1) 0)]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_44 (b : Fin 3) : PolyHom 32 44 :=
  ![polyRep32_44_0,polyRep32_44_1,polyRep32_44_2] b
theorem polyLiftFree32_44 : ∀ b : Fin 3, (polyLift32_44 b).freeBlock=basisInt (homKind 32 44) b := by decide
def polyRep32_45_0 : PolyHom 32 45 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep32_45_1 : PolyHom 32 45 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift32_45 (b : Fin 3) : PolyHom 32 45 :=
  ![polyRep32_45_0,polyRep32_45_1,PolyHom.zero 32 45] b
theorem polyLiftFree32_45 : ∀ b : Fin 3, (polyLift32_45 b).freeBlock=basisInt (homKind 32 45) b := by decide
def polyLift32_46 (b : Fin 3) : PolyHom 32 46 :=
  ![PolyHom.zero 32 46,PolyHom.zero 32 46,PolyHom.zero 32 46] b
theorem polyLiftFree32_46 : ∀ b : Fin 3, (polyLift32_46 b).freeBlock=basisInt (homKind 32 46) b := by decide
def polyLiftRow32 (j : Fin 47) (b : Fin 3) : PolyHom 32 j :=
  match j with
  | ⟨0,_⟩ => polyLift32_0 b
  | ⟨1,_⟩ => polyLift32_1 b
  | ⟨2,_⟩ => polyLift32_2 b
  | ⟨3,_⟩ => polyLift32_3 b
  | ⟨4,_⟩ => polyLift32_4 b
  | ⟨5,_⟩ => polyLift32_5 b
  | ⟨6,_⟩ => polyLift32_6 b
  | ⟨7,_⟩ => polyLift32_7 b
  | ⟨8,_⟩ => polyLift32_8 b
  | ⟨9,_⟩ => polyLift32_9 b
  | ⟨10,_⟩ => polyLift32_10 b
  | ⟨11,_⟩ => polyLift32_11 b
  | ⟨12,_⟩ => polyLift32_12 b
  | ⟨13,_⟩ => polyLift32_13 b
  | ⟨14,_⟩ => polyLift32_14 b
  | ⟨15,_⟩ => polyLift32_15 b
  | ⟨16,_⟩ => polyLift32_16 b
  | ⟨17,_⟩ => polyLift32_17 b
  | ⟨18,_⟩ => polyLift32_18 b
  | ⟨19,_⟩ => polyLift32_19 b
  | ⟨20,_⟩ => polyLift32_20 b
  | ⟨21,_⟩ => polyLift32_21 b
  | ⟨22,_⟩ => polyLift32_22 b
  | ⟨23,_⟩ => polyLift32_23 b
  | ⟨24,_⟩ => polyLift32_24 b
  | ⟨25,_⟩ => polyLift32_25 b
  | ⟨26,_⟩ => polyLift32_26 b
  | ⟨27,_⟩ => polyLift32_27 b
  | ⟨28,_⟩ => polyLift32_28 b
  | ⟨29,_⟩ => polyLift32_29 b
  | ⟨30,_⟩ => polyLift32_30 b
  | ⟨31,_⟩ => polyLift32_31 b
  | ⟨32,_⟩ => polyLift32_32 b
  | ⟨33,_⟩ => polyLift32_33 b
  | ⟨34,_⟩ => polyLift32_34 b
  | ⟨35,_⟩ => polyLift32_35 b
  | ⟨36,_⟩ => polyLift32_36 b
  | ⟨37,_⟩ => polyLift32_37 b
  | ⟨38,_⟩ => polyLift32_38 b
  | ⟨39,_⟩ => polyLift32_39 b
  | ⟨40,_⟩ => polyLift32_40 b
  | ⟨41,_⟩ => polyLift32_41 b
  | ⟨42,_⟩ => polyLift32_42 b
  | ⟨43,_⟩ => polyLift32_43 b
  | ⟨44,_⟩ => polyLift32_44 b
  | ⟨45,_⟩ => polyLift32_45 b
  | ⟨46,_⟩ => polyLift32_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree32 (j : Fin 47) (b : Fin 3) : (polyLiftRow32 j b).freeBlock=basisInt (homKind 32 j) b := by
  fin_cases j
  · exact polyLiftFree32_0 b
  · exact polyLiftFree32_1 b
  · exact polyLiftFree32_2 b
  · exact polyLiftFree32_3 b
  · exact polyLiftFree32_4 b
  · exact polyLiftFree32_5 b
  · exact polyLiftFree32_6 b
  · exact polyLiftFree32_7 b
  · exact polyLiftFree32_8 b
  · exact polyLiftFree32_9 b
  · exact polyLiftFree32_10 b
  · exact polyLiftFree32_11 b
  · exact polyLiftFree32_12 b
  · exact polyLiftFree32_13 b
  · exact polyLiftFree32_14 b
  · exact polyLiftFree32_15 b
  · exact polyLiftFree32_16 b
  · exact polyLiftFree32_17 b
  · exact polyLiftFree32_18 b
  · exact polyLiftFree32_19 b
  · exact polyLiftFree32_20 b
  · exact polyLiftFree32_21 b
  · exact polyLiftFree32_22 b
  · exact polyLiftFree32_23 b
  · exact polyLiftFree32_24 b
  · exact polyLiftFree32_25 b
  · exact polyLiftFree32_26 b
  · exact polyLiftFree32_27 b
  · exact polyLiftFree32_28 b
  · exact polyLiftFree32_29 b
  · exact polyLiftFree32_30 b
  · exact polyLiftFree32_31 b
  · exact polyLiftFree32_32 b
  · exact polyLiftFree32_33 b
  · exact polyLiftFree32_34 b
  · exact polyLiftFree32_35 b
  · exact polyLiftFree32_36 b
  · exact polyLiftFree32_37 b
  · exact polyLiftFree32_38 b
  · exact polyLiftFree32_39 b
  · exact polyLiftFree32_40 b
  · exact polyLiftFree32_41 b
  · exact polyLiftFree32_42 b
  · exact polyLiftFree32_43 b
  · exact polyLiftFree32_44 b
  · exact polyLiftFree32_45 b
  · exact polyLiftFree32_46 b
end UniserialComputations.N6
