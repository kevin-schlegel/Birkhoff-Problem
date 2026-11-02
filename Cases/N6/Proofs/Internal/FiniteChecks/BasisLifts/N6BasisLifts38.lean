import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift38_0 (b : Fin 3) : PolyHom 38 0 :=
  ![PolyHom.zero 38 0,PolyHom.zero 38 0,PolyHom.zero 38 0] b
theorem polyLiftFree38_0 : ∀ b : Fin 3, (polyLift38_0 b).freeBlock=basisInt (homKind 38 0) b := by decide
def polyLift38_1 (b : Fin 3) : PolyHom 38 1 :=
  ![PolyHom.zero 38 1,PolyHom.zero 38 1,PolyHom.zero 38 1] b
theorem polyLiftFree38_1 : ∀ b : Fin 3, (polyLift38_1 b).freeBlock=basisInt (homKind 38 1) b := by decide
def polyLift38_2 (b : Fin 3) : PolyHom 38 2 :=
  ![PolyHom.zero 38 2,PolyHom.zero 38 2,PolyHom.zero 38 2] b
theorem polyLiftFree38_2 : ∀ b : Fin 3, (polyLift38_2 b).freeBlock=basisInt (homKind 38 2) b := by decide
def polyRep38_3_0 : PolyHom 38 3 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (-1) 1),0,0,0;(mono6 (1) 0),0,0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_3 (b : Fin 3) : PolyHom 38 3 :=
  ![polyRep38_3_0,PolyHom.zero 38 3,PolyHom.zero 38 3] b
theorem polyLiftFree38_3 : ∀ b : Fin 3, (polyLift38_3 b).freeBlock=basisInt (homKind 38 3) b := by decide
def polyRep38_4_0 : PolyHom 38 4 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 0),0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_4 (b : Fin 3) : PolyHom 38 4 :=
  ![polyRep38_4_0,PolyHom.zero 38 4,PolyHom.zero 38 4] b
theorem polyLiftFree38_4 : ∀ b : Fin 3, (polyLift38_4 b).freeBlock=basisInt (homKind 38 4) b := by decide
def polyLift38_5 (b : Fin 3) : PolyHom 38 5 :=
  ![PolyHom.zero 38 5,PolyHom.zero 38 5,PolyHom.zero 38 5] b
theorem polyLiftFree38_5 : ∀ b : Fin 3, (polyLift38_5 b).freeBlock=basisInt (homKind 38 5) b := by decide
def polyRep38_6_0 : PolyHom 38 6 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_6 (b : Fin 3) : PolyHom 38 6 :=
  ![polyRep38_6_0,PolyHom.zero 38 6,PolyHom.zero 38 6] b
theorem polyLiftFree38_6 : ∀ b : Fin 3, (polyLift38_6 b).freeBlock=basisInt (homKind 38 6) b := by decide
def polyRep38_7_0 : PolyHom 38 7 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_7 (b : Fin 3) : PolyHom 38 7 :=
  ![polyRep38_7_0,PolyHom.zero 38 7,PolyHom.zero 38 7] b
theorem polyLiftFree38_7 : ∀ b : Fin 3, (polyLift38_7 b).freeBlock=basisInt (homKind 38 7) b := by decide
def polyRep38_8_0 : PolyHom 38 8 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_8 (b : Fin 3) : PolyHom 38 8 :=
  ![polyRep38_8_0,PolyHom.zero 38 8,PolyHom.zero 38 8] b
theorem polyLiftFree38_8 : ∀ b : Fin 3, (polyLift38_8 b).freeBlock=basisInt (homKind 38 8) b := by decide
def polyLift38_9 (b : Fin 3) : PolyHom 38 9 :=
  ![PolyHom.zero 38 9,PolyHom.zero 38 9,PolyHom.zero 38 9] b
theorem polyLiftFree38_9 : ∀ b : Fin 3, (polyLift38_9 b).freeBlock=basisInt (homKind 38 9) b := by decide
def polyRep38_10_0 : PolyHom 38 10 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep38_10_1 : PolyHom 38 10 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_10 (b : Fin 3) : PolyHom 38 10 :=
  ![polyRep38_10_0,polyRep38_10_1,PolyHom.zero 38 10] b
theorem polyLiftFree38_10 : ∀ b : Fin 3, (polyLift38_10 b).freeBlock=basisInt (homKind 38 10) b := by decide
def polyRep38_11_0 : PolyHom 38 11 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep38_11_1 : PolyHom 38 11 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_11 (b : Fin 3) : PolyHom 38 11 :=
  ![polyRep38_11_0,polyRep38_11_1,PolyHom.zero 38 11] b
theorem polyLiftFree38_11 : ∀ b : Fin 3, (polyLift38_11 b).freeBlock=basisInt (homKind 38 11) b := by decide
def polyRep38_12_0 : PolyHom 38 12 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep38_12_1 : PolyHom 38 12 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_12 (b : Fin 3) : PolyHom 38 12 :=
  ![polyRep38_12_0,polyRep38_12_1,PolyHom.zero 38 12] b
theorem polyLiftFree38_12 : ∀ b : Fin 3, (polyLift38_12 b).freeBlock=basisInt (homKind 38 12) b := by decide
def polyRep38_13_0 : PolyHom 38 13 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_13 (b : Fin 3) : PolyHom 38 13 :=
  ![polyRep38_13_0,PolyHom.zero 38 13,PolyHom.zero 38 13] b
theorem polyLiftFree38_13 : ∀ b : Fin 3, (polyLift38_13 b).freeBlock=basisInt (homKind 38 13) b := by decide
def polyLift38_14 (b : Fin 3) : PolyHom 38 14 :=
  ![PolyHom.zero 38 14,PolyHom.zero 38 14,PolyHom.zero 38 14] b
theorem polyLiftFree38_14 : ∀ b : Fin 3, (polyLift38_14 b).freeBlock=basisInt (homKind 38 14) b := by decide
def polyLift38_15 (b : Fin 3) : PolyHom 38 15 :=
  ![PolyHom.zero 38 15,PolyHom.zero 38 15,PolyHom.zero 38 15] b
theorem polyLiftFree38_15 : ∀ b : Fin 3, (polyLift38_15 b).freeBlock=basisInt (homKind 38 15) b := by decide
def polyRep38_16_0 : PolyHom 38 16 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_16 (b : Fin 3) : PolyHom 38 16 :=
  ![polyRep38_16_0,PolyHom.zero 38 16,PolyHom.zero 38 16] b
theorem polyLiftFree38_16 : ∀ b : Fin 3, (polyLift38_16 b).freeBlock=basisInt (homKind 38 16) b := by decide
def polyRep38_17_0 : PolyHom 38 17 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_17 (b : Fin 3) : PolyHom 38 17 :=
  ![polyRep38_17_0,PolyHom.zero 38 17,PolyHom.zero 38 17] b
theorem polyLiftFree38_17 : ∀ b : Fin 3, (polyLift38_17 b).freeBlock=basisInt (homKind 38 17) b := by decide
def polyRep38_18_0 : PolyHom 38 18 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_18 (b : Fin 3) : PolyHom 38 18 :=
  ![polyRep38_18_0,PolyHom.zero 38 18,PolyHom.zero 38 18] b
theorem polyLiftFree38_18 : ∀ b : Fin 3, (polyLift38_18 b).freeBlock=basisInt (homKind 38 18) b := by decide
def polyRep38_19_0 : PolyHom 38 19 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_19 (b : Fin 3) : PolyHom 38 19 :=
  ![polyRep38_19_0,PolyHom.zero 38 19,PolyHom.zero 38 19] b
theorem polyLiftFree38_19 : ∀ b : Fin 3, (polyLift38_19 b).freeBlock=basisInt (homKind 38 19) b := by decide
def polyRep38_20_0 : PolyHom 38 20 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_20 (b : Fin 3) : PolyHom 38 20 :=
  ![polyRep38_20_0,PolyHom.zero 38 20,PolyHom.zero 38 20] b
theorem polyLiftFree38_20 : ∀ b : Fin 3, (polyLift38_20 b).freeBlock=basisInt (homKind 38 20) b := by decide
def polyRep38_21_0 : PolyHom 38 21 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep38_21_1 : PolyHom 38 21 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_21 (b : Fin 3) : PolyHom 38 21 :=
  ![polyRep38_21_0,polyRep38_21_1,PolyHom.zero 38 21] b
theorem polyLiftFree38_21 : ∀ b : Fin 3, (polyLift38_21 b).freeBlock=basisInt (homKind 38 21) b := by decide
def polyRep38_22_0 : PolyHom 38 22 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_22 (b : Fin 3) : PolyHom 38 22 :=
  ![polyRep38_22_0,PolyHom.zero 38 22,PolyHom.zero 38 22] b
theorem polyLiftFree38_22 : ∀ b : Fin 3, (polyLift38_22 b).freeBlock=basisInt (homKind 38 22) b := by decide
def polyRep38_23_0 : PolyHom 38 23 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_23 (b : Fin 3) : PolyHom 38 23 :=
  ![polyRep38_23_0,PolyHom.zero 38 23,PolyHom.zero 38 23] b
theorem polyLiftFree38_23 : ∀ b : Fin 3, (polyLift38_23 b).freeBlock=basisInt (homKind 38 23) b := by decide
def polyRep38_24_0 : PolyHom 38 24 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep38_24_1 : PolyHom 38 24 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_24 (b : Fin 3) : PolyHom 38 24 :=
  ![polyRep38_24_0,polyRep38_24_1,PolyHom.zero 38 24] b
theorem polyLiftFree38_24 : ∀ b : Fin 3, (polyLift38_24 b).freeBlock=basisInt (homKind 38 24) b := by decide
def polyRep38_25_0 : PolyHom 38 25 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep38_25_1 : PolyHom 38 25 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_25 (b : Fin 3) : PolyHom 38 25 :=
  ![polyRep38_25_0,polyRep38_25_1,PolyHom.zero 38 25] b
theorem polyLiftFree38_25 : ∀ b : Fin 3, (polyLift38_25 b).freeBlock=basisInt (homKind 38 25) b := by decide
def polyRep38_26_0 : PolyHom 38 26 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_26 (b : Fin 3) : PolyHom 38 26 :=
  ![polyRep38_26_0,PolyHom.zero 38 26,PolyHom.zero 38 26] b
theorem polyLiftFree38_26 : ∀ b : Fin 3, (polyLift38_26 b).freeBlock=basisInt (homKind 38 26) b := by decide
def polyRep38_27_0 : PolyHom 38 27 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep38_27_1 : PolyHom 38 27 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_27 (b : Fin 3) : PolyHom 38 27 :=
  ![polyRep38_27_0,polyRep38_27_1,PolyHom.zero 38 27] b
theorem polyLiftFree38_27 : ∀ b : Fin 3, (polyLift38_27 b).freeBlock=basisInt (homKind 38 27) b := by decide
def polyRep38_28_0 : PolyHom 38 28 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_28 (b : Fin 3) : PolyHom 38 28 :=
  ![polyRep38_28_0,PolyHom.zero 38 28,PolyHom.zero 38 28] b
theorem polyLiftFree38_28 : ∀ b : Fin 3, (polyLift38_28 b).freeBlock=basisInt (homKind 38 28) b := by decide
def polyRep38_29_0 : PolyHom 38 29 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_29 (b : Fin 3) : PolyHom 38 29 :=
  ![polyRep38_29_0,PolyHom.zero 38 29,PolyHom.zero 38 29] b
theorem polyLiftFree38_29 : ∀ b : Fin 3, (polyLift38_29 b).freeBlock=basisInt (homKind 38 29) b := by decide
def polyRep38_30_0 : PolyHom 38 30 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep38_30_1 : PolyHom 38 30 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep38_30_2 : PolyHom 38 30 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![0,(mono6 (-1) 0);0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_30 (b : Fin 3) : PolyHom 38 30 :=
  ![polyRep38_30_0,polyRep38_30_1,polyRep38_30_2] b
theorem polyLiftFree38_30 : ∀ b : Fin 3, (polyLift38_30 b).freeBlock=basisInt (homKind 38 30) b := by decide
def polyRep38_31_0 : PolyHom 38 31 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_31 (b : Fin 3) : PolyHom 38 31 :=
  ![polyRep38_31_0,PolyHom.zero 38 31,PolyHom.zero 38 31] b
theorem polyLiftFree38_31 : ∀ b : Fin 3, (polyLift38_31 b).freeBlock=basisInt (homKind 38 31) b := by decide
def polyRep38_32_0 : PolyHom 38 32 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_32 (b : Fin 3) : PolyHom 38 32 :=
  ![polyRep38_32_0,PolyHom.zero 38 32,PolyHom.zero 38 32] b
theorem polyLiftFree38_32 : ∀ b : Fin 3, (polyLift38_32 b).freeBlock=basisInt (homKind 38 32) b := by decide
def polyRep38_33_0 : PolyHom 38 33 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_33 (b : Fin 3) : PolyHom 38 33 :=
  ![polyRep38_33_0,PolyHom.zero 38 33,PolyHom.zero 38 33] b
theorem polyLiftFree38_33 : ∀ b : Fin 3, (polyLift38_33 b).freeBlock=basisInt (homKind 38 33) b := by decide
def polyRep38_34_0 : PolyHom 38 34 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_34 (b : Fin 3) : PolyHom 38 34 :=
  ![polyRep38_34_0,PolyHom.zero 38 34,PolyHom.zero 38 34] b
theorem polyLiftFree38_34 : ∀ b : Fin 3, (polyLift38_34 b).freeBlock=basisInt (homKind 38 34) b := by decide
def polyRep38_35_0 : PolyHom 38 35 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_35 (b : Fin 3) : PolyHom 38 35 :=
  ![polyRep38_35_0,PolyHom.zero 38 35,PolyHom.zero 38 35] b
theorem polyLiftFree38_35 : ∀ b : Fin 3, (polyLift38_35 b).freeBlock=basisInt (homKind 38 35) b := by decide
def polyRep38_36_0 : PolyHom 38 36 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_36 (b : Fin 3) : PolyHom 38 36 :=
  ![polyRep38_36_0,PolyHom.zero 38 36,PolyHom.zero 38 36] b
theorem polyLiftFree38_36 : ∀ b : Fin 3, (polyLift38_36 b).freeBlock=basisInt (homKind 38 36) b := by decide
def polyRep38_37_0 : PolyHom 38 37 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (1) 1),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep38_37_1 : PolyHom 38 37 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_37 (b : Fin 3) : PolyHom 38 37 :=
  ![polyRep38_37_0,polyRep38_37_1,PolyHom.zero 38 37] b
theorem polyLiftFree38_37 : ∀ b : Fin 3, (polyLift38_37 b).freeBlock=basisInt (homKind 38 37) b := by decide
def polyRep38_38_0 : PolyHom 38 38 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,(mono6 (1) 0)]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep38_38_1 : PolyHom 38 38 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_38 (b : Fin 3) : PolyHom 38 38 :=
  ![polyRep38_38_0,polyRep38_38_1,PolyHom.zero 38 38] b
theorem polyLiftFree38_38 : ∀ b : Fin 3, (polyLift38_38 b).freeBlock=basisInt (homKind 38 38) b := by decide
def polyRep38_39_0 : PolyHom 38 39 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_39 (b : Fin 3) : PolyHom 38 39 :=
  ![polyRep38_39_0,PolyHom.zero 38 39,PolyHom.zero 38 39] b
theorem polyLiftFree38_39 : ∀ b : Fin 3, (polyLift38_39 b).freeBlock=basisInt (homKind 38 39) b := by decide
def polyRep38_40_0 : PolyHom 38 40 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep38_40_1 : PolyHom 38 40 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep38_40_2 : PolyHom 38 40 where
  M := !![0,0,0,0;0,(mono6 (-1) 0),0,0;0,0,0,(mono6 (-1) 1);0,0,0,(mono6 (1) 0)]
  U := !![0,(mono6 (-1) 0);0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_40 (b : Fin 3) : PolyHom 38 40 :=
  ![polyRep38_40_0,polyRep38_40_1,polyRep38_40_2] b
theorem polyLiftFree38_40 : ∀ b : Fin 3, (polyLift38_40 b).freeBlock=basisInt (homKind 38 40) b := by decide
def polyRep38_41_0 : PolyHom 38 41 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_41 (b : Fin 3) : PolyHom 38 41 :=
  ![polyRep38_41_0,PolyHom.zero 38 41,PolyHom.zero 38 41] b
theorem polyLiftFree38_41 : ∀ b : Fin 3, (polyLift38_41 b).freeBlock=basisInt (homKind 38 41) b := by decide
def polyRep38_42_0 : PolyHom 38 42 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep38_42_1 : PolyHom 38 42 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep38_42_2 : PolyHom 38 42 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,(mono6 (1) 0)]
  U := !![0,0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_42 (b : Fin 3) : PolyHom 38 42 :=
  ![polyRep38_42_0,polyRep38_42_1,polyRep38_42_2] b
theorem polyLiftFree38_42 : ∀ b : Fin 3, (polyLift38_42 b).freeBlock=basisInt (homKind 38 42) b := by decide
def polyRep38_43_0 : PolyHom 38 43 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep38_43_1 : PolyHom 38 43 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 1),0;0,0,0,(mono6 (1) 0)]
  U := !![(mono6 (1) 1),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_43 (b : Fin 3) : PolyHom 38 43 :=
  ![polyRep38_43_0,polyRep38_43_1,PolyHom.zero 38 43] b
theorem polyLiftFree38_43 : ∀ b : Fin 3, (polyLift38_43 b).freeBlock=basisInt (homKind 38 43) b := by decide
def polyRep38_44_0 : PolyHom 38 44 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep38_44_1 : PolyHom 38 44 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep38_44_2 : PolyHom 38 44 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,(mono6 (1) 0)]
  U := !![0,0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_44 (b : Fin 3) : PolyHom 38 44 :=
  ![polyRep38_44_0,polyRep38_44_1,polyRep38_44_2] b
theorem polyLiftFree38_44 : ∀ b : Fin 3, (polyLift38_44 b).freeBlock=basisInt (homKind 38 44) b := by decide
def polyRep38_45_0 : PolyHom 38 45 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep38_45_1 : PolyHom 38 45 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift38_45 (b : Fin 3) : PolyHom 38 45 :=
  ![polyRep38_45_0,polyRep38_45_1,PolyHom.zero 38 45] b
theorem polyLiftFree38_45 : ∀ b : Fin 3, (polyLift38_45 b).freeBlock=basisInt (homKind 38 45) b := by decide
def polyLift38_46 (b : Fin 3) : PolyHom 38 46 :=
  ![PolyHom.zero 38 46,PolyHom.zero 38 46,PolyHom.zero 38 46] b
theorem polyLiftFree38_46 : ∀ b : Fin 3, (polyLift38_46 b).freeBlock=basisInt (homKind 38 46) b := by decide
def polyLiftRow38 (j : Fin 47) (b : Fin 3) : PolyHom 38 j :=
  match j with
  | ⟨0,_⟩ => polyLift38_0 b
  | ⟨1,_⟩ => polyLift38_1 b
  | ⟨2,_⟩ => polyLift38_2 b
  | ⟨3,_⟩ => polyLift38_3 b
  | ⟨4,_⟩ => polyLift38_4 b
  | ⟨5,_⟩ => polyLift38_5 b
  | ⟨6,_⟩ => polyLift38_6 b
  | ⟨7,_⟩ => polyLift38_7 b
  | ⟨8,_⟩ => polyLift38_8 b
  | ⟨9,_⟩ => polyLift38_9 b
  | ⟨10,_⟩ => polyLift38_10 b
  | ⟨11,_⟩ => polyLift38_11 b
  | ⟨12,_⟩ => polyLift38_12 b
  | ⟨13,_⟩ => polyLift38_13 b
  | ⟨14,_⟩ => polyLift38_14 b
  | ⟨15,_⟩ => polyLift38_15 b
  | ⟨16,_⟩ => polyLift38_16 b
  | ⟨17,_⟩ => polyLift38_17 b
  | ⟨18,_⟩ => polyLift38_18 b
  | ⟨19,_⟩ => polyLift38_19 b
  | ⟨20,_⟩ => polyLift38_20 b
  | ⟨21,_⟩ => polyLift38_21 b
  | ⟨22,_⟩ => polyLift38_22 b
  | ⟨23,_⟩ => polyLift38_23 b
  | ⟨24,_⟩ => polyLift38_24 b
  | ⟨25,_⟩ => polyLift38_25 b
  | ⟨26,_⟩ => polyLift38_26 b
  | ⟨27,_⟩ => polyLift38_27 b
  | ⟨28,_⟩ => polyLift38_28 b
  | ⟨29,_⟩ => polyLift38_29 b
  | ⟨30,_⟩ => polyLift38_30 b
  | ⟨31,_⟩ => polyLift38_31 b
  | ⟨32,_⟩ => polyLift38_32 b
  | ⟨33,_⟩ => polyLift38_33 b
  | ⟨34,_⟩ => polyLift38_34 b
  | ⟨35,_⟩ => polyLift38_35 b
  | ⟨36,_⟩ => polyLift38_36 b
  | ⟨37,_⟩ => polyLift38_37 b
  | ⟨38,_⟩ => polyLift38_38 b
  | ⟨39,_⟩ => polyLift38_39 b
  | ⟨40,_⟩ => polyLift38_40 b
  | ⟨41,_⟩ => polyLift38_41 b
  | ⟨42,_⟩ => polyLift38_42 b
  | ⟨43,_⟩ => polyLift38_43 b
  | ⟨44,_⟩ => polyLift38_44 b
  | ⟨45,_⟩ => polyLift38_45 b
  | ⟨46,_⟩ => polyLift38_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree38 (j : Fin 47) (b : Fin 3) : (polyLiftRow38 j b).freeBlock=basisInt (homKind 38 j) b := by
  fin_cases j
  · exact polyLiftFree38_0 b
  · exact polyLiftFree38_1 b
  · exact polyLiftFree38_2 b
  · exact polyLiftFree38_3 b
  · exact polyLiftFree38_4 b
  · exact polyLiftFree38_5 b
  · exact polyLiftFree38_6 b
  · exact polyLiftFree38_7 b
  · exact polyLiftFree38_8 b
  · exact polyLiftFree38_9 b
  · exact polyLiftFree38_10 b
  · exact polyLiftFree38_11 b
  · exact polyLiftFree38_12 b
  · exact polyLiftFree38_13 b
  · exact polyLiftFree38_14 b
  · exact polyLiftFree38_15 b
  · exact polyLiftFree38_16 b
  · exact polyLiftFree38_17 b
  · exact polyLiftFree38_18 b
  · exact polyLiftFree38_19 b
  · exact polyLiftFree38_20 b
  · exact polyLiftFree38_21 b
  · exact polyLiftFree38_22 b
  · exact polyLiftFree38_23 b
  · exact polyLiftFree38_24 b
  · exact polyLiftFree38_25 b
  · exact polyLiftFree38_26 b
  · exact polyLiftFree38_27 b
  · exact polyLiftFree38_28 b
  · exact polyLiftFree38_29 b
  · exact polyLiftFree38_30 b
  · exact polyLiftFree38_31 b
  · exact polyLiftFree38_32 b
  · exact polyLiftFree38_33 b
  · exact polyLiftFree38_34 b
  · exact polyLiftFree38_35 b
  · exact polyLiftFree38_36 b
  · exact polyLiftFree38_37 b
  · exact polyLiftFree38_38 b
  · exact polyLiftFree38_39 b
  · exact polyLiftFree38_40 b
  · exact polyLiftFree38_41 b
  · exact polyLiftFree38_42 b
  · exact polyLiftFree38_43 b
  · exact polyLiftFree38_44 b
  · exact polyLiftFree38_45 b
  · exact polyLiftFree38_46 b
end UniserialComputations.N6
