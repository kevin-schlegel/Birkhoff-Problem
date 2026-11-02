import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift39_0 (b : Fin 3) : PolyHom 39 0 :=
  ![PolyHom.zero 39 0,PolyHom.zero 39 0,PolyHom.zero 39 0] b
theorem polyLiftFree39_0 : ∀ b : Fin 3, (polyLift39_0 b).freeBlock=basisInt (homKind 39 0) b := by decide
def polyLift39_1 (b : Fin 3) : PolyHom 39 1 :=
  ![PolyHom.zero 39 1,PolyHom.zero 39 1,PolyHom.zero 39 1] b
theorem polyLiftFree39_1 : ∀ b : Fin 3, (polyLift39_1 b).freeBlock=basisInt (homKind 39 1) b := by decide
def polyLift39_2 (b : Fin 3) : PolyHom 39 2 :=
  ![PolyHom.zero 39 2,PolyHom.zero 39 2,PolyHom.zero 39 2] b
theorem polyLiftFree39_2 : ∀ b : Fin 3, (polyLift39_2 b).freeBlock=basisInt (homKind 39 2) b := by decide
def polyRep39_3_0 : PolyHom 39 3 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (-1) 1),0,0,0;(mono6 (1) 0),0,0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_3 (b : Fin 3) : PolyHom 39 3 :=
  ![polyRep39_3_0,PolyHom.zero 39 3,PolyHom.zero 39 3] b
theorem polyLiftFree39_3 : ∀ b : Fin 3, (polyLift39_3 b).freeBlock=basisInt (homKind 39 3) b := by decide
def polyRep39_4_0 : PolyHom 39 4 where
  M := !![0,0,0,0;(mono6 (1) 1),0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_4 (b : Fin 3) : PolyHom 39 4 :=
  ![polyRep39_4_0,PolyHom.zero 39 4,PolyHom.zero 39 4] b
theorem polyLiftFree39_4 : ∀ b : Fin 3, (polyLift39_4 b).freeBlock=basisInt (homKind 39 4) b := by decide
def polyLift39_5 (b : Fin 3) : PolyHom 39 5 :=
  ![PolyHom.zero 39 5,PolyHom.zero 39 5,PolyHom.zero 39 5] b
theorem polyLiftFree39_5 : ∀ b : Fin 3, (polyLift39_5 b).freeBlock=basisInt (homKind 39 5) b := by decide
def polyRep39_6_0 : PolyHom 39 6 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_6 (b : Fin 3) : PolyHom 39 6 :=
  ![polyRep39_6_0,PolyHom.zero 39 6,PolyHom.zero 39 6] b
theorem polyLiftFree39_6 : ∀ b : Fin 3, (polyLift39_6 b).freeBlock=basisInt (homKind 39 6) b := by decide
def polyRep39_7_0 : PolyHom 39 7 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_7 (b : Fin 3) : PolyHom 39 7 :=
  ![polyRep39_7_0,PolyHom.zero 39 7,PolyHom.zero 39 7] b
theorem polyLiftFree39_7 : ∀ b : Fin 3, (polyLift39_7 b).freeBlock=basisInt (homKind 39 7) b := by decide
def polyRep39_8_0 : PolyHom 39 8 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_8 (b : Fin 3) : PolyHom 39 8 :=
  ![polyRep39_8_0,PolyHom.zero 39 8,PolyHom.zero 39 8] b
theorem polyLiftFree39_8 : ∀ b : Fin 3, (polyLift39_8 b).freeBlock=basisInt (homKind 39 8) b := by decide
def polyRep39_9_0 : PolyHom 39 9 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_9 (b : Fin 3) : PolyHom 39 9 :=
  ![polyRep39_9_0,PolyHom.zero 39 9,PolyHom.zero 39 9] b
theorem polyLiftFree39_9 : ∀ b : Fin 3, (polyLift39_9 b).freeBlock=basisInt (homKind 39 9) b := by decide
def polyRep39_10_0 : PolyHom 39 10 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_10_1 : PolyHom 39 10 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0]
  U := !![0,0;(mono6 (1) 4),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_10 (b : Fin 3) : PolyHom 39 10 :=
  ![polyRep39_10_0,polyRep39_10_1,PolyHom.zero 39 10] b
theorem polyLiftFree39_10 : ∀ b : Fin 3, (polyLift39_10 b).freeBlock=basisInt (homKind 39 10) b := by decide
def polyRep39_11_0 : PolyHom 39 11 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_11_1 : PolyHom 39 11 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_11 (b : Fin 3) : PolyHom 39 11 :=
  ![polyRep39_11_0,polyRep39_11_1,PolyHom.zero 39 11] b
theorem polyLiftFree39_11 : ∀ b : Fin 3, (polyLift39_11 b).freeBlock=basisInt (homKind 39 11) b := by decide
def polyRep39_12_0 : PolyHom 39 12 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_12_1 : PolyHom 39 12 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_12 (b : Fin 3) : PolyHom 39 12 :=
  ![polyRep39_12_0,polyRep39_12_1,PolyHom.zero 39 12] b
theorem polyLiftFree39_12 : ∀ b : Fin 3, (polyLift39_12 b).freeBlock=basisInt (homKind 39 12) b := by decide
def polyRep39_13_0 : PolyHom 39 13 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_13 (b : Fin 3) : PolyHom 39 13 :=
  ![polyRep39_13_0,PolyHom.zero 39 13,PolyHom.zero 39 13] b
theorem polyLiftFree39_13 : ∀ b : Fin 3, (polyLift39_13 b).freeBlock=basisInt (homKind 39 13) b := by decide
def polyRep39_14_0 : PolyHom 39 14 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_14 (b : Fin 3) : PolyHom 39 14 :=
  ![polyRep39_14_0,PolyHom.zero 39 14,PolyHom.zero 39 14] b
theorem polyLiftFree39_14 : ∀ b : Fin 3, (polyLift39_14 b).freeBlock=basisInt (homKind 39 14) b := by decide
def polyRep39_15_0 : PolyHom 39 15 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_15 (b : Fin 3) : PolyHom 39 15 :=
  ![polyRep39_15_0,PolyHom.zero 39 15,PolyHom.zero 39 15] b
theorem polyLiftFree39_15 : ∀ b : Fin 3, (polyLift39_15 b).freeBlock=basisInt (homKind 39 15) b := by decide
def polyRep39_16_0 : PolyHom 39 16 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_16 (b : Fin 3) : PolyHom 39 16 :=
  ![polyRep39_16_0,PolyHom.zero 39 16,PolyHom.zero 39 16] b
theorem polyLiftFree39_16 : ∀ b : Fin 3, (polyLift39_16 b).freeBlock=basisInt (homKind 39 16) b := by decide
def polyRep39_17_0 : PolyHom 39 17 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_17 (b : Fin 3) : PolyHom 39 17 :=
  ![polyRep39_17_0,PolyHom.zero 39 17,PolyHom.zero 39 17] b
theorem polyLiftFree39_17 : ∀ b : Fin 3, (polyLift39_17 b).freeBlock=basisInt (homKind 39 17) b := by decide
def polyRep39_18_0 : PolyHom 39 18 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_18 (b : Fin 3) : PolyHom 39 18 :=
  ![polyRep39_18_0,PolyHom.zero 39 18,PolyHom.zero 39 18] b
theorem polyLiftFree39_18 : ∀ b : Fin 3, (polyLift39_18 b).freeBlock=basisInt (homKind 39 18) b := by decide
def polyRep39_19_0 : PolyHom 39 19 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_19 (b : Fin 3) : PolyHom 39 19 :=
  ![polyRep39_19_0,PolyHom.zero 39 19,PolyHom.zero 39 19] b
theorem polyLiftFree39_19 : ∀ b : Fin 3, (polyLift39_19 b).freeBlock=basisInt (homKind 39 19) b := by decide
def polyRep39_20_0 : PolyHom 39 20 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_20 (b : Fin 3) : PolyHom 39 20 :=
  ![polyRep39_20_0,PolyHom.zero 39 20,PolyHom.zero 39 20] b
theorem polyLiftFree39_20 : ∀ b : Fin 3, (polyLift39_20 b).freeBlock=basisInt (homKind 39 20) b := by decide
def polyRep39_21_0 : PolyHom 39 21 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_21_1 : PolyHom 39 21 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_21 (b : Fin 3) : PolyHom 39 21 :=
  ![polyRep39_21_0,polyRep39_21_1,PolyHom.zero 39 21] b
theorem polyLiftFree39_21 : ∀ b : Fin 3, (polyLift39_21 b).freeBlock=basisInt (homKind 39 21) b := by decide
def polyRep39_22_0 : PolyHom 39 22 where
  M := !![(mono6 (1) 0),0,0,0;(mono6 (-1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_22_1 : PolyHom 39 22 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_22 (b : Fin 3) : PolyHom 39 22 :=
  ![polyRep39_22_0,polyRep39_22_1,PolyHom.zero 39 22] b
theorem polyLiftFree39_22 : ∀ b : Fin 3, (polyLift39_22 b).freeBlock=basisInt (homKind 39 22) b := by decide
def polyRep39_23_0 : PolyHom 39 23 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_23 (b : Fin 3) : PolyHom 39 23 :=
  ![polyRep39_23_0,PolyHom.zero 39 23,PolyHom.zero 39 23] b
theorem polyLiftFree39_23 : ∀ b : Fin 3, (polyLift39_23 b).freeBlock=basisInt (homKind 39 23) b := by decide
def polyRep39_24_0 : PolyHom 39 24 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 1),0]
  U := !![(mono6 (1) 1),0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_24_1 : PolyHom 39 24 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_24 (b : Fin 3) : PolyHom 39 24 :=
  ![polyRep39_24_0,polyRep39_24_1,PolyHom.zero 39 24] b
theorem polyLiftFree39_24 : ∀ b : Fin 3, (polyLift39_24 b).freeBlock=basisInt (homKind 39 24) b := by decide
def polyRep39_25_0 : PolyHom 39 25 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_25_1 : PolyHom 39 25 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_25 (b : Fin 3) : PolyHom 39 25 :=
  ![polyRep39_25_0,polyRep39_25_1,PolyHom.zero 39 25] b
theorem polyLiftFree39_25 : ∀ b : Fin 3, (polyLift39_25 b).freeBlock=basisInt (homKind 39 25) b := by decide
def polyRep39_26_0 : PolyHom 39 26 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_26 (b : Fin 3) : PolyHom 39 26 :=
  ![polyRep39_26_0,PolyHom.zero 39 26,PolyHom.zero 39 26] b
theorem polyLiftFree39_26 : ∀ b : Fin 3, (polyLift39_26 b).freeBlock=basisInt (homKind 39 26) b := by decide
def polyRep39_27_0 : PolyHom 39 27 where
  M := !![(mono6 (1) 0),0,0,0;(mono6 (-1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_27_1 : PolyHom 39 27 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_27 (b : Fin 3) : PolyHom 39 27 :=
  ![polyRep39_27_0,polyRep39_27_1,PolyHom.zero 39 27] b
theorem polyLiftFree39_27 : ∀ b : Fin 3, (polyLift39_27 b).freeBlock=basisInt (homKind 39 27) b := by decide
def polyRep39_28_0 : PolyHom 39 28 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_28 (b : Fin 3) : PolyHom 39 28 :=
  ![polyRep39_28_0,PolyHom.zero 39 28,PolyHom.zero 39 28] b
theorem polyLiftFree39_28 : ∀ b : Fin 3, (polyLift39_28 b).freeBlock=basisInt (homKind 39 28) b := by decide
def polyRep39_29_0 : PolyHom 39 29 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_29 (b : Fin 3) : PolyHom 39 29 :=
  ![polyRep39_29_0,PolyHom.zero 39 29,PolyHom.zero 39 29] b
theorem polyLiftFree39_29 : ∀ b : Fin 3, (polyLift39_29 b).freeBlock=basisInt (homKind 39 29) b := by decide
def polyRep39_30_0 : PolyHom 39 30 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 1),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_30_1 : PolyHom 39 30 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_30_2 : PolyHom 39 30 where
  M := !![0,0,0,0;(mono6 (1) 1),0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![0,(mono6 (-1) 0);0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_30 (b : Fin 3) : PolyHom 39 30 :=
  ![polyRep39_30_0,polyRep39_30_1,polyRep39_30_2] b
theorem polyLiftFree39_30 : ∀ b : Fin 3, (polyLift39_30 b).freeBlock=basisInt (homKind 39 30) b := by decide
def polyRep39_31_0 : PolyHom 39 31 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (1) 1),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_31_1 : PolyHom 39 31 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_31 (b : Fin 3) : PolyHom 39 31 :=
  ![polyRep39_31_0,polyRep39_31_1,PolyHom.zero 39 31] b
theorem polyLiftFree39_31 : ∀ b : Fin 3, (polyLift39_31 b).freeBlock=basisInt (homKind 39 31) b := by decide
def polyRep39_32_0 : PolyHom 39 32 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,(mono6 (1) 0)]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_32_1 : PolyHom 39 32 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_32 (b : Fin 3) : PolyHom 39 32 :=
  ![polyRep39_32_0,polyRep39_32_1,PolyHom.zero 39 32] b
theorem polyLiftFree39_32 : ∀ b : Fin 3, (polyLift39_32 b).freeBlock=basisInt (homKind 39 32) b := by decide
def polyRep39_33_0 : PolyHom 39 33 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_33 (b : Fin 3) : PolyHom 39 33 :=
  ![polyRep39_33_0,PolyHom.zero 39 33,PolyHom.zero 39 33] b
theorem polyLiftFree39_33 : ∀ b : Fin 3, (polyLift39_33 b).freeBlock=basisInt (homKind 39 33) b := by decide
def polyRep39_34_0 : PolyHom 39 34 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_34 (b : Fin 3) : PolyHom 39 34 :=
  ![polyRep39_34_0,PolyHom.zero 39 34,PolyHom.zero 39 34] b
theorem polyLiftFree39_34 : ∀ b : Fin 3, (polyLift39_34 b).freeBlock=basisInt (homKind 39 34) b := by decide
def polyRep39_35_0 : PolyHom 39 35 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_35 (b : Fin 3) : PolyHom 39 35 :=
  ![polyRep39_35_0,PolyHom.zero 39 35,PolyHom.zero 39 35] b
theorem polyLiftFree39_35 : ∀ b : Fin 3, (polyLift39_35 b).freeBlock=basisInt (homKind 39 35) b := by decide
def polyRep39_36_0 : PolyHom 39 36 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_36 (b : Fin 3) : PolyHom 39 36 :=
  ![polyRep39_36_0,PolyHom.zero 39 36,PolyHom.zero 39 36] b
theorem polyLiftFree39_36 : ∀ b : Fin 3, (polyLift39_36 b).freeBlock=basisInt (homKind 39 36) b := by decide
def polyRep39_37_0 : PolyHom 39 37 where
  M := !![(mono6 (1) 0),0,0,0;(mono6 (-1) 0),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_37_1 : PolyHom 39 37 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_37_2 : PolyHom 39 37 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![0,(mono6 (-1) 0);0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_37 (b : Fin 3) : PolyHom 39 37 :=
  ![polyRep39_37_0,polyRep39_37_1,polyRep39_37_2] b
theorem polyLiftFree39_37 : ∀ b : Fin 3, (polyLift39_37 b).freeBlock=basisInt (homKind 39 37) b := by decide
def polyRep39_38_0 : PolyHom 39 38 where
  M := !![(mono6 (1) 0),0,0,0;(mono6 (-1) 0),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0]
  U := !![(mono6 (1) 0),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_38_1 : PolyHom 39 38 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_38_2 : PolyHom 39 38 where
  M := !![0,0,0,0;(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,0,(mono6 (-1) 1);0,0,0,(mono6 (1) 0)]
  U := !![0,(mono6 (-1) 0);0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_38 (b : Fin 3) : PolyHom 39 38 :=
  ![polyRep39_38_0,polyRep39_38_1,polyRep39_38_2] b
theorem polyLiftFree39_38 : ∀ b : Fin 3, (polyLift39_38 b).freeBlock=basisInt (homKind 39 38) b := by decide
def polyRep39_39_0 : PolyHom 39 39 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,(mono6 (1) 0)]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_39_1 : PolyHom 39 39 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_39 (b : Fin 3) : PolyHom 39 39 :=
  ![polyRep39_39_0,polyRep39_39_1,PolyHom.zero 39 39] b
theorem polyLiftFree39_39 : ∀ b : Fin 3, (polyLift39_39 b).freeBlock=basisInt (homKind 39 39) b := by decide
def polyRep39_40_0 : PolyHom 39 40 where
  M := !![(mono6 (1) 0),0,0,0;(mono6 (-1) 0),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_40_1 : PolyHom 39 40 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_40_2 : PolyHom 39 40 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,(mono6 (-1) 1);0,0,0,(mono6 (1) 0)]
  U := !![0,(mono6 (-1) 0);0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_40 (b : Fin 3) : PolyHom 39 40 :=
  ![polyRep39_40_0,polyRep39_40_1,polyRep39_40_2] b
theorem polyLiftFree39_40 : ∀ b : Fin 3, (polyLift39_40 b).freeBlock=basisInt (homKind 39 40) b := by decide
def polyRep39_41_0 : PolyHom 39 41 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_41 (b : Fin 3) : PolyHom 39 41 :=
  ![polyRep39_41_0,PolyHom.zero 39 41,PolyHom.zero 39 41] b
theorem polyLiftFree39_41 : ∀ b : Fin 3, (polyLift39_41 b).freeBlock=basisInt (homKind 39 41) b := by decide
def polyRep39_42_0 : PolyHom 39 42 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_42_1 : PolyHom 39 42 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_42_2 : PolyHom 39 42 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,(mono6 (1) 0)]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_42 (b : Fin 3) : PolyHom 39 42 :=
  ![polyRep39_42_0,polyRep39_42_1,polyRep39_42_2] b
theorem polyLiftFree39_42 : ∀ b : Fin 3, (polyLift39_42 b).freeBlock=basisInt (homKind 39 42) b := by decide
def polyRep39_43_0 : PolyHom 39 43 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_43_1 : PolyHom 39 43 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 1),0;0,0,0,(mono6 (1) 0)]
  U := !![(mono6 (1) 1),0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_43 (b : Fin 3) : PolyHom 39 43 :=
  ![polyRep39_43_0,polyRep39_43_1,PolyHom.zero 39 43] b
theorem polyLiftFree39_43 : ∀ b : Fin 3, (polyLift39_43 b).freeBlock=basisInt (homKind 39 43) b := by decide
def polyRep39_44_0 : PolyHom 39 44 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_44_1 : PolyHom 39 44 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_44_2 : PolyHom 39 44 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,(mono6 (1) 0)]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_44 (b : Fin 3) : PolyHom 39 44 :=
  ![polyRep39_44_0,polyRep39_44_1,polyRep39_44_2] b
theorem polyLiftFree39_44 : ∀ b : Fin 3, (polyLift39_44 b).freeBlock=basisInt (homKind 39 44) b := by decide
def polyRep39_45_0 : PolyHom 39 45 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep39_45_1 : PolyHom 39 45 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift39_45 (b : Fin 3) : PolyHom 39 45 :=
  ![polyRep39_45_0,polyRep39_45_1,PolyHom.zero 39 45] b
theorem polyLiftFree39_45 : ∀ b : Fin 3, (polyLift39_45 b).freeBlock=basisInt (homKind 39 45) b := by decide
def polyLift39_46 (b : Fin 3) : PolyHom 39 46 :=
  ![PolyHom.zero 39 46,PolyHom.zero 39 46,PolyHom.zero 39 46] b
theorem polyLiftFree39_46 : ∀ b : Fin 3, (polyLift39_46 b).freeBlock=basisInt (homKind 39 46) b := by decide
def polyLiftRow39 (j : Fin 47) (b : Fin 3) : PolyHom 39 j :=
  match j with
  | ⟨0,_⟩ => polyLift39_0 b
  | ⟨1,_⟩ => polyLift39_1 b
  | ⟨2,_⟩ => polyLift39_2 b
  | ⟨3,_⟩ => polyLift39_3 b
  | ⟨4,_⟩ => polyLift39_4 b
  | ⟨5,_⟩ => polyLift39_5 b
  | ⟨6,_⟩ => polyLift39_6 b
  | ⟨7,_⟩ => polyLift39_7 b
  | ⟨8,_⟩ => polyLift39_8 b
  | ⟨9,_⟩ => polyLift39_9 b
  | ⟨10,_⟩ => polyLift39_10 b
  | ⟨11,_⟩ => polyLift39_11 b
  | ⟨12,_⟩ => polyLift39_12 b
  | ⟨13,_⟩ => polyLift39_13 b
  | ⟨14,_⟩ => polyLift39_14 b
  | ⟨15,_⟩ => polyLift39_15 b
  | ⟨16,_⟩ => polyLift39_16 b
  | ⟨17,_⟩ => polyLift39_17 b
  | ⟨18,_⟩ => polyLift39_18 b
  | ⟨19,_⟩ => polyLift39_19 b
  | ⟨20,_⟩ => polyLift39_20 b
  | ⟨21,_⟩ => polyLift39_21 b
  | ⟨22,_⟩ => polyLift39_22 b
  | ⟨23,_⟩ => polyLift39_23 b
  | ⟨24,_⟩ => polyLift39_24 b
  | ⟨25,_⟩ => polyLift39_25 b
  | ⟨26,_⟩ => polyLift39_26 b
  | ⟨27,_⟩ => polyLift39_27 b
  | ⟨28,_⟩ => polyLift39_28 b
  | ⟨29,_⟩ => polyLift39_29 b
  | ⟨30,_⟩ => polyLift39_30 b
  | ⟨31,_⟩ => polyLift39_31 b
  | ⟨32,_⟩ => polyLift39_32 b
  | ⟨33,_⟩ => polyLift39_33 b
  | ⟨34,_⟩ => polyLift39_34 b
  | ⟨35,_⟩ => polyLift39_35 b
  | ⟨36,_⟩ => polyLift39_36 b
  | ⟨37,_⟩ => polyLift39_37 b
  | ⟨38,_⟩ => polyLift39_38 b
  | ⟨39,_⟩ => polyLift39_39 b
  | ⟨40,_⟩ => polyLift39_40 b
  | ⟨41,_⟩ => polyLift39_41 b
  | ⟨42,_⟩ => polyLift39_42 b
  | ⟨43,_⟩ => polyLift39_43 b
  | ⟨44,_⟩ => polyLift39_44 b
  | ⟨45,_⟩ => polyLift39_45 b
  | ⟨46,_⟩ => polyLift39_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree39 (j : Fin 47) (b : Fin 3) : (polyLiftRow39 j b).freeBlock=basisInt (homKind 39 j) b := by
  fin_cases j
  · exact polyLiftFree39_0 b
  · exact polyLiftFree39_1 b
  · exact polyLiftFree39_2 b
  · exact polyLiftFree39_3 b
  · exact polyLiftFree39_4 b
  · exact polyLiftFree39_5 b
  · exact polyLiftFree39_6 b
  · exact polyLiftFree39_7 b
  · exact polyLiftFree39_8 b
  · exact polyLiftFree39_9 b
  · exact polyLiftFree39_10 b
  · exact polyLiftFree39_11 b
  · exact polyLiftFree39_12 b
  · exact polyLiftFree39_13 b
  · exact polyLiftFree39_14 b
  · exact polyLiftFree39_15 b
  · exact polyLiftFree39_16 b
  · exact polyLiftFree39_17 b
  · exact polyLiftFree39_18 b
  · exact polyLiftFree39_19 b
  · exact polyLiftFree39_20 b
  · exact polyLiftFree39_21 b
  · exact polyLiftFree39_22 b
  · exact polyLiftFree39_23 b
  · exact polyLiftFree39_24 b
  · exact polyLiftFree39_25 b
  · exact polyLiftFree39_26 b
  · exact polyLiftFree39_27 b
  · exact polyLiftFree39_28 b
  · exact polyLiftFree39_29 b
  · exact polyLiftFree39_30 b
  · exact polyLiftFree39_31 b
  · exact polyLiftFree39_32 b
  · exact polyLiftFree39_33 b
  · exact polyLiftFree39_34 b
  · exact polyLiftFree39_35 b
  · exact polyLiftFree39_36 b
  · exact polyLiftFree39_37 b
  · exact polyLiftFree39_38 b
  · exact polyLiftFree39_39 b
  · exact polyLiftFree39_40 b
  · exact polyLiftFree39_41 b
  · exact polyLiftFree39_42 b
  · exact polyLiftFree39_43 b
  · exact polyLiftFree39_44 b
  · exact polyLiftFree39_45 b
  · exact polyLiftFree39_46 b
end UniserialComputations.N6
