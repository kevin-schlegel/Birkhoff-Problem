import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift41_0 (b : Fin 3) : PolyHom 41 0 :=
  ![PolyHom.zero 41 0,PolyHom.zero 41 0,PolyHom.zero 41 0] b
theorem polyLiftFree41_0 : ∀ b : Fin 3, (polyLift41_0 b).freeBlock=basisInt (homKind 41 0) b := by decide
def polyRep41_1_0 : PolyHom 41 1 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (-1) 1),0,0,0;(mono6 (1) 0),0,0,0]
  U := !![(mono6 (-1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_1 (b : Fin 3) : PolyHom 41 1 :=
  ![polyRep41_1_0,PolyHom.zero 41 1,PolyHom.zero 41 1] b
theorem polyLiftFree41_1 : ∀ b : Fin 3, (polyLift41_1 b).freeBlock=basisInt (homKind 41 1) b := by decide
def polyLift41_2 (b : Fin 3) : PolyHom 41 2 :=
  ![PolyHom.zero 41 2,PolyHom.zero 41 2,PolyHom.zero 41 2] b
theorem polyLiftFree41_2 : ∀ b : Fin 3, (polyLift41_2 b).freeBlock=basisInt (homKind 41 2) b := by decide
def polyRep41_3_0 : PolyHom 41 3 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (-1) 1),0,0,0;(mono6 (1) 0),0,0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_3 (b : Fin 3) : PolyHom 41 3 :=
  ![polyRep41_3_0,PolyHom.zero 41 3,PolyHom.zero 41 3] b
theorem polyLiftFree41_3 : ∀ b : Fin 3, (polyLift41_3 b).freeBlock=basisInt (homKind 41 3) b := by decide
def polyRep41_4_0 : PolyHom 41 4 where
  M := !![0,(mono6 (-1) 0),0,0;(mono6 (-1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_4 (b : Fin 3) : PolyHom 41 4 :=
  ![polyRep41_4_0,PolyHom.zero 41 4,PolyHom.zero 41 4] b
theorem polyLiftFree41_4 : ∀ b : Fin 3, (polyLift41_4 b).freeBlock=basisInt (homKind 41 4) b := by decide
def polyRep41_5_0 : PolyHom 41 5 where
  M := !![0,(mono6 (-1) 0),0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_5 (b : Fin 3) : PolyHom 41 5 :=
  ![polyRep41_5_0,PolyHom.zero 41 5,PolyHom.zero 41 5] b
theorem polyLiftFree41_5 : ∀ b : Fin 3, (polyLift41_5 b).freeBlock=basisInt (homKind 41 5) b := by decide
def polyRep41_6_0 : PolyHom 41 6 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_6 (b : Fin 3) : PolyHom 41 6 :=
  ![polyRep41_6_0,PolyHom.zero 41 6,PolyHom.zero 41 6] b
theorem polyLiftFree41_6 : ∀ b : Fin 3, (polyLift41_6 b).freeBlock=basisInt (homKind 41 6) b := by decide
def polyRep41_7_0 : PolyHom 41 7 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_7 (b : Fin 3) : PolyHom 41 7 :=
  ![polyRep41_7_0,PolyHom.zero 41 7,PolyHom.zero 41 7] b
theorem polyLiftFree41_7 : ∀ b : Fin 3, (polyLift41_7 b).freeBlock=basisInt (homKind 41 7) b := by decide
def polyRep41_8_0 : PolyHom 41 8 where
  M := !![(mono6 (1) 2),0,0,0;(mono6 (-1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_8 (b : Fin 3) : PolyHom 41 8 :=
  ![polyRep41_8_0,PolyHom.zero 41 8,PolyHom.zero 41 8] b
theorem polyLiftFree41_8 : ∀ b : Fin 3, (polyLift41_8 b).freeBlock=basisInt (homKind 41 8) b := by decide
def polyRep41_9_0 : PolyHom 41 9 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_9 (b : Fin 3) : PolyHom 41 9 :=
  ![polyRep41_9_0,PolyHom.zero 41 9,PolyHom.zero 41 9] b
theorem polyLiftFree41_9 : ∀ b : Fin 3, (polyLift41_9 b).freeBlock=basisInt (homKind 41 9) b := by decide
def polyRep41_10_0 : PolyHom 41 10 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_10_1 : PolyHom 41 10 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0]
  U := !![0,0;(mono6 (1) 4),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_10 (b : Fin 3) : PolyHom 41 10 :=
  ![polyRep41_10_0,polyRep41_10_1,PolyHom.zero 41 10] b
theorem polyLiftFree41_10 : ∀ b : Fin 3, (polyLift41_10 b).freeBlock=basisInt (homKind 41 10) b := by decide
def polyRep41_11_0 : PolyHom 41 11 where
  M := !![(mono6 (1) 3),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_11_1 : PolyHom 41 11 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_11 (b : Fin 3) : PolyHom 41 11 :=
  ![polyRep41_11_0,polyRep41_11_1,PolyHom.zero 41 11] b
theorem polyLiftFree41_11 : ∀ b : Fin 3, (polyLift41_11 b).freeBlock=basisInt (homKind 41 11) b := by decide
def polyRep41_12_0 : PolyHom 41 12 where
  M := !![(mono6 (1) 2),0,0,0;(mono6 (-1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_12_1 : PolyHom 41 12 where
  M := !![(mono6 (1) 3),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_12 (b : Fin 3) : PolyHom 41 12 :=
  ![polyRep41_12_0,polyRep41_12_1,PolyHom.zero 41 12] b
theorem polyLiftFree41_12 : ∀ b : Fin 3, (polyLift41_12 b).freeBlock=basisInt (homKind 41 12) b := by decide
def polyRep41_13_0 : PolyHom 41 13 where
  M := !![(mono6 (1) 2),0,0,0;(mono6 (-1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_13 (b : Fin 3) : PolyHom 41 13 :=
  ![polyRep41_13_0,PolyHom.zero 41 13,PolyHom.zero 41 13] b
theorem polyLiftFree41_13 : ∀ b : Fin 3, (polyLift41_13 b).freeBlock=basisInt (homKind 41 13) b := by decide
def polyRep41_14_0 : PolyHom 41 14 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_14 (b : Fin 3) : PolyHom 41 14 :=
  ![polyRep41_14_0,PolyHom.zero 41 14,PolyHom.zero 41 14] b
theorem polyLiftFree41_14 : ∀ b : Fin 3, (polyLift41_14 b).freeBlock=basisInt (homKind 41 14) b := by decide
def polyRep41_15_0 : PolyHom 41 15 where
  M := !![0,(mono6 (-1) 0),0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_15 (b : Fin 3) : PolyHom 41 15 :=
  ![polyRep41_15_0,PolyHom.zero 41 15,PolyHom.zero 41 15] b
theorem polyLiftFree41_15 : ∀ b : Fin 3, (polyLift41_15 b).freeBlock=basisInt (homKind 41 15) b := by decide
def polyRep41_16_0 : PolyHom 41 16 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_16 (b : Fin 3) : PolyHom 41 16 :=
  ![polyRep41_16_0,PolyHom.zero 41 16,PolyHom.zero 41 16] b
theorem polyLiftFree41_16 : ∀ b : Fin 3, (polyLift41_16 b).freeBlock=basisInt (homKind 41 16) b := by decide
def polyRep41_17_0 : PolyHom 41 17 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_17 (b : Fin 3) : PolyHom 41 17 :=
  ![polyRep41_17_0,PolyHom.zero 41 17,PolyHom.zero 41 17] b
theorem polyLiftFree41_17 : ∀ b : Fin 3, (polyLift41_17 b).freeBlock=basisInt (homKind 41 17) b := by decide
def polyRep41_18_0 : PolyHom 41 18 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_18 (b : Fin 3) : PolyHom 41 18 :=
  ![polyRep41_18_0,PolyHom.zero 41 18,PolyHom.zero 41 18] b
theorem polyLiftFree41_18 : ∀ b : Fin 3, (polyLift41_18 b).freeBlock=basisInt (homKind 41 18) b := by decide
def polyRep41_19_0 : PolyHom 41 19 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_19 (b : Fin 3) : PolyHom 41 19 :=
  ![polyRep41_19_0,PolyHom.zero 41 19,PolyHom.zero 41 19] b
theorem polyLiftFree41_19 : ∀ b : Fin 3, (polyLift41_19 b).freeBlock=basisInt (homKind 41 19) b := by decide
def polyRep41_20_0 : PolyHom 41 20 where
  M := !![0,0,(mono6 (-1) 0),0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_20 (b : Fin 3) : PolyHom 41 20 :=
  ![polyRep41_20_0,PolyHom.zero 41 20,PolyHom.zero 41 20] b
theorem polyLiftFree41_20 : ∀ b : Fin 3, (polyLift41_20 b).freeBlock=basisInt (homKind 41 20) b := by decide
def polyRep41_21_0 : PolyHom 41 21 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_21_1 : PolyHom 41 21 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_21 (b : Fin 3) : PolyHom 41 21 :=
  ![polyRep41_21_0,polyRep41_21_1,PolyHom.zero 41 21] b
theorem polyLiftFree41_21 : ∀ b : Fin 3, (polyLift41_21 b).freeBlock=basisInt (homKind 41 21) b := by decide
def polyRep41_22_0 : PolyHom 41 22 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_22_1 : PolyHom 41 22 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_22 (b : Fin 3) : PolyHom 41 22 :=
  ![polyRep41_22_0,polyRep41_22_1,PolyHom.zero 41 22] b
theorem polyLiftFree41_22 : ∀ b : Fin 3, (polyLift41_22 b).freeBlock=basisInt (homKind 41 22) b := by decide
def polyRep41_23_0 : PolyHom 41 23 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_23 (b : Fin 3) : PolyHom 41 23 :=
  ![polyRep41_23_0,PolyHom.zero 41 23,PolyHom.zero 41 23] b
theorem polyLiftFree41_23 : ∀ b : Fin 3, (polyLift41_23 b).freeBlock=basisInt (homKind 41 23) b := by decide
def polyRep41_24_0 : PolyHom 41 24 where
  M := !![(mono6 (1) 2),0,(mono6 (1) 1),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_24_1 : PolyHom 41 24 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_24 (b : Fin 3) : PolyHom 41 24 :=
  ![polyRep41_24_0,polyRep41_24_1,PolyHom.zero 41 24] b
theorem polyLiftFree41_24 : ∀ b : Fin 3, (polyLift41_24 b).freeBlock=basisInt (homKind 41 24) b := by decide
def polyRep41_25_0 : PolyHom 41 25 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_25_1 : PolyHom 41 25 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_25 (b : Fin 3) : PolyHom 41 25 :=
  ![polyRep41_25_0,polyRep41_25_1,PolyHom.zero 41 25] b
theorem polyLiftFree41_25 : ∀ b : Fin 3, (polyLift41_25 b).freeBlock=basisInt (homKind 41 25) b := by decide
def polyRep41_26_0 : PolyHom 41 26 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_26_1 : PolyHom 41 26 where
  M := !![(mono6 (1) 2),0,(mono6 (1) 1),0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_26 (b : Fin 3) : PolyHom 41 26 :=
  ![polyRep41_26_0,polyRep41_26_1,PolyHom.zero 41 26] b
theorem polyLiftFree41_26 : ∀ b : Fin 3, (polyLift41_26 b).freeBlock=basisInt (homKind 41 26) b := by decide
def polyRep41_27_0 : PolyHom 41 27 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_27_1 : PolyHom 41 27 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_27 (b : Fin 3) : PolyHom 41 27 :=
  ![polyRep41_27_0,polyRep41_27_1,PolyHom.zero 41 27] b
theorem polyLiftFree41_27 : ∀ b : Fin 3, (polyLift41_27 b).freeBlock=basisInt (homKind 41 27) b := by decide
def polyRep41_28_0 : PolyHom 41 28 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_28 (b : Fin 3) : PolyHom 41 28 :=
  ![polyRep41_28_0,PolyHom.zero 41 28,PolyHom.zero 41 28] b
theorem polyLiftFree41_28 : ∀ b : Fin 3, (polyLift41_28 b).freeBlock=basisInt (homKind 41 28) b := by decide
def polyRep41_29_0 : PolyHom 41 29 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_29 (b : Fin 3) : PolyHom 41 29 :=
  ![polyRep41_29_0,PolyHom.zero 41 29,PolyHom.zero 41 29] b
theorem polyLiftFree41_29 : ∀ b : Fin 3, (polyLift41_29 b).freeBlock=basisInt (homKind 41 29) b := by decide
def polyRep41_30_0 : PolyHom 41 30 where
  M := !![(mono6 (1) 2),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_30_1 : PolyHom 41 30 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_30_2 : PolyHom 41 30 where
  M := !![0,0,(mono6 (-1) 0),0;(mono6 (-1) 1),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_30 (b : Fin 3) : PolyHom 41 30 :=
  ![polyRep41_30_0,polyRep41_30_1,polyRep41_30_2] b
theorem polyLiftFree41_30 : ∀ b : Fin 3, (polyLift41_30 b).freeBlock=basisInt (homKind 41 30) b := by decide
def polyRep41_31_0 : PolyHom 41 31 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_31_1 : PolyHom 41 31 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_31_2 : PolyHom 41 31 where
  M := !![0,0,(mono6 (-1) 0),0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_31 (b : Fin 3) : PolyHom 41 31 :=
  ![polyRep41_31_0,polyRep41_31_1,polyRep41_31_2] b
theorem polyLiftFree41_31 : ∀ b : Fin 3, (polyLift41_31 b).freeBlock=basisInt (homKind 41 31) b := by decide
def polyRep41_32_0 : PolyHom 41 32 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_32_1 : PolyHom 41 32 where
  M := !![(mono6 (1) 2),0,0,(mono6 (1) 1);0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_32_2 : PolyHom 41 32 where
  M := !![0,0,0,(mono6 (-1) 0);(mono6 (-1) 0),(mono6 (-1) 1),0,0;0,0,0,0;0,0,0,(mono6 (1) 0)]
  U := !![0,0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_32 (b : Fin 3) : PolyHom 41 32 :=
  ![polyRep41_32_0,polyRep41_32_1,polyRep41_32_2] b
theorem polyLiftFree41_32 : ∀ b : Fin 3, (polyLift41_32 b).freeBlock=basisInt (homKind 41 32) b := by decide
def polyRep41_33_0 : PolyHom 41 33 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_33_1 : PolyHom 41 33 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_33 (b : Fin 3) : PolyHom 41 33 :=
  ![polyRep41_33_0,polyRep41_33_1,PolyHom.zero 41 33] b
theorem polyLiftFree41_33 : ∀ b : Fin 3, (polyLift41_33 b).freeBlock=basisInt (homKind 41 33) b := by decide
def polyRep41_34_0 : PolyHom 41 34 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_34_1 : PolyHom 41 34 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_34 (b : Fin 3) : PolyHom 41 34 :=
  ![polyRep41_34_0,polyRep41_34_1,PolyHom.zero 41 34] b
theorem polyLiftFree41_34 : ∀ b : Fin 3, (polyLift41_34 b).freeBlock=basisInt (homKind 41 34) b := by decide
def polyRep41_35_0 : PolyHom 41 35 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_35 (b : Fin 3) : PolyHom 41 35 :=
  ![polyRep41_35_0,PolyHom.zero 41 35,PolyHom.zero 41 35] b
theorem polyLiftFree41_35 : ∀ b : Fin 3, (polyLift41_35 b).freeBlock=basisInt (homKind 41 35) b := by decide
def polyRep41_36_0 : PolyHom 41 36 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_36_1 : PolyHom 41 36 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_36 (b : Fin 3) : PolyHom 41 36 :=
  ![polyRep41_36_0,polyRep41_36_1,PolyHom.zero 41 36] b
theorem polyLiftFree41_36 : ∀ b : Fin 3, (polyLift41_36 b).freeBlock=basisInt (homKind 41 36) b := by decide
def polyRep41_37_0 : PolyHom 41 37 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_37_1 : PolyHom 41 37 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_37_2 : PolyHom 41 37 where
  M := !![0,0,(mono6 (-1) 0),0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_37 (b : Fin 3) : PolyHom 41 37 :=
  ![polyRep41_37_0,polyRep41_37_1,polyRep41_37_2] b
theorem polyLiftFree41_37 : ∀ b : Fin 3, (polyLift41_37 b).freeBlock=basisInt (homKind 41 37) b := by decide
def polyRep41_38_0 : PolyHom 41 38 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_38_1 : PolyHom 41 38 where
  M := !![(mono6 (1) 2),0,0,(mono6 (1) 1);0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_38_2 : PolyHom 41 38 where
  M := !![0,0,0,(mono6 (-1) 0);(mono6 (-1) 0),(mono6 (-1) 1),0,0;0,0,0,0;0,0,0,(mono6 (1) 0)]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_38 (b : Fin 3) : PolyHom 41 38 :=
  ![polyRep41_38_0,polyRep41_38_1,polyRep41_38_2] b
theorem polyLiftFree41_38 : ∀ b : Fin 3, (polyLift41_38 b).freeBlock=basisInt (homKind 41 38) b := by decide
def polyRep41_39_0 : PolyHom 41 39 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_39_1 : PolyHom 41 39 where
  M := !![(mono6 (1) 2),0,0,(mono6 (1) 1);0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_39_2 : PolyHom 41 39 where
  M := !![0,0,0,(mono6 (-1) 0);(mono6 (-1) 0),(mono6 (-1) 0),0,0;0,0,0,0;0,0,0,(mono6 (1) 0)]
  U := !![0,0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_39 (b : Fin 3) : PolyHom 41 39 :=
  ![polyRep41_39_0,polyRep41_39_1,polyRep41_39_2] b
theorem polyLiftFree41_39 : ∀ b : Fin 3, (polyLift41_39 b).freeBlock=basisInt (homKind 41 39) b := by decide
def polyRep41_40_0 : PolyHom 41 40 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_40_1 : PolyHom 41 40 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_40_2 : PolyHom 41 40 where
  M := !![0,0,0,(mono6 (-1) 0);(mono6 (-1) 0),0,0,0;0,0,0,0;0,0,0,(mono6 (1) 0)]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_40 (b : Fin 3) : PolyHom 41 40 :=
  ![polyRep41_40_0,polyRep41_40_1,polyRep41_40_2] b
theorem polyLiftFree41_40 : ∀ b : Fin 3, (polyLift41_40 b).freeBlock=basisInt (homKind 41 40) b := by decide
def polyRep41_41_0 : PolyHom 41 41 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,(mono6 (1) 0)]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_41_1 : PolyHom 41 41 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 1);0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_41 (b : Fin 3) : PolyHom 41 41 :=
  ![polyRep41_41_0,polyRep41_41_1,PolyHom.zero 41 41] b
theorem polyLiftFree41_41 : ∀ b : Fin 3, (polyLift41_41 b).freeBlock=basisInt (homKind 41 41) b := by decide
def polyRep41_42_0 : PolyHom 41 42 where
  M := !![0,(mono6 (1) 2),0,(mono6 (-1) 0);0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_42_1 : PolyHom 41 42 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_42_2 : PolyHom 41 42 where
  M := !![0,0,0,(mono6 (-1) 0);0,(mono6 (1) 1),0,0;0,0,0,0;0,0,0,(mono6 (1) 0)]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_42 (b : Fin 3) : PolyHom 41 42 :=
  ![polyRep41_42_0,polyRep41_42_1,polyRep41_42_2] b
theorem polyLiftFree41_42 : ∀ b : Fin 3, (polyLift41_42 b).freeBlock=basisInt (homKind 41 42) b := by decide
def polyRep41_43_0 : PolyHom 41 43 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_43_1 : PolyHom 41 43 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 1),0,0;0,0,(mono6 (1) 1),0;0,0,0,(mono6 (1) 0)]
  U := !![(mono6 (1) 1),0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_43 (b : Fin 3) : PolyHom 41 43 :=
  ![polyRep41_43_0,polyRep41_43_1,PolyHom.zero 41 43] b
theorem polyLiftFree41_43 : ∀ b : Fin 3, (polyLift41_43 b).freeBlock=basisInt (homKind 41 43) b := by decide
def polyRep41_44_0 : PolyHom 41 44 where
  M := !![(mono6 (1) 1),(mono6 (1) 2),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_44_1 : PolyHom 41 44 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_44_2 : PolyHom 41 44 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 1),0,0;0,0,0,0;0,0,0,(mono6 (1) 0)]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_44 (b : Fin 3) : PolyHom 41 44 :=
  ![polyRep41_44_0,polyRep41_44_1,polyRep41_44_2] b
theorem polyLiftFree41_44 : ∀ b : Fin 3, (polyLift41_44 b).freeBlock=basisInt (homKind 41 44) b := by decide
def polyRep41_45_0 : PolyHom 41 45 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep41_45_1 : PolyHom 41 45 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift41_45 (b : Fin 3) : PolyHom 41 45 :=
  ![polyRep41_45_0,polyRep41_45_1,PolyHom.zero 41 45] b
theorem polyLiftFree41_45 : ∀ b : Fin 3, (polyLift41_45 b).freeBlock=basisInt (homKind 41 45) b := by decide
def polyLift41_46 (b : Fin 3) : PolyHom 41 46 :=
  ![PolyHom.zero 41 46,PolyHom.zero 41 46,PolyHom.zero 41 46] b
theorem polyLiftFree41_46 : ∀ b : Fin 3, (polyLift41_46 b).freeBlock=basisInt (homKind 41 46) b := by decide
def polyLiftRow41 (j : Fin 47) (b : Fin 3) : PolyHom 41 j :=
  match j with
  | ⟨0,_⟩ => polyLift41_0 b
  | ⟨1,_⟩ => polyLift41_1 b
  | ⟨2,_⟩ => polyLift41_2 b
  | ⟨3,_⟩ => polyLift41_3 b
  | ⟨4,_⟩ => polyLift41_4 b
  | ⟨5,_⟩ => polyLift41_5 b
  | ⟨6,_⟩ => polyLift41_6 b
  | ⟨7,_⟩ => polyLift41_7 b
  | ⟨8,_⟩ => polyLift41_8 b
  | ⟨9,_⟩ => polyLift41_9 b
  | ⟨10,_⟩ => polyLift41_10 b
  | ⟨11,_⟩ => polyLift41_11 b
  | ⟨12,_⟩ => polyLift41_12 b
  | ⟨13,_⟩ => polyLift41_13 b
  | ⟨14,_⟩ => polyLift41_14 b
  | ⟨15,_⟩ => polyLift41_15 b
  | ⟨16,_⟩ => polyLift41_16 b
  | ⟨17,_⟩ => polyLift41_17 b
  | ⟨18,_⟩ => polyLift41_18 b
  | ⟨19,_⟩ => polyLift41_19 b
  | ⟨20,_⟩ => polyLift41_20 b
  | ⟨21,_⟩ => polyLift41_21 b
  | ⟨22,_⟩ => polyLift41_22 b
  | ⟨23,_⟩ => polyLift41_23 b
  | ⟨24,_⟩ => polyLift41_24 b
  | ⟨25,_⟩ => polyLift41_25 b
  | ⟨26,_⟩ => polyLift41_26 b
  | ⟨27,_⟩ => polyLift41_27 b
  | ⟨28,_⟩ => polyLift41_28 b
  | ⟨29,_⟩ => polyLift41_29 b
  | ⟨30,_⟩ => polyLift41_30 b
  | ⟨31,_⟩ => polyLift41_31 b
  | ⟨32,_⟩ => polyLift41_32 b
  | ⟨33,_⟩ => polyLift41_33 b
  | ⟨34,_⟩ => polyLift41_34 b
  | ⟨35,_⟩ => polyLift41_35 b
  | ⟨36,_⟩ => polyLift41_36 b
  | ⟨37,_⟩ => polyLift41_37 b
  | ⟨38,_⟩ => polyLift41_38 b
  | ⟨39,_⟩ => polyLift41_39 b
  | ⟨40,_⟩ => polyLift41_40 b
  | ⟨41,_⟩ => polyLift41_41 b
  | ⟨42,_⟩ => polyLift41_42 b
  | ⟨43,_⟩ => polyLift41_43 b
  | ⟨44,_⟩ => polyLift41_44 b
  | ⟨45,_⟩ => polyLift41_45 b
  | ⟨46,_⟩ => polyLift41_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree41 (j : Fin 47) (b : Fin 3) : (polyLiftRow41 j b).freeBlock=basisInt (homKind 41 j) b := by
  fin_cases j
  · exact polyLiftFree41_0 b
  · exact polyLiftFree41_1 b
  · exact polyLiftFree41_2 b
  · exact polyLiftFree41_3 b
  · exact polyLiftFree41_4 b
  · exact polyLiftFree41_5 b
  · exact polyLiftFree41_6 b
  · exact polyLiftFree41_7 b
  · exact polyLiftFree41_8 b
  · exact polyLiftFree41_9 b
  · exact polyLiftFree41_10 b
  · exact polyLiftFree41_11 b
  · exact polyLiftFree41_12 b
  · exact polyLiftFree41_13 b
  · exact polyLiftFree41_14 b
  · exact polyLiftFree41_15 b
  · exact polyLiftFree41_16 b
  · exact polyLiftFree41_17 b
  · exact polyLiftFree41_18 b
  · exact polyLiftFree41_19 b
  · exact polyLiftFree41_20 b
  · exact polyLiftFree41_21 b
  · exact polyLiftFree41_22 b
  · exact polyLiftFree41_23 b
  · exact polyLiftFree41_24 b
  · exact polyLiftFree41_25 b
  · exact polyLiftFree41_26 b
  · exact polyLiftFree41_27 b
  · exact polyLiftFree41_28 b
  · exact polyLiftFree41_29 b
  · exact polyLiftFree41_30 b
  · exact polyLiftFree41_31 b
  · exact polyLiftFree41_32 b
  · exact polyLiftFree41_33 b
  · exact polyLiftFree41_34 b
  · exact polyLiftFree41_35 b
  · exact polyLiftFree41_36 b
  · exact polyLiftFree41_37 b
  · exact polyLiftFree41_38 b
  · exact polyLiftFree41_39 b
  · exact polyLiftFree41_40 b
  · exact polyLiftFree41_41 b
  · exact polyLiftFree41_42 b
  · exact polyLiftFree41_43 b
  · exact polyLiftFree41_44 b
  · exact polyLiftFree41_45 b
  · exact polyLiftFree41_46 b
end UniserialComputations.N6
