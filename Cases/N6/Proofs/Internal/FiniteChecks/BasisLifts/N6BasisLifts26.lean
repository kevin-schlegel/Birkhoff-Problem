import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift26_0 (b : Fin 3) : PolyHom 26 0 :=
  ![PolyHom.zero 26 0,PolyHom.zero 26 0,PolyHom.zero 26 0] b
theorem polyLiftFree26_0 : ∀ b : Fin 3, (polyLift26_0 b).freeBlock=basisInt (homKind 26 0) b := by decide
def polyRep26_1_0 : PolyHom 26 1 where
  M := !![0,0,0,0;(mono6 (-1) 1),0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![(mono6 (-1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_1 (b : Fin 3) : PolyHom 26 1 :=
  ![polyRep26_1_0,PolyHom.zero 26 1,PolyHom.zero 26 1] b
theorem polyLiftFree26_1 : ∀ b : Fin 3, (polyLift26_1 b).freeBlock=basisInt (homKind 26 1) b := by decide
def polyLift26_2 (b : Fin 3) : PolyHom 26 2 :=
  ![PolyHom.zero 26 2,PolyHom.zero 26 2,PolyHom.zero 26 2] b
theorem polyLiftFree26_2 : ∀ b : Fin 3, (polyLift26_2 b).freeBlock=basisInt (homKind 26 2) b := by decide
def polyRep26_3_0 : PolyHom 26 3 where
  M := !![0,0,0,0;(mono6 (-1) 1),0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_3 (b : Fin 3) : PolyHom 26 3 :=
  ![polyRep26_3_0,PolyHom.zero 26 3,PolyHom.zero 26 3] b
theorem polyLiftFree26_3 : ∀ b : Fin 3, (polyLift26_3 b).freeBlock=basisInt (homKind 26 3) b := by decide
def polyRep26_4_0 : PolyHom 26 4 where
  M := !![0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (-1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_4 (b : Fin 3) : PolyHom 26 4 :=
  ![polyRep26_4_0,PolyHom.zero 26 4,PolyHom.zero 26 4] b
theorem polyLiftFree26_4 : ∀ b : Fin 3, (polyLift26_4 b).freeBlock=basisInt (homKind 26 4) b := by decide
def polyLift26_5 (b : Fin 3) : PolyHom 26 5 :=
  ![PolyHom.zero 26 5,PolyHom.zero 26 5,PolyHom.zero 26 5] b
theorem polyLiftFree26_5 : ∀ b : Fin 3, (polyLift26_5 b).freeBlock=basisInt (homKind 26 5) b := by decide
def polyRep26_6_0 : PolyHom 26 6 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_6 (b : Fin 3) : PolyHom 26 6 :=
  ![polyRep26_6_0,PolyHom.zero 26 6,PolyHom.zero 26 6] b
theorem polyLiftFree26_6 : ∀ b : Fin 3, (polyLift26_6 b).freeBlock=basisInt (homKind 26 6) b := by decide
def polyRep26_7_0 : PolyHom 26 7 where
  M := !![0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_7 (b : Fin 3) : PolyHom 26 7 :=
  ![polyRep26_7_0,PolyHom.zero 26 7,PolyHom.zero 26 7] b
theorem polyLiftFree26_7 : ∀ b : Fin 3, (polyLift26_7 b).freeBlock=basisInt (homKind 26 7) b := by decide
def polyRep26_8_0 : PolyHom 26 8 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_8 (b : Fin 3) : PolyHom 26 8 :=
  ![polyRep26_8_0,PolyHom.zero 26 8,PolyHom.zero 26 8] b
theorem polyLiftFree26_8 : ∀ b : Fin 3, (polyLift26_8 b).freeBlock=basisInt (homKind 26 8) b := by decide
def polyRep26_9_0 : PolyHom 26 9 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_9 (b : Fin 3) : PolyHom 26 9 :=
  ![polyRep26_9_0,PolyHom.zero 26 9,PolyHom.zero 26 9] b
theorem polyLiftFree26_9 : ∀ b : Fin 3, (polyLift26_9 b).freeBlock=basisInt (homKind 26 9) b := by decide
def polyRep26_10_0 : PolyHom 26 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_10_1 : PolyHom 26 10 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 4),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_10 (b : Fin 3) : PolyHom 26 10 :=
  ![polyRep26_10_0,polyRep26_10_1,PolyHom.zero 26 10] b
theorem polyLiftFree26_10 : ∀ b : Fin 3, (polyLift26_10 b).freeBlock=basisInt (homKind 26 10) b := by decide
def polyRep26_11_0 : PolyHom 26 11 where
  M := !![(mono6 (1) 2),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_11_1 : PolyHom 26 11 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_11 (b : Fin 3) : PolyHom 26 11 :=
  ![polyRep26_11_0,polyRep26_11_1,PolyHom.zero 26 11] b
theorem polyLiftFree26_11 : ∀ b : Fin 3, (polyLift26_11 b).freeBlock=basisInt (homKind 26 11) b := by decide
def polyRep26_12_0 : PolyHom 26 12 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_12_1 : PolyHom 26 12 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_12 (b : Fin 3) : PolyHom 26 12 :=
  ![polyRep26_12_0,polyRep26_12_1,PolyHom.zero 26 12] b
theorem polyLiftFree26_12 : ∀ b : Fin 3, (polyLift26_12 b).freeBlock=basisInt (homKind 26 12) b := by decide
def polyRep26_13_0 : PolyHom 26 13 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_13 (b : Fin 3) : PolyHom 26 13 :=
  ![polyRep26_13_0,PolyHom.zero 26 13,PolyHom.zero 26 13] b
theorem polyLiftFree26_13 : ∀ b : Fin 3, (polyLift26_13 b).freeBlock=basisInt (homKind 26 13) b := by decide
def polyRep26_14_0 : PolyHom 26 14 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_14 (b : Fin 3) : PolyHom 26 14 :=
  ![polyRep26_14_0,PolyHom.zero 26 14,PolyHom.zero 26 14] b
theorem polyLiftFree26_14 : ∀ b : Fin 3, (polyLift26_14 b).freeBlock=basisInt (homKind 26 14) b := by decide
def polyRep26_15_0 : PolyHom 26 15 where
  M := !![0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (-1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_15 (b : Fin 3) : PolyHom 26 15 :=
  ![polyRep26_15_0,PolyHom.zero 26 15,PolyHom.zero 26 15] b
theorem polyLiftFree26_15 : ∀ b : Fin 3, (polyLift26_15 b).freeBlock=basisInt (homKind 26 15) b := by decide
def polyRep26_16_0 : PolyHom 26 16 where
  M := !![0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_16 (b : Fin 3) : PolyHom 26 16 :=
  ![polyRep26_16_0,PolyHom.zero 26 16,PolyHom.zero 26 16] b
theorem polyLiftFree26_16 : ∀ b : Fin 3, (polyLift26_16 b).freeBlock=basisInt (homKind 26 16) b := by decide
def polyRep26_17_0 : PolyHom 26 17 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_17 (b : Fin 3) : PolyHom 26 17 :=
  ![polyRep26_17_0,PolyHom.zero 26 17,PolyHom.zero 26 17] b
theorem polyLiftFree26_17 : ∀ b : Fin 3, (polyLift26_17 b).freeBlock=basisInt (homKind 26 17) b := by decide
def polyRep26_18_0 : PolyHom 26 18 where
  M := !![0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_18 (b : Fin 3) : PolyHom 26 18 :=
  ![polyRep26_18_0,PolyHom.zero 26 18,PolyHom.zero 26 18] b
theorem polyLiftFree26_18 : ∀ b : Fin 3, (polyLift26_18 b).freeBlock=basisInt (homKind 26 18) b := by decide
def polyRep26_19_0 : PolyHom 26 19 where
  M := !![0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_19 (b : Fin 3) : PolyHom 26 19 :=
  ![polyRep26_19_0,PolyHom.zero 26 19,PolyHom.zero 26 19] b
theorem polyLiftFree26_19 : ∀ b : Fin 3, (polyLift26_19 b).freeBlock=basisInt (homKind 26 19) b := by decide
def polyRep26_20_0 : PolyHom 26 20 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_20 (b : Fin 3) : PolyHom 26 20 :=
  ![polyRep26_20_0,PolyHom.zero 26 20,PolyHom.zero 26 20] b
theorem polyLiftFree26_20 : ∀ b : Fin 3, (polyLift26_20 b).freeBlock=basisInt (homKind 26 20) b := by decide
def polyRep26_21_0 : PolyHom 26 21 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_21_1 : PolyHom 26 21 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_21 (b : Fin 3) : PolyHom 26 21 :=
  ![polyRep26_21_0,polyRep26_21_1,PolyHom.zero 26 21] b
theorem polyLiftFree26_21 : ∀ b : Fin 3, (polyLift26_21 b).freeBlock=basisInt (homKind 26 21) b := by decide
def polyRep26_22_0 : PolyHom 26 22 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_22_1 : PolyHom 26 22 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_22 (b : Fin 3) : PolyHom 26 22 :=
  ![polyRep26_22_0,polyRep26_22_1,PolyHom.zero 26 22] b
theorem polyLiftFree26_22 : ∀ b : Fin 3, (polyLift26_22 b).freeBlock=basisInt (homKind 26 22) b := by decide
def polyRep26_23_0 : PolyHom 26 23 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_23 (b : Fin 3) : PolyHom 26 23 :=
  ![polyRep26_23_0,PolyHom.zero 26 23,PolyHom.zero 26 23] b
theorem polyLiftFree26_23 : ∀ b : Fin 3, (polyLift26_23 b).freeBlock=basisInt (homKind 26 23) b := by decide
def polyRep26_24_0 : PolyHom 26 24 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 1),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_24_1 : PolyHom 26 24 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_24 (b : Fin 3) : PolyHom 26 24 :=
  ![polyRep26_24_0,polyRep26_24_1,PolyHom.zero 26 24] b
theorem polyLiftFree26_24 : ∀ b : Fin 3, (polyLift26_24 b).freeBlock=basisInt (homKind 26 24) b := by decide
def polyRep26_25_0 : PolyHom 26 25 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_25_1 : PolyHom 26 25 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_25 (b : Fin 3) : PolyHom 26 25 :=
  ![polyRep26_25_0,polyRep26_25_1,PolyHom.zero 26 25] b
theorem polyLiftFree26_25 : ∀ b : Fin 3, (polyLift26_25 b).freeBlock=basisInt (homKind 26 25) b := by decide
def polyRep26_26_0 : PolyHom 26 26 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_26_1 : PolyHom 26 26 where
  M := !![0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_26 (b : Fin 3) : PolyHom 26 26 :=
  ![polyRep26_26_0,polyRep26_26_1,PolyHom.zero 26 26] b
theorem polyLiftFree26_26 : ∀ b : Fin 3, (polyLift26_26 b).freeBlock=basisInt (homKind 26 26) b := by decide
def polyRep26_27_0 : PolyHom 26 27 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_27_1 : PolyHom 26 27 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_27 (b : Fin 3) : PolyHom 26 27 :=
  ![polyRep26_27_0,polyRep26_27_1,PolyHom.zero 26 27] b
theorem polyLiftFree26_27 : ∀ b : Fin 3, (polyLift26_27 b).freeBlock=basisInt (homKind 26 27) b := by decide
def polyRep26_28_0 : PolyHom 26 28 where
  M := !![0,0,0,0;0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_28 (b : Fin 3) : PolyHom 26 28 :=
  ![polyRep26_28_0,PolyHom.zero 26 28,PolyHom.zero 26 28] b
theorem polyLiftFree26_28 : ∀ b : Fin 3, (polyLift26_28 b).freeBlock=basisInt (homKind 26 28) b := by decide
def polyRep26_29_0 : PolyHom 26 29 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_29 (b : Fin 3) : PolyHom 26 29 :=
  ![polyRep26_29_0,PolyHom.zero 26 29,PolyHom.zero 26 29] b
theorem polyLiftFree26_29 : ∀ b : Fin 3, (polyLift26_29 b).freeBlock=basisInt (homKind 26 29) b := by decide
def polyRep26_30_0 : PolyHom 26 30 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_30_1 : PolyHom 26 30 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_30_2 : PolyHom 26 30 where
  M := !![0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,(mono6 (-1) 0);0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_30 (b : Fin 3) : PolyHom 26 30 :=
  ![polyRep26_30_0,polyRep26_30_1,polyRep26_30_2] b
theorem polyLiftFree26_30 : ∀ b : Fin 3, (polyLift26_30 b).freeBlock=basisInt (homKind 26 30) b := by decide
def polyRep26_31_0 : PolyHom 26 31 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_31_1 : PolyHom 26 31 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_31 (b : Fin 3) : PolyHom 26 31 :=
  ![polyRep26_31_0,polyRep26_31_1,PolyHom.zero 26 31] b
theorem polyLiftFree26_31 : ∀ b : Fin 3, (polyLift26_31 b).freeBlock=basisInt (homKind 26 31) b := by decide
def polyRep26_32_0 : PolyHom 26 32 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_32_1 : PolyHom 26 32 where
  M := !![0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_32 (b : Fin 3) : PolyHom 26 32 :=
  ![polyRep26_32_0,polyRep26_32_1,PolyHom.zero 26 32] b
theorem polyLiftFree26_32 : ∀ b : Fin 3, (polyLift26_32 b).freeBlock=basisInt (homKind 26 32) b := by decide
def polyRep26_33_0 : PolyHom 26 33 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_33 (b : Fin 3) : PolyHom 26 33 :=
  ![polyRep26_33_0,PolyHom.zero 26 33,PolyHom.zero 26 33] b
theorem polyLiftFree26_33 : ∀ b : Fin 3, (polyLift26_33 b).freeBlock=basisInt (homKind 26 33) b := by decide
def polyRep26_34_0 : PolyHom 26 34 where
  M := !![0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_34 (b : Fin 3) : PolyHom 26 34 :=
  ![polyRep26_34_0,PolyHom.zero 26 34,PolyHom.zero 26 34] b
theorem polyLiftFree26_34 : ∀ b : Fin 3, (polyLift26_34 b).freeBlock=basisInt (homKind 26 34) b := by decide
def polyRep26_35_0 : PolyHom 26 35 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_35 (b : Fin 3) : PolyHom 26 35 :=
  ![polyRep26_35_0,PolyHom.zero 26 35,PolyHom.zero 26 35] b
theorem polyLiftFree26_35 : ∀ b : Fin 3, (polyLift26_35 b).freeBlock=basisInt (homKind 26 35) b := by decide
def polyRep26_36_0 : PolyHom 26 36 where
  M := !![0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_36 (b : Fin 3) : PolyHom 26 36 :=
  ![polyRep26_36_0,PolyHom.zero 26 36,PolyHom.zero 26 36] b
theorem polyLiftFree26_36 : ∀ b : Fin 3, (polyLift26_36 b).freeBlock=basisInt (homKind 26 36) b := by decide
def polyRep26_37_0 : PolyHom 26 37 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_37_1 : PolyHom 26 37 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_37_2 : PolyHom 26 37 where
  M := !![0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,(mono6 (-1) 0);0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_37 (b : Fin 3) : PolyHom 26 37 :=
  ![polyRep26_37_0,polyRep26_37_1,polyRep26_37_2] b
theorem polyLiftFree26_37 : ∀ b : Fin 3, (polyLift26_37 b).freeBlock=basisInt (homKind 26 37) b := by decide
def polyRep26_38_0 : PolyHom 26 38 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_38_1 : PolyHom 26 38 where
  M := !![0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_38_2 : PolyHom 26 38 where
  M := !![0,0,0,0;0,0,0,(mono6 (-1) 1);0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,(mono6 (-1) 0);0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_38 (b : Fin 3) : PolyHom 26 38 :=
  ![polyRep26_38_0,polyRep26_38_1,polyRep26_38_2] b
theorem polyLiftFree26_38 : ∀ b : Fin 3, (polyLift26_38 b).freeBlock=basisInt (homKind 26 38) b := by decide
def polyRep26_39_0 : PolyHom 26 39 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_39_1 : PolyHom 26 39 where
  M := !![0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_39 (b : Fin 3) : PolyHom 26 39 :=
  ![polyRep26_39_0,polyRep26_39_1,PolyHom.zero 26 39] b
theorem polyLiftFree26_39 : ∀ b : Fin 3, (polyLift26_39 b).freeBlock=basisInt (homKind 26 39) b := by decide
def polyRep26_40_0 : PolyHom 26 40 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_40_1 : PolyHom 26 40 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_40_2 : PolyHom 26 40 where
  M := !![0,0,0,0;0,0,0,(mono6 (-1) 1);0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,(mono6 (-1) 0);0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_40 (b : Fin 3) : PolyHom 26 40 :=
  ![polyRep26_40_0,polyRep26_40_1,polyRep26_40_2] b
theorem polyLiftFree26_40 : ∀ b : Fin 3, (polyLift26_40 b).freeBlock=basisInt (homKind 26 40) b := by decide
def polyRep26_41_0 : PolyHom 26 41 where
  M := !![0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_41 (b : Fin 3) : PolyHom 26 41 :=
  ![polyRep26_41_0,PolyHom.zero 26 41,PolyHom.zero 26 41] b
theorem polyLiftFree26_41 : ∀ b : Fin 3, (polyLift26_41 b).freeBlock=basisInt (homKind 26 41) b := by decide
def polyRep26_42_0 : PolyHom 26 42 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_42_1 : PolyHom 26 42 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_42_2 : PolyHom 26 42 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_42 (b : Fin 3) : PolyHom 26 42 :=
  ![polyRep26_42_0,polyRep26_42_1,polyRep26_42_2] b
theorem polyLiftFree26_42 : ∀ b : Fin 3, (polyLift26_42 b).freeBlock=basisInt (homKind 26 42) b := by decide
def polyRep26_43_0 : PolyHom 26 43 where
  M := !![0,0,0,0;0,0,(mono6 (-1) 1),0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (-1) 1),0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_43_1 : PolyHom 26 43 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 1),0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![(mono6 (1) 1),0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_43 (b : Fin 3) : PolyHom 26 43 :=
  ![polyRep26_43_0,polyRep26_43_1,PolyHom.zero 26 43] b
theorem polyLiftFree26_43 : ∀ b : Fin 3, (polyLift26_43 b).freeBlock=basisInt (homKind 26 43) b := by decide
def polyRep26_44_0 : PolyHom 26 44 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_44_1 : PolyHom 26 44 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_44_2 : PolyHom 26 44 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_44 (b : Fin 3) : PolyHom 26 44 :=
  ![polyRep26_44_0,polyRep26_44_1,polyRep26_44_2] b
theorem polyLiftFree26_44 : ∀ b : Fin 3, (polyLift26_44 b).freeBlock=basisInt (homKind 26 44) b := by decide
def polyRep26_45_0 : PolyHom 26 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep26_45_1 : PolyHom 26 45 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift26_45 (b : Fin 3) : PolyHom 26 45 :=
  ![polyRep26_45_0,polyRep26_45_1,PolyHom.zero 26 45] b
theorem polyLiftFree26_45 : ∀ b : Fin 3, (polyLift26_45 b).freeBlock=basisInt (homKind 26 45) b := by decide
def polyLift26_46 (b : Fin 3) : PolyHom 26 46 :=
  ![PolyHom.zero 26 46,PolyHom.zero 26 46,PolyHom.zero 26 46] b
theorem polyLiftFree26_46 : ∀ b : Fin 3, (polyLift26_46 b).freeBlock=basisInt (homKind 26 46) b := by decide
def polyLiftRow26 (j : Fin 47) (b : Fin 3) : PolyHom 26 j :=
  match j with
  | ⟨0,_⟩ => polyLift26_0 b
  | ⟨1,_⟩ => polyLift26_1 b
  | ⟨2,_⟩ => polyLift26_2 b
  | ⟨3,_⟩ => polyLift26_3 b
  | ⟨4,_⟩ => polyLift26_4 b
  | ⟨5,_⟩ => polyLift26_5 b
  | ⟨6,_⟩ => polyLift26_6 b
  | ⟨7,_⟩ => polyLift26_7 b
  | ⟨8,_⟩ => polyLift26_8 b
  | ⟨9,_⟩ => polyLift26_9 b
  | ⟨10,_⟩ => polyLift26_10 b
  | ⟨11,_⟩ => polyLift26_11 b
  | ⟨12,_⟩ => polyLift26_12 b
  | ⟨13,_⟩ => polyLift26_13 b
  | ⟨14,_⟩ => polyLift26_14 b
  | ⟨15,_⟩ => polyLift26_15 b
  | ⟨16,_⟩ => polyLift26_16 b
  | ⟨17,_⟩ => polyLift26_17 b
  | ⟨18,_⟩ => polyLift26_18 b
  | ⟨19,_⟩ => polyLift26_19 b
  | ⟨20,_⟩ => polyLift26_20 b
  | ⟨21,_⟩ => polyLift26_21 b
  | ⟨22,_⟩ => polyLift26_22 b
  | ⟨23,_⟩ => polyLift26_23 b
  | ⟨24,_⟩ => polyLift26_24 b
  | ⟨25,_⟩ => polyLift26_25 b
  | ⟨26,_⟩ => polyLift26_26 b
  | ⟨27,_⟩ => polyLift26_27 b
  | ⟨28,_⟩ => polyLift26_28 b
  | ⟨29,_⟩ => polyLift26_29 b
  | ⟨30,_⟩ => polyLift26_30 b
  | ⟨31,_⟩ => polyLift26_31 b
  | ⟨32,_⟩ => polyLift26_32 b
  | ⟨33,_⟩ => polyLift26_33 b
  | ⟨34,_⟩ => polyLift26_34 b
  | ⟨35,_⟩ => polyLift26_35 b
  | ⟨36,_⟩ => polyLift26_36 b
  | ⟨37,_⟩ => polyLift26_37 b
  | ⟨38,_⟩ => polyLift26_38 b
  | ⟨39,_⟩ => polyLift26_39 b
  | ⟨40,_⟩ => polyLift26_40 b
  | ⟨41,_⟩ => polyLift26_41 b
  | ⟨42,_⟩ => polyLift26_42 b
  | ⟨43,_⟩ => polyLift26_43 b
  | ⟨44,_⟩ => polyLift26_44 b
  | ⟨45,_⟩ => polyLift26_45 b
  | ⟨46,_⟩ => polyLift26_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree26 (j : Fin 47) (b : Fin 3) : (polyLiftRow26 j b).freeBlock=basisInt (homKind 26 j) b := by
  fin_cases j
  · exact polyLiftFree26_0 b
  · exact polyLiftFree26_1 b
  · exact polyLiftFree26_2 b
  · exact polyLiftFree26_3 b
  · exact polyLiftFree26_4 b
  · exact polyLiftFree26_5 b
  · exact polyLiftFree26_6 b
  · exact polyLiftFree26_7 b
  · exact polyLiftFree26_8 b
  · exact polyLiftFree26_9 b
  · exact polyLiftFree26_10 b
  · exact polyLiftFree26_11 b
  · exact polyLiftFree26_12 b
  · exact polyLiftFree26_13 b
  · exact polyLiftFree26_14 b
  · exact polyLiftFree26_15 b
  · exact polyLiftFree26_16 b
  · exact polyLiftFree26_17 b
  · exact polyLiftFree26_18 b
  · exact polyLiftFree26_19 b
  · exact polyLiftFree26_20 b
  · exact polyLiftFree26_21 b
  · exact polyLiftFree26_22 b
  · exact polyLiftFree26_23 b
  · exact polyLiftFree26_24 b
  · exact polyLiftFree26_25 b
  · exact polyLiftFree26_26 b
  · exact polyLiftFree26_27 b
  · exact polyLiftFree26_28 b
  · exact polyLiftFree26_29 b
  · exact polyLiftFree26_30 b
  · exact polyLiftFree26_31 b
  · exact polyLiftFree26_32 b
  · exact polyLiftFree26_33 b
  · exact polyLiftFree26_34 b
  · exact polyLiftFree26_35 b
  · exact polyLiftFree26_36 b
  · exact polyLiftFree26_37 b
  · exact polyLiftFree26_38 b
  · exact polyLiftFree26_39 b
  · exact polyLiftFree26_40 b
  · exact polyLiftFree26_41 b
  · exact polyLiftFree26_42 b
  · exact polyLiftFree26_43 b
  · exact polyLiftFree26_44 b
  · exact polyLiftFree26_45 b
  · exact polyLiftFree26_46 b
end UniserialComputations.N6
