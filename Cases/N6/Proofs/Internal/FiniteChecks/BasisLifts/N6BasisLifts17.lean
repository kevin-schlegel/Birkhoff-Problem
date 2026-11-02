import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift17_0 (b : Fin 3) : PolyHom 17 0 :=
  ![PolyHom.zero 17 0,PolyHom.zero 17 0,PolyHom.zero 17 0] b
theorem polyLiftFree17_0 : ∀ b : Fin 3, (polyLift17_0 b).freeBlock=basisInt (homKind 17 0) b := by decide
def polyLift17_1 (b : Fin 3) : PolyHom 17 1 :=
  ![PolyHom.zero 17 1,PolyHom.zero 17 1,PolyHom.zero 17 1] b
theorem polyLiftFree17_1 : ∀ b : Fin 3, (polyLift17_1 b).freeBlock=basisInt (homKind 17 1) b := by decide
def polyLift17_2 (b : Fin 3) : PolyHom 17 2 :=
  ![PolyHom.zero 17 2,PolyHom.zero 17 2,PolyHom.zero 17 2] b
theorem polyLiftFree17_2 : ∀ b : Fin 3, (polyLift17_2 b).freeBlock=basisInt (homKind 17 2) b := by decide
def polyLift17_3 (b : Fin 3) : PolyHom 17 3 :=
  ![PolyHom.zero 17 3,PolyHom.zero 17 3,PolyHom.zero 17 3] b
theorem polyLiftFree17_3 : ∀ b : Fin 3, (polyLift17_3 b).freeBlock=basisInt (homKind 17 3) b := by decide
def polyLift17_4 (b : Fin 3) : PolyHom 17 4 :=
  ![PolyHom.zero 17 4,PolyHom.zero 17 4,PolyHom.zero 17 4] b
theorem polyLiftFree17_4 : ∀ b : Fin 3, (polyLift17_4 b).freeBlock=basisInt (homKind 17 4) b := by decide
def polyLift17_5 (b : Fin 3) : PolyHom 17 5 :=
  ![PolyHom.zero 17 5,PolyHom.zero 17 5,PolyHom.zero 17 5] b
theorem polyLiftFree17_5 : ∀ b : Fin 3, (polyLift17_5 b).freeBlock=basisInt (homKind 17 5) b := by decide
def polyRep17_6_0 : PolyHom 17 6 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_6 (b : Fin 3) : PolyHom 17 6 :=
  ![polyRep17_6_0,PolyHom.zero 17 6,PolyHom.zero 17 6] b
theorem polyLiftFree17_6 : ∀ b : Fin 3, (polyLift17_6 b).freeBlock=basisInt (homKind 17 6) b := by decide
def polyRep17_7_0 : PolyHom 17 7 where
  M := !![(mono6 (1) 2),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_7 (b : Fin 3) : PolyHom 17 7 :=
  ![polyRep17_7_0,PolyHom.zero 17 7,PolyHom.zero 17 7] b
theorem polyLiftFree17_7 : ∀ b : Fin 3, (polyLift17_7 b).freeBlock=basisInt (homKind 17 7) b := by decide
def polyRep17_8_0 : PolyHom 17 8 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_8 (b : Fin 3) : PolyHom 17 8 :=
  ![polyRep17_8_0,PolyHom.zero 17 8,PolyHom.zero 17 8] b
theorem polyLiftFree17_8 : ∀ b : Fin 3, (polyLift17_8 b).freeBlock=basisInt (homKind 17 8) b := by decide
def polyLift17_9 (b : Fin 3) : PolyHom 17 9 :=
  ![PolyHom.zero 17 9,PolyHom.zero 17 9,PolyHom.zero 17 9] b
theorem polyLiftFree17_9 : ∀ b : Fin 3, (polyLift17_9 b).freeBlock=basisInt (homKind 17 9) b := by decide
def polyRep17_10_0 : PolyHom 17 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_10 (b : Fin 3) : PolyHom 17 10 :=
  ![polyRep17_10_0,PolyHom.zero 17 10,PolyHom.zero 17 10] b
theorem polyLiftFree17_10 : ∀ b : Fin 3, (polyLift17_10 b).freeBlock=basisInt (homKind 17 10) b := by decide
def polyRep17_11_0 : PolyHom 17 11 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_11 (b : Fin 3) : PolyHom 17 11 :=
  ![polyRep17_11_0,PolyHom.zero 17 11,PolyHom.zero 17 11] b
theorem polyLiftFree17_11 : ∀ b : Fin 3, (polyLift17_11 b).freeBlock=basisInt (homKind 17 11) b := by decide
def polyRep17_12_0 : PolyHom 17 12 where
  M := !![(mono6 (1) 2),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_12 (b : Fin 3) : PolyHom 17 12 :=
  ![polyRep17_12_0,PolyHom.zero 17 12,PolyHom.zero 17 12] b
theorem polyLiftFree17_12 : ∀ b : Fin 3, (polyLift17_12 b).freeBlock=basisInt (homKind 17 12) b := by decide
def polyRep17_13_0 : PolyHom 17 13 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_13 (b : Fin 3) : PolyHom 17 13 :=
  ![polyRep17_13_0,PolyHom.zero 17 13,PolyHom.zero 17 13] b
theorem polyLiftFree17_13 : ∀ b : Fin 3, (polyLift17_13 b).freeBlock=basisInt (homKind 17 13) b := by decide
def polyLift17_14 (b : Fin 3) : PolyHom 17 14 :=
  ![PolyHom.zero 17 14,PolyHom.zero 17 14,PolyHom.zero 17 14] b
theorem polyLiftFree17_14 : ∀ b : Fin 3, (polyLift17_14 b).freeBlock=basisInt (homKind 17 14) b := by decide
def polyLift17_15 (b : Fin 3) : PolyHom 17 15 :=
  ![PolyHom.zero 17 15,PolyHom.zero 17 15,PolyHom.zero 17 15] b
theorem polyLiftFree17_15 : ∀ b : Fin 3, (polyLift17_15 b).freeBlock=basisInt (homKind 17 15) b := by decide
def polyRep17_16_0 : PolyHom 17 16 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_16 (b : Fin 3) : PolyHom 17 16 :=
  ![polyRep17_16_0,PolyHom.zero 17 16,PolyHom.zero 17 16] b
theorem polyLiftFree17_16 : ∀ b : Fin 3, (polyLift17_16 b).freeBlock=basisInt (homKind 17 16) b := by decide
def polyRep17_17_0 : PolyHom 17 17 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_17 (b : Fin 3) : PolyHom 17 17 :=
  ![polyRep17_17_0,PolyHom.zero 17 17,PolyHom.zero 17 17] b
theorem polyLiftFree17_17 : ∀ b : Fin 3, (polyLift17_17 b).freeBlock=basisInt (homKind 17 17) b := by decide
def polyRep17_18_0 : PolyHom 17 18 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_18 (b : Fin 3) : PolyHom 17 18 :=
  ![polyRep17_18_0,PolyHom.zero 17 18,PolyHom.zero 17 18] b
theorem polyLiftFree17_18 : ∀ b : Fin 3, (polyLift17_18 b).freeBlock=basisInt (homKind 17 18) b := by decide
def polyRep17_19_0 : PolyHom 17 19 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_19 (b : Fin 3) : PolyHom 17 19 :=
  ![polyRep17_19_0,PolyHom.zero 17 19,PolyHom.zero 17 19] b
theorem polyLiftFree17_19 : ∀ b : Fin 3, (polyLift17_19 b).freeBlock=basisInt (homKind 17 19) b := by decide
def polyRep17_20_0 : PolyHom 17 20 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_20 (b : Fin 3) : PolyHom 17 20 :=
  ![polyRep17_20_0,PolyHom.zero 17 20,PolyHom.zero 17 20] b
theorem polyLiftFree17_20 : ∀ b : Fin 3, (polyLift17_20 b).freeBlock=basisInt (homKind 17 20) b := by decide
def polyRep17_21_0 : PolyHom 17 21 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_21 (b : Fin 3) : PolyHom 17 21 :=
  ![polyRep17_21_0,PolyHom.zero 17 21,PolyHom.zero 17 21] b
theorem polyLiftFree17_21 : ∀ b : Fin 3, (polyLift17_21 b).freeBlock=basisInt (homKind 17 21) b := by decide
def polyRep17_22_0 : PolyHom 17 22 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_22 (b : Fin 3) : PolyHom 17 22 :=
  ![polyRep17_22_0,PolyHom.zero 17 22,PolyHom.zero 17 22] b
theorem polyLiftFree17_22 : ∀ b : Fin 3, (polyLift17_22 b).freeBlock=basisInt (homKind 17 22) b := by decide
def polyRep17_23_0 : PolyHom 17 23 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_23 (b : Fin 3) : PolyHom 17 23 :=
  ![polyRep17_23_0,PolyHom.zero 17 23,PolyHom.zero 17 23] b
theorem polyLiftFree17_23 : ∀ b : Fin 3, (polyLift17_23 b).freeBlock=basisInt (homKind 17 23) b := by decide
def polyRep17_24_0 : PolyHom 17 24 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_24 (b : Fin 3) : PolyHom 17 24 :=
  ![polyRep17_24_0,PolyHom.zero 17 24,PolyHom.zero 17 24] b
theorem polyLiftFree17_24 : ∀ b : Fin 3, (polyLift17_24 b).freeBlock=basisInt (homKind 17 24) b := by decide
def polyRep17_25_0 : PolyHom 17 25 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_25 (b : Fin 3) : PolyHom 17 25 :=
  ![polyRep17_25_0,PolyHom.zero 17 25,PolyHom.zero 17 25] b
theorem polyLiftFree17_25 : ∀ b : Fin 3, (polyLift17_25 b).freeBlock=basisInt (homKind 17 25) b := by decide
def polyRep17_26_0 : PolyHom 17 26 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_26 (b : Fin 3) : PolyHom 17 26 :=
  ![polyRep17_26_0,PolyHom.zero 17 26,PolyHom.zero 17 26] b
theorem polyLiftFree17_26 : ∀ b : Fin 3, (polyLift17_26 b).freeBlock=basisInt (homKind 17 26) b := by decide
def polyRep17_27_0 : PolyHom 17 27 where
  M := !![(mono6 (1) 1),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_27 (b : Fin 3) : PolyHom 17 27 :=
  ![polyRep17_27_0,PolyHom.zero 17 27,PolyHom.zero 17 27] b
theorem polyLiftFree17_27 : ∀ b : Fin 3, (polyLift17_27 b).freeBlock=basisInt (homKind 17 27) b := by decide
def polyRep17_28_0 : PolyHom 17 28 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_28 (b : Fin 3) : PolyHom 17 28 :=
  ![polyRep17_28_0,PolyHom.zero 17 28,PolyHom.zero 17 28] b
theorem polyLiftFree17_28 : ∀ b : Fin 3, (polyLift17_28 b).freeBlock=basisInt (homKind 17 28) b := by decide
def polyRep17_29_0 : PolyHom 17 29 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_29 (b : Fin 3) : PolyHom 17 29 :=
  ![polyRep17_29_0,PolyHom.zero 17 29,PolyHom.zero 17 29] b
theorem polyLiftFree17_29 : ∀ b : Fin 3, (polyLift17_29 b).freeBlock=basisInt (homKind 17 29) b := by decide
def polyRep17_30_0 : PolyHom 17 30 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_30 (b : Fin 3) : PolyHom 17 30 :=
  ![polyRep17_30_0,PolyHom.zero 17 30,PolyHom.zero 17 30] b
theorem polyLiftFree17_30 : ∀ b : Fin 3, (polyLift17_30 b).freeBlock=basisInt (homKind 17 30) b := by decide
def polyRep17_31_0 : PolyHom 17 31 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_31 (b : Fin 3) : PolyHom 17 31 :=
  ![polyRep17_31_0,PolyHom.zero 17 31,PolyHom.zero 17 31] b
theorem polyLiftFree17_31 : ∀ b : Fin 3, (polyLift17_31 b).freeBlock=basisInt (homKind 17 31) b := by decide
def polyRep17_32_0 : PolyHom 17 32 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_32 (b : Fin 3) : PolyHom 17 32 :=
  ![polyRep17_32_0,PolyHom.zero 17 32,PolyHom.zero 17 32] b
theorem polyLiftFree17_32 : ∀ b : Fin 3, (polyLift17_32 b).freeBlock=basisInt (homKind 17 32) b := by decide
def polyRep17_33_0 : PolyHom 17 33 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_33 (b : Fin 3) : PolyHom 17 33 :=
  ![polyRep17_33_0,PolyHom.zero 17 33,PolyHom.zero 17 33] b
theorem polyLiftFree17_33 : ∀ b : Fin 3, (polyLift17_33 b).freeBlock=basisInt (homKind 17 33) b := by decide
def polyRep17_34_0 : PolyHom 17 34 where
  M := !![0,(mono6 (-1) 2),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_34 (b : Fin 3) : PolyHom 17 34 :=
  ![polyRep17_34_0,PolyHom.zero 17 34,PolyHom.zero 17 34] b
theorem polyLiftFree17_34 : ∀ b : Fin 3, (polyLift17_34 b).freeBlock=basisInt (homKind 17 34) b := by decide
def polyRep17_35_0 : PolyHom 17 35 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_35 (b : Fin 3) : PolyHom 17 35 :=
  ![polyRep17_35_0,PolyHom.zero 17 35,PolyHom.zero 17 35] b
theorem polyLiftFree17_35 : ∀ b : Fin 3, (polyLift17_35 b).freeBlock=basisInt (homKind 17 35) b := by decide
def polyRep17_36_0 : PolyHom 17 36 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_36 (b : Fin 3) : PolyHom 17 36 :=
  ![polyRep17_36_0,PolyHom.zero 17 36,PolyHom.zero 17 36] b
theorem polyLiftFree17_36 : ∀ b : Fin 3, (polyLift17_36 b).freeBlock=basisInt (homKind 17 36) b := by decide
def polyRep17_37_0 : PolyHom 17 37 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_37 (b : Fin 3) : PolyHom 17 37 :=
  ![polyRep17_37_0,PolyHom.zero 17 37,PolyHom.zero 17 37] b
theorem polyLiftFree17_37 : ∀ b : Fin 3, (polyLift17_37 b).freeBlock=basisInt (homKind 17 37) b := by decide
def polyRep17_38_0 : PolyHom 17 38 where
  M := !![(mono6 (1) 1),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_38 (b : Fin 3) : PolyHom 17 38 :=
  ![polyRep17_38_0,PolyHom.zero 17 38,PolyHom.zero 17 38] b
theorem polyLiftFree17_38 : ∀ b : Fin 3, (polyLift17_38 b).freeBlock=basisInt (homKind 17 38) b := by decide
def polyRep17_39_0 : PolyHom 17 39 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_39 (b : Fin 3) : PolyHom 17 39 :=
  ![polyRep17_39_0,PolyHom.zero 17 39,PolyHom.zero 17 39] b
theorem polyLiftFree17_39 : ∀ b : Fin 3, (polyLift17_39 b).freeBlock=basisInt (homKind 17 39) b := by decide
def polyRep17_40_0 : PolyHom 17 40 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_40 (b : Fin 3) : PolyHom 17 40 :=
  ![polyRep17_40_0,PolyHom.zero 17 40,PolyHom.zero 17 40] b
theorem polyLiftFree17_40 : ∀ b : Fin 3, (polyLift17_40 b).freeBlock=basisInt (homKind 17 40) b := by decide
def polyRep17_41_0 : PolyHom 17 41 where
  M := !![0,(mono6 (-1) 1),0,(mono6 (1) 0);0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_41 (b : Fin 3) : PolyHom 17 41 :=
  ![polyRep17_41_0,PolyHom.zero 17 41,PolyHom.zero 17 41] b
theorem polyLiftFree17_41 : ∀ b : Fin 3, (polyLift17_41 b).freeBlock=basisInt (homKind 17 41) b := by decide
def polyRep17_42_0 : PolyHom 17 42 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep17_42_1 : PolyHom 17 42 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_42 (b : Fin 3) : PolyHom 17 42 :=
  ![polyRep17_42_0,polyRep17_42_1,PolyHom.zero 17 42] b
theorem polyLiftFree17_42 : ∀ b : Fin 3, (polyLift17_42 b).freeBlock=basisInt (homKind 17 42) b := by decide
def polyRep17_43_0 : PolyHom 17 43 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep17_43_1 : PolyHom 17 43 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_43 (b : Fin 3) : PolyHom 17 43 :=
  ![polyRep17_43_0,polyRep17_43_1,PolyHom.zero 17 43] b
theorem polyLiftFree17_43 : ∀ b : Fin 3, (polyLift17_43 b).freeBlock=basisInt (homKind 17 43) b := by decide
def polyRep17_44_0 : PolyHom 17 44 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep17_44_1 : PolyHom 17 44 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_44 (b : Fin 3) : PolyHom 17 44 :=
  ![polyRep17_44_0,polyRep17_44_1,PolyHom.zero 17 44] b
theorem polyLiftFree17_44 : ∀ b : Fin 3, (polyLift17_44 b).freeBlock=basisInt (homKind 17 44) b := by decide
def polyRep17_45_0 : PolyHom 17 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift17_45 (b : Fin 3) : PolyHom 17 45 :=
  ![polyRep17_45_0,PolyHom.zero 17 45,PolyHom.zero 17 45] b
theorem polyLiftFree17_45 : ∀ b : Fin 3, (polyLift17_45 b).freeBlock=basisInt (homKind 17 45) b := by decide
def polyLift17_46 (b : Fin 3) : PolyHom 17 46 :=
  ![PolyHom.zero 17 46,PolyHom.zero 17 46,PolyHom.zero 17 46] b
theorem polyLiftFree17_46 : ∀ b : Fin 3, (polyLift17_46 b).freeBlock=basisInt (homKind 17 46) b := by decide
def polyLiftRow17 (j : Fin 47) (b : Fin 3) : PolyHom 17 j :=
  match j with
  | ⟨0,_⟩ => polyLift17_0 b
  | ⟨1,_⟩ => polyLift17_1 b
  | ⟨2,_⟩ => polyLift17_2 b
  | ⟨3,_⟩ => polyLift17_3 b
  | ⟨4,_⟩ => polyLift17_4 b
  | ⟨5,_⟩ => polyLift17_5 b
  | ⟨6,_⟩ => polyLift17_6 b
  | ⟨7,_⟩ => polyLift17_7 b
  | ⟨8,_⟩ => polyLift17_8 b
  | ⟨9,_⟩ => polyLift17_9 b
  | ⟨10,_⟩ => polyLift17_10 b
  | ⟨11,_⟩ => polyLift17_11 b
  | ⟨12,_⟩ => polyLift17_12 b
  | ⟨13,_⟩ => polyLift17_13 b
  | ⟨14,_⟩ => polyLift17_14 b
  | ⟨15,_⟩ => polyLift17_15 b
  | ⟨16,_⟩ => polyLift17_16 b
  | ⟨17,_⟩ => polyLift17_17 b
  | ⟨18,_⟩ => polyLift17_18 b
  | ⟨19,_⟩ => polyLift17_19 b
  | ⟨20,_⟩ => polyLift17_20 b
  | ⟨21,_⟩ => polyLift17_21 b
  | ⟨22,_⟩ => polyLift17_22 b
  | ⟨23,_⟩ => polyLift17_23 b
  | ⟨24,_⟩ => polyLift17_24 b
  | ⟨25,_⟩ => polyLift17_25 b
  | ⟨26,_⟩ => polyLift17_26 b
  | ⟨27,_⟩ => polyLift17_27 b
  | ⟨28,_⟩ => polyLift17_28 b
  | ⟨29,_⟩ => polyLift17_29 b
  | ⟨30,_⟩ => polyLift17_30 b
  | ⟨31,_⟩ => polyLift17_31 b
  | ⟨32,_⟩ => polyLift17_32 b
  | ⟨33,_⟩ => polyLift17_33 b
  | ⟨34,_⟩ => polyLift17_34 b
  | ⟨35,_⟩ => polyLift17_35 b
  | ⟨36,_⟩ => polyLift17_36 b
  | ⟨37,_⟩ => polyLift17_37 b
  | ⟨38,_⟩ => polyLift17_38 b
  | ⟨39,_⟩ => polyLift17_39 b
  | ⟨40,_⟩ => polyLift17_40 b
  | ⟨41,_⟩ => polyLift17_41 b
  | ⟨42,_⟩ => polyLift17_42 b
  | ⟨43,_⟩ => polyLift17_43 b
  | ⟨44,_⟩ => polyLift17_44 b
  | ⟨45,_⟩ => polyLift17_45 b
  | ⟨46,_⟩ => polyLift17_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree17 (j : Fin 47) (b : Fin 3) : (polyLiftRow17 j b).freeBlock=basisInt (homKind 17 j) b := by
  fin_cases j
  · exact polyLiftFree17_0 b
  · exact polyLiftFree17_1 b
  · exact polyLiftFree17_2 b
  · exact polyLiftFree17_3 b
  · exact polyLiftFree17_4 b
  · exact polyLiftFree17_5 b
  · exact polyLiftFree17_6 b
  · exact polyLiftFree17_7 b
  · exact polyLiftFree17_8 b
  · exact polyLiftFree17_9 b
  · exact polyLiftFree17_10 b
  · exact polyLiftFree17_11 b
  · exact polyLiftFree17_12 b
  · exact polyLiftFree17_13 b
  · exact polyLiftFree17_14 b
  · exact polyLiftFree17_15 b
  · exact polyLiftFree17_16 b
  · exact polyLiftFree17_17 b
  · exact polyLiftFree17_18 b
  · exact polyLiftFree17_19 b
  · exact polyLiftFree17_20 b
  · exact polyLiftFree17_21 b
  · exact polyLiftFree17_22 b
  · exact polyLiftFree17_23 b
  · exact polyLiftFree17_24 b
  · exact polyLiftFree17_25 b
  · exact polyLiftFree17_26 b
  · exact polyLiftFree17_27 b
  · exact polyLiftFree17_28 b
  · exact polyLiftFree17_29 b
  · exact polyLiftFree17_30 b
  · exact polyLiftFree17_31 b
  · exact polyLiftFree17_32 b
  · exact polyLiftFree17_33 b
  · exact polyLiftFree17_34 b
  · exact polyLiftFree17_35 b
  · exact polyLiftFree17_36 b
  · exact polyLiftFree17_37 b
  · exact polyLiftFree17_38 b
  · exact polyLiftFree17_39 b
  · exact polyLiftFree17_40 b
  · exact polyLiftFree17_41 b
  · exact polyLiftFree17_42 b
  · exact polyLiftFree17_43 b
  · exact polyLiftFree17_44 b
  · exact polyLiftFree17_45 b
  · exact polyLiftFree17_46 b
end UniserialComputations.N6
