import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift4_0 (b : Fin 3) : PolyHom 4 0 :=
  ![PolyHom.zero 4 0,PolyHom.zero 4 0,PolyHom.zero 4 0] b
theorem polyLiftFree4_0 : ∀ b : Fin 3, (polyLift4_0 b).freeBlock=basisInt (homKind 4 0) b := by decide
def polyLift4_1 (b : Fin 3) : PolyHom 4 1 :=
  ![PolyHom.zero 4 1,PolyHom.zero 4 1,PolyHom.zero 4 1] b
theorem polyLiftFree4_1 : ∀ b : Fin 3, (polyLift4_1 b).freeBlock=basisInt (homKind 4 1) b := by decide
def polyLift4_2 (b : Fin 3) : PolyHom 4 2 :=
  ![PolyHom.zero 4 2,PolyHom.zero 4 2,PolyHom.zero 4 2] b
theorem polyLiftFree4_2 : ∀ b : Fin 3, (polyLift4_2 b).freeBlock=basisInt (homKind 4 2) b := by decide
def polyRep4_3_0 : PolyHom 4 3 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_3 (b : Fin 3) : PolyHom 4 3 :=
  ![polyRep4_3_0,PolyHom.zero 4 3,PolyHom.zero 4 3] b
theorem polyLiftFree4_3 : ∀ b : Fin 3, (polyLift4_3 b).freeBlock=basisInt (homKind 4 3) b := by decide
def polyRep4_4_0 : PolyHom 4 4 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_4 (b : Fin 3) : PolyHom 4 4 :=
  ![polyRep4_4_0,PolyHom.zero 4 4,PolyHom.zero 4 4] b
theorem polyLiftFree4_4 : ∀ b : Fin 3, (polyLift4_4 b).freeBlock=basisInt (homKind 4 4) b := by decide
def polyLift4_5 (b : Fin 3) : PolyHom 4 5 :=
  ![PolyHom.zero 4 5,PolyHom.zero 4 5,PolyHom.zero 4 5] b
theorem polyLiftFree4_5 : ∀ b : Fin 3, (polyLift4_5 b).freeBlock=basisInt (homKind 4 5) b := by decide
def polyRep4_6_0 : PolyHom 4 6 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_6 (b : Fin 3) : PolyHom 4 6 :=
  ![polyRep4_6_0,PolyHom.zero 4 6,PolyHom.zero 4 6] b
theorem polyLiftFree4_6 : ∀ b : Fin 3, (polyLift4_6 b).freeBlock=basisInt (homKind 4 6) b := by decide
def polyRep4_7_0 : PolyHom 4 7 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_7 (b : Fin 3) : PolyHom 4 7 :=
  ![polyRep4_7_0,PolyHom.zero 4 7,PolyHom.zero 4 7] b
theorem polyLiftFree4_7 : ∀ b : Fin 3, (polyLift4_7 b).freeBlock=basisInt (homKind 4 7) b := by decide
def polyRep4_8_0 : PolyHom 4 8 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_8 (b : Fin 3) : PolyHom 4 8 :=
  ![polyRep4_8_0,PolyHom.zero 4 8,PolyHom.zero 4 8] b
theorem polyLiftFree4_8 : ∀ b : Fin 3, (polyLift4_8 b).freeBlock=basisInt (homKind 4 8) b := by decide
def polyLift4_9 (b : Fin 3) : PolyHom 4 9 :=
  ![PolyHom.zero 4 9,PolyHom.zero 4 9,PolyHom.zero 4 9] b
theorem polyLiftFree4_9 : ∀ b : Fin 3, (polyLift4_9 b).freeBlock=basisInt (homKind 4 9) b := by decide
def polyRep4_10_0 : PolyHom 4 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_10 (b : Fin 3) : PolyHom 4 10 :=
  ![polyRep4_10_0,PolyHom.zero 4 10,PolyHom.zero 4 10] b
theorem polyLiftFree4_10 : ∀ b : Fin 3, (polyLift4_10 b).freeBlock=basisInt (homKind 4 10) b := by decide
def polyRep4_11_0 : PolyHom 4 11 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_11 (b : Fin 3) : PolyHom 4 11 :=
  ![polyRep4_11_0,PolyHom.zero 4 11,PolyHom.zero 4 11] b
theorem polyLiftFree4_11 : ∀ b : Fin 3, (polyLift4_11 b).freeBlock=basisInt (homKind 4 11) b := by decide
def polyRep4_12_0 : PolyHom 4 12 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_12 (b : Fin 3) : PolyHom 4 12 :=
  ![polyRep4_12_0,PolyHom.zero 4 12,PolyHom.zero 4 12] b
theorem polyLiftFree4_12 : ∀ b : Fin 3, (polyLift4_12 b).freeBlock=basisInt (homKind 4 12) b := by decide
def polyRep4_13_0 : PolyHom 4 13 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_13 (b : Fin 3) : PolyHom 4 13 :=
  ![polyRep4_13_0,PolyHom.zero 4 13,PolyHom.zero 4 13] b
theorem polyLiftFree4_13 : ∀ b : Fin 3, (polyLift4_13 b).freeBlock=basisInt (homKind 4 13) b := by decide
def polyLift4_14 (b : Fin 3) : PolyHom 4 14 :=
  ![PolyHom.zero 4 14,PolyHom.zero 4 14,PolyHom.zero 4 14] b
theorem polyLiftFree4_14 : ∀ b : Fin 3, (polyLift4_14 b).freeBlock=basisInt (homKind 4 14) b := by decide
def polyLift4_15 (b : Fin 3) : PolyHom 4 15 :=
  ![PolyHom.zero 4 15,PolyHom.zero 4 15,PolyHom.zero 4 15] b
theorem polyLiftFree4_15 : ∀ b : Fin 3, (polyLift4_15 b).freeBlock=basisInt (homKind 4 15) b := by decide
def polyRep4_16_0 : PolyHom 4 16 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_16 (b : Fin 3) : PolyHom 4 16 :=
  ![polyRep4_16_0,PolyHom.zero 4 16,PolyHom.zero 4 16] b
theorem polyLiftFree4_16 : ∀ b : Fin 3, (polyLift4_16 b).freeBlock=basisInt (homKind 4 16) b := by decide
def polyLift4_17 (b : Fin 3) : PolyHom 4 17 :=
  ![PolyHom.zero 4 17,PolyHom.zero 4 17,PolyHom.zero 4 17] b
theorem polyLiftFree4_17 : ∀ b : Fin 3, (polyLift4_17 b).freeBlock=basisInt (homKind 4 17) b := by decide
def polyRep4_18_0 : PolyHom 4 18 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_18 (b : Fin 3) : PolyHom 4 18 :=
  ![polyRep4_18_0,PolyHom.zero 4 18,PolyHom.zero 4 18] b
theorem polyLiftFree4_18 : ∀ b : Fin 3, (polyLift4_18 b).freeBlock=basisInt (homKind 4 18) b := by decide
def polyRep4_19_0 : PolyHom 4 19 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_19 (b : Fin 3) : PolyHom 4 19 :=
  ![polyRep4_19_0,PolyHom.zero 4 19,PolyHom.zero 4 19] b
theorem polyLiftFree4_19 : ∀ b : Fin 3, (polyLift4_19 b).freeBlock=basisInt (homKind 4 19) b := by decide
def polyRep4_20_0 : PolyHom 4 20 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_20 (b : Fin 3) : PolyHom 4 20 :=
  ![polyRep4_20_0,PolyHom.zero 4 20,PolyHom.zero 4 20] b
theorem polyLiftFree4_20 : ∀ b : Fin 3, (polyLift4_20 b).freeBlock=basisInt (homKind 4 20) b := by decide
def polyRep4_21_0 : PolyHom 4 21 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_21 (b : Fin 3) : PolyHom 4 21 :=
  ![polyRep4_21_0,PolyHom.zero 4 21,PolyHom.zero 4 21] b
theorem polyLiftFree4_21 : ∀ b : Fin 3, (polyLift4_21 b).freeBlock=basisInt (homKind 4 21) b := by decide
def polyRep4_22_0 : PolyHom 4 22 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_22 (b : Fin 3) : PolyHom 4 22 :=
  ![polyRep4_22_0,PolyHom.zero 4 22,PolyHom.zero 4 22] b
theorem polyLiftFree4_22 : ∀ b : Fin 3, (polyLift4_22 b).freeBlock=basisInt (homKind 4 22) b := by decide
def polyLift4_23 (b : Fin 3) : PolyHom 4 23 :=
  ![PolyHom.zero 4 23,PolyHom.zero 4 23,PolyHom.zero 4 23] b
theorem polyLiftFree4_23 : ∀ b : Fin 3, (polyLift4_23 b).freeBlock=basisInt (homKind 4 23) b := by decide
def polyRep4_24_0 : PolyHom 4 24 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_24 (b : Fin 3) : PolyHom 4 24 :=
  ![polyRep4_24_0,PolyHom.zero 4 24,PolyHom.zero 4 24] b
theorem polyLiftFree4_24 : ∀ b : Fin 3, (polyLift4_24 b).freeBlock=basisInt (homKind 4 24) b := by decide
def polyRep4_25_0 : PolyHom 4 25 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_25 (b : Fin 3) : PolyHom 4 25 :=
  ![polyRep4_25_0,PolyHom.zero 4 25,PolyHom.zero 4 25] b
theorem polyLiftFree4_25 : ∀ b : Fin 3, (polyLift4_25 b).freeBlock=basisInt (homKind 4 25) b := by decide
def polyRep4_26_0 : PolyHom 4 26 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_26 (b : Fin 3) : PolyHom 4 26 :=
  ![polyRep4_26_0,PolyHom.zero 4 26,PolyHom.zero 4 26] b
theorem polyLiftFree4_26 : ∀ b : Fin 3, (polyLift4_26 b).freeBlock=basisInt (homKind 4 26) b := by decide
def polyRep4_27_0 : PolyHom 4 27 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_27 (b : Fin 3) : PolyHom 4 27 :=
  ![polyRep4_27_0,PolyHom.zero 4 27,PolyHom.zero 4 27] b
theorem polyLiftFree4_27 : ∀ b : Fin 3, (polyLift4_27 b).freeBlock=basisInt (homKind 4 27) b := by decide
def polyRep4_28_0 : PolyHom 4 28 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_28 (b : Fin 3) : PolyHom 4 28 :=
  ![polyRep4_28_0,PolyHom.zero 4 28,PolyHom.zero 4 28] b
theorem polyLiftFree4_28 : ∀ b : Fin 3, (polyLift4_28 b).freeBlock=basisInt (homKind 4 28) b := by decide
def polyRep4_29_0 : PolyHom 4 29 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_29 (b : Fin 3) : PolyHom 4 29 :=
  ![polyRep4_29_0,PolyHom.zero 4 29,PolyHom.zero 4 29] b
theorem polyLiftFree4_29 : ∀ b : Fin 3, (polyLift4_29 b).freeBlock=basisInt (homKind 4 29) b := by decide
def polyRep4_30_0 : PolyHom 4 30 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep4_30_1 : PolyHom 4 30 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_30 (b : Fin 3) : PolyHom 4 30 :=
  ![polyRep4_30_0,polyRep4_30_1,PolyHom.zero 4 30] b
theorem polyLiftFree4_30 : ∀ b : Fin 3, (polyLift4_30 b).freeBlock=basisInt (homKind 4 30) b := by decide
def polyRep4_31_0 : PolyHom 4 31 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_31 (b : Fin 3) : PolyHom 4 31 :=
  ![polyRep4_31_0,PolyHom.zero 4 31,PolyHom.zero 4 31] b
theorem polyLiftFree4_31 : ∀ b : Fin 3, (polyLift4_31 b).freeBlock=basisInt (homKind 4 31) b := by decide
def polyRep4_32_0 : PolyHom 4 32 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_32 (b : Fin 3) : PolyHom 4 32 :=
  ![polyRep4_32_0,PolyHom.zero 4 32,PolyHom.zero 4 32] b
theorem polyLiftFree4_32 : ∀ b : Fin 3, (polyLift4_32 b).freeBlock=basisInt (homKind 4 32) b := by decide
def polyRep4_33_0 : PolyHom 4 33 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_33 (b : Fin 3) : PolyHom 4 33 :=
  ![polyRep4_33_0,PolyHom.zero 4 33,PolyHom.zero 4 33] b
theorem polyLiftFree4_33 : ∀ b : Fin 3, (polyLift4_33 b).freeBlock=basisInt (homKind 4 33) b := by decide
def polyRep4_34_0 : PolyHom 4 34 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_34 (b : Fin 3) : PolyHom 4 34 :=
  ![polyRep4_34_0,PolyHom.zero 4 34,PolyHom.zero 4 34] b
theorem polyLiftFree4_34 : ∀ b : Fin 3, (polyLift4_34 b).freeBlock=basisInt (homKind 4 34) b := by decide
def polyRep4_35_0 : PolyHom 4 35 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_35 (b : Fin 3) : PolyHom 4 35 :=
  ![polyRep4_35_0,PolyHom.zero 4 35,PolyHom.zero 4 35] b
theorem polyLiftFree4_35 : ∀ b : Fin 3, (polyLift4_35 b).freeBlock=basisInt (homKind 4 35) b := by decide
def polyRep4_36_0 : PolyHom 4 36 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_36 (b : Fin 3) : PolyHom 4 36 :=
  ![polyRep4_36_0,PolyHom.zero 4 36,PolyHom.zero 4 36] b
theorem polyLiftFree4_36 : ∀ b : Fin 3, (polyLift4_36 b).freeBlock=basisInt (homKind 4 36) b := by decide
def polyRep4_37_0 : PolyHom 4 37 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_37 (b : Fin 3) : PolyHom 4 37 :=
  ![polyRep4_37_0,PolyHom.zero 4 37,PolyHom.zero 4 37] b
theorem polyLiftFree4_37 : ∀ b : Fin 3, (polyLift4_37 b).freeBlock=basisInt (homKind 4 37) b := by decide
def polyRep4_38_0 : PolyHom 4 38 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_38 (b : Fin 3) : PolyHom 4 38 :=
  ![polyRep4_38_0,PolyHom.zero 4 38,PolyHom.zero 4 38] b
theorem polyLiftFree4_38 : ∀ b : Fin 3, (polyLift4_38 b).freeBlock=basisInt (homKind 4 38) b := by decide
def polyRep4_39_0 : PolyHom 4 39 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_39 (b : Fin 3) : PolyHom 4 39 :=
  ![polyRep4_39_0,PolyHom.zero 4 39,PolyHom.zero 4 39] b
theorem polyLiftFree4_39 : ∀ b : Fin 3, (polyLift4_39 b).freeBlock=basisInt (homKind 4 39) b := by decide
def polyRep4_40_0 : PolyHom 4 40 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep4_40_1 : PolyHom 4 40 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_40 (b : Fin 3) : PolyHom 4 40 :=
  ![polyRep4_40_0,polyRep4_40_1,PolyHom.zero 4 40] b
theorem polyLiftFree4_40 : ∀ b : Fin 3, (polyLift4_40 b).freeBlock=basisInt (homKind 4 40) b := by decide
def polyRep4_41_0 : PolyHom 4 41 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_41 (b : Fin 3) : PolyHom 4 41 :=
  ![polyRep4_41_0,PolyHom.zero 4 41,PolyHom.zero 4 41] b
theorem polyLiftFree4_41 : ∀ b : Fin 3, (polyLift4_41 b).freeBlock=basisInt (homKind 4 41) b := by decide
def polyRep4_42_0 : PolyHom 4 42 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep4_42_1 : PolyHom 4 42 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_42 (b : Fin 3) : PolyHom 4 42 :=
  ![polyRep4_42_0,polyRep4_42_1,PolyHom.zero 4 42] b
theorem polyLiftFree4_42 : ∀ b : Fin 3, (polyLift4_42 b).freeBlock=basisInt (homKind 4 42) b := by decide
def polyRep4_43_0 : PolyHom 4 43 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep4_43_1 : PolyHom 4 43 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_43 (b : Fin 3) : PolyHom 4 43 :=
  ![polyRep4_43_0,polyRep4_43_1,PolyHom.zero 4 43] b
theorem polyLiftFree4_43 : ∀ b : Fin 3, (polyLift4_43 b).freeBlock=basisInt (homKind 4 43) b := by decide
def polyRep4_44_0 : PolyHom 4 44 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep4_44_1 : PolyHom 4 44 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_44 (b : Fin 3) : PolyHom 4 44 :=
  ![polyRep4_44_0,polyRep4_44_1,PolyHom.zero 4 44] b
theorem polyLiftFree4_44 : ∀ b : Fin 3, (polyLift4_44 b).freeBlock=basisInt (homKind 4 44) b := by decide
def polyRep4_45_0 : PolyHom 4 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift4_45 (b : Fin 3) : PolyHom 4 45 :=
  ![polyRep4_45_0,PolyHom.zero 4 45,PolyHom.zero 4 45] b
theorem polyLiftFree4_45 : ∀ b : Fin 3, (polyLift4_45 b).freeBlock=basisInt (homKind 4 45) b := by decide
def polyLift4_46 (b : Fin 3) : PolyHom 4 46 :=
  ![PolyHom.zero 4 46,PolyHom.zero 4 46,PolyHom.zero 4 46] b
theorem polyLiftFree4_46 : ∀ b : Fin 3, (polyLift4_46 b).freeBlock=basisInt (homKind 4 46) b := by decide
def polyLiftRow4 (j : Fin 47) (b : Fin 3) : PolyHom 4 j :=
  match j with
  | ⟨0,_⟩ => polyLift4_0 b
  | ⟨1,_⟩ => polyLift4_1 b
  | ⟨2,_⟩ => polyLift4_2 b
  | ⟨3,_⟩ => polyLift4_3 b
  | ⟨4,_⟩ => polyLift4_4 b
  | ⟨5,_⟩ => polyLift4_5 b
  | ⟨6,_⟩ => polyLift4_6 b
  | ⟨7,_⟩ => polyLift4_7 b
  | ⟨8,_⟩ => polyLift4_8 b
  | ⟨9,_⟩ => polyLift4_9 b
  | ⟨10,_⟩ => polyLift4_10 b
  | ⟨11,_⟩ => polyLift4_11 b
  | ⟨12,_⟩ => polyLift4_12 b
  | ⟨13,_⟩ => polyLift4_13 b
  | ⟨14,_⟩ => polyLift4_14 b
  | ⟨15,_⟩ => polyLift4_15 b
  | ⟨16,_⟩ => polyLift4_16 b
  | ⟨17,_⟩ => polyLift4_17 b
  | ⟨18,_⟩ => polyLift4_18 b
  | ⟨19,_⟩ => polyLift4_19 b
  | ⟨20,_⟩ => polyLift4_20 b
  | ⟨21,_⟩ => polyLift4_21 b
  | ⟨22,_⟩ => polyLift4_22 b
  | ⟨23,_⟩ => polyLift4_23 b
  | ⟨24,_⟩ => polyLift4_24 b
  | ⟨25,_⟩ => polyLift4_25 b
  | ⟨26,_⟩ => polyLift4_26 b
  | ⟨27,_⟩ => polyLift4_27 b
  | ⟨28,_⟩ => polyLift4_28 b
  | ⟨29,_⟩ => polyLift4_29 b
  | ⟨30,_⟩ => polyLift4_30 b
  | ⟨31,_⟩ => polyLift4_31 b
  | ⟨32,_⟩ => polyLift4_32 b
  | ⟨33,_⟩ => polyLift4_33 b
  | ⟨34,_⟩ => polyLift4_34 b
  | ⟨35,_⟩ => polyLift4_35 b
  | ⟨36,_⟩ => polyLift4_36 b
  | ⟨37,_⟩ => polyLift4_37 b
  | ⟨38,_⟩ => polyLift4_38 b
  | ⟨39,_⟩ => polyLift4_39 b
  | ⟨40,_⟩ => polyLift4_40 b
  | ⟨41,_⟩ => polyLift4_41 b
  | ⟨42,_⟩ => polyLift4_42 b
  | ⟨43,_⟩ => polyLift4_43 b
  | ⟨44,_⟩ => polyLift4_44 b
  | ⟨45,_⟩ => polyLift4_45 b
  | ⟨46,_⟩ => polyLift4_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree4 (j : Fin 47) (b : Fin 3) : (polyLiftRow4 j b).freeBlock=basisInt (homKind 4 j) b := by
  fin_cases j
  · exact polyLiftFree4_0 b
  · exact polyLiftFree4_1 b
  · exact polyLiftFree4_2 b
  · exact polyLiftFree4_3 b
  · exact polyLiftFree4_4 b
  · exact polyLiftFree4_5 b
  · exact polyLiftFree4_6 b
  · exact polyLiftFree4_7 b
  · exact polyLiftFree4_8 b
  · exact polyLiftFree4_9 b
  · exact polyLiftFree4_10 b
  · exact polyLiftFree4_11 b
  · exact polyLiftFree4_12 b
  · exact polyLiftFree4_13 b
  · exact polyLiftFree4_14 b
  · exact polyLiftFree4_15 b
  · exact polyLiftFree4_16 b
  · exact polyLiftFree4_17 b
  · exact polyLiftFree4_18 b
  · exact polyLiftFree4_19 b
  · exact polyLiftFree4_20 b
  · exact polyLiftFree4_21 b
  · exact polyLiftFree4_22 b
  · exact polyLiftFree4_23 b
  · exact polyLiftFree4_24 b
  · exact polyLiftFree4_25 b
  · exact polyLiftFree4_26 b
  · exact polyLiftFree4_27 b
  · exact polyLiftFree4_28 b
  · exact polyLiftFree4_29 b
  · exact polyLiftFree4_30 b
  · exact polyLiftFree4_31 b
  · exact polyLiftFree4_32 b
  · exact polyLiftFree4_33 b
  · exact polyLiftFree4_34 b
  · exact polyLiftFree4_35 b
  · exact polyLiftFree4_36 b
  · exact polyLiftFree4_37 b
  · exact polyLiftFree4_38 b
  · exact polyLiftFree4_39 b
  · exact polyLiftFree4_40 b
  · exact polyLiftFree4_41 b
  · exact polyLiftFree4_42 b
  · exact polyLiftFree4_43 b
  · exact polyLiftFree4_44 b
  · exact polyLiftFree4_45 b
  · exact polyLiftFree4_46 b
end UniserialComputations.N6
