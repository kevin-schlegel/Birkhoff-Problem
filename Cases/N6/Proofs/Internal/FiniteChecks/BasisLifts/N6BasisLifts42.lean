import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift42_0 (b : Fin 3) : PolyHom 42 0 :=
  ![PolyHom.zero 42 0,PolyHom.zero 42 0,PolyHom.zero 42 0] b
theorem polyLiftFree42_0 : ∀ b : Fin 3, (polyLift42_0 b).freeBlock=basisInt (homKind 42 0) b := by decide
def polyLift42_1 (b : Fin 3) : PolyHom 42 1 :=
  ![PolyHom.zero 42 1,PolyHom.zero 42 1,PolyHom.zero 42 1] b
theorem polyLiftFree42_1 : ∀ b : Fin 3, (polyLift42_1 b).freeBlock=basisInt (homKind 42 1) b := by decide
def polyLift42_2 (b : Fin 3) : PolyHom 42 2 :=
  ![PolyHom.zero 42 2,PolyHom.zero 42 2,PolyHom.zero 42 2] b
theorem polyLiftFree42_2 : ∀ b : Fin 3, (polyLift42_2 b).freeBlock=basisInt (homKind 42 2) b := by decide
def polyLift42_3 (b : Fin 3) : PolyHom 42 3 :=
  ![PolyHom.zero 42 3,PolyHom.zero 42 3,PolyHom.zero 42 3] b
theorem polyLiftFree42_3 : ∀ b : Fin 3, (polyLift42_3 b).freeBlock=basisInt (homKind 42 3) b := by decide
def polyLift42_4 (b : Fin 3) : PolyHom 42 4 :=
  ![PolyHom.zero 42 4,PolyHom.zero 42 4,PolyHom.zero 42 4] b
theorem polyLiftFree42_4 : ∀ b : Fin 3, (polyLift42_4 b).freeBlock=basisInt (homKind 42 4) b := by decide
def polyLift42_5 (b : Fin 3) : PolyHom 42 5 :=
  ![PolyHom.zero 42 5,PolyHom.zero 42 5,PolyHom.zero 42 5] b
theorem polyLiftFree42_5 : ∀ b : Fin 3, (polyLift42_5 b).freeBlock=basisInt (homKind 42 5) b := by decide
def polyRep42_6_0 : PolyHom 42 6 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_6 (b : Fin 3) : PolyHom 42 6 :=
  ![polyRep42_6_0,PolyHom.zero 42 6,PolyHom.zero 42 6] b
theorem polyLiftFree42_6 : ∀ b : Fin 3, (polyLift42_6 b).freeBlock=basisInt (homKind 42 6) b := by decide
def polyRep42_7_0 : PolyHom 42 7 where
  M := !![(mono6 (1) 2),0,0,0;(mono6 (-1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_7 (b : Fin 3) : PolyHom 42 7 :=
  ![polyRep42_7_0,PolyHom.zero 42 7,PolyHom.zero 42 7] b
theorem polyLiftFree42_7 : ∀ b : Fin 3, (polyLift42_7 b).freeBlock=basisInt (homKind 42 7) b := by decide
def polyRep42_8_0 : PolyHom 42 8 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_8 (b : Fin 3) : PolyHom 42 8 :=
  ![polyRep42_8_0,PolyHom.zero 42 8,PolyHom.zero 42 8] b
theorem polyLiftFree42_8 : ∀ b : Fin 3, (polyLift42_8 b).freeBlock=basisInt (homKind 42 8) b := by decide
def polyLift42_9 (b : Fin 3) : PolyHom 42 9 :=
  ![PolyHom.zero 42 9,PolyHom.zero 42 9,PolyHom.zero 42 9] b
theorem polyLiftFree42_9 : ∀ b : Fin 3, (polyLift42_9 b).freeBlock=basisInt (homKind 42 9) b := by decide
def polyRep42_10_0 : PolyHom 42 10 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep42_10_1 : PolyHom 42 10 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_10 (b : Fin 3) : PolyHom 42 10 :=
  ![polyRep42_10_0,polyRep42_10_1,PolyHom.zero 42 10] b
theorem polyLiftFree42_10 : ∀ b : Fin 3, (polyLift42_10 b).freeBlock=basisInt (homKind 42 10) b := by decide
def polyRep42_11_0 : PolyHom 42 11 where
  M := !![0,0,0,0;(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep42_11_1 : PolyHom 42 11 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_11 (b : Fin 3) : PolyHom 42 11 :=
  ![polyRep42_11_0,polyRep42_11_1,PolyHom.zero 42 11] b
theorem polyLiftFree42_11 : ∀ b : Fin 3, (polyLift42_11 b).freeBlock=basisInt (homKind 42 11) b := by decide
def polyRep42_12_0 : PolyHom 42 12 where
  M := !![(mono6 (1) 2),0,0,0;(mono6 (-1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_12 (b : Fin 3) : PolyHom 42 12 :=
  ![polyRep42_12_0,PolyHom.zero 42 12,PolyHom.zero 42 12] b
theorem polyLiftFree42_12 : ∀ b : Fin 3, (polyLift42_12 b).freeBlock=basisInt (homKind 42 12) b := by decide
def polyRep42_13_0 : PolyHom 42 13 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_13 (b : Fin 3) : PolyHom 42 13 :=
  ![polyRep42_13_0,PolyHom.zero 42 13,PolyHom.zero 42 13] b
theorem polyLiftFree42_13 : ∀ b : Fin 3, (polyLift42_13 b).freeBlock=basisInt (homKind 42 13) b := by decide
def polyLift42_14 (b : Fin 3) : PolyHom 42 14 :=
  ![PolyHom.zero 42 14,PolyHom.zero 42 14,PolyHom.zero 42 14] b
theorem polyLiftFree42_14 : ∀ b : Fin 3, (polyLift42_14 b).freeBlock=basisInt (homKind 42 14) b := by decide
def polyLift42_15 (b : Fin 3) : PolyHom 42 15 :=
  ![PolyHom.zero 42 15,PolyHom.zero 42 15,PolyHom.zero 42 15] b
theorem polyLiftFree42_15 : ∀ b : Fin 3, (polyLift42_15 b).freeBlock=basisInt (homKind 42 15) b := by decide
def polyRep42_16_0 : PolyHom 42 16 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_16 (b : Fin 3) : PolyHom 42 16 :=
  ![polyRep42_16_0,PolyHom.zero 42 16,PolyHom.zero 42 16] b
theorem polyLiftFree42_16 : ∀ b : Fin 3, (polyLift42_16 b).freeBlock=basisInt (homKind 42 16) b := by decide
def polyLift42_17 (b : Fin 3) : PolyHom 42 17 :=
  ![PolyHom.zero 42 17,PolyHom.zero 42 17,PolyHom.zero 42 17] b
theorem polyLiftFree42_17 : ∀ b : Fin 3, (polyLift42_17 b).freeBlock=basisInt (homKind 42 17) b := by decide
def polyRep42_18_0 : PolyHom 42 18 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_18 (b : Fin 3) : PolyHom 42 18 :=
  ![polyRep42_18_0,PolyHom.zero 42 18,PolyHom.zero 42 18] b
theorem polyLiftFree42_18 : ∀ b : Fin 3, (polyLift42_18 b).freeBlock=basisInt (homKind 42 18) b := by decide
def polyRep42_19_0 : PolyHom 42 19 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_19 (b : Fin 3) : PolyHom 42 19 :=
  ![polyRep42_19_0,PolyHom.zero 42 19,PolyHom.zero 42 19] b
theorem polyLiftFree42_19 : ∀ b : Fin 3, (polyLift42_19 b).freeBlock=basisInt (homKind 42 19) b := by decide
def polyLift42_20 (b : Fin 3) : PolyHom 42 20 :=
  ![PolyHom.zero 42 20,PolyHom.zero 42 20,PolyHom.zero 42 20] b
theorem polyLiftFree42_20 : ∀ b : Fin 3, (polyLift42_20 b).freeBlock=basisInt (homKind 42 20) b := by decide
def polyRep42_21_0 : PolyHom 42 21 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep42_21_1 : PolyHom 42 21 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_21 (b : Fin 3) : PolyHom 42 21 :=
  ![polyRep42_21_0,polyRep42_21_1,PolyHom.zero 42 21] b
theorem polyLiftFree42_21 : ∀ b : Fin 3, (polyLift42_21 b).freeBlock=basisInt (homKind 42 21) b := by decide
def polyRep42_22_0 : PolyHom 42 22 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_22 (b : Fin 3) : PolyHom 42 22 :=
  ![polyRep42_22_0,PolyHom.zero 42 22,PolyHom.zero 42 22] b
theorem polyLiftFree42_22 : ∀ b : Fin 3, (polyLift42_22 b).freeBlock=basisInt (homKind 42 22) b := by decide
def polyLift42_23 (b : Fin 3) : PolyHom 42 23 :=
  ![PolyHom.zero 42 23,PolyHom.zero 42 23,PolyHom.zero 42 23] b
theorem polyLiftFree42_23 : ∀ b : Fin 3, (polyLift42_23 b).freeBlock=basisInt (homKind 42 23) b := by decide
def polyRep42_24_0 : PolyHom 42 24 where
  M := !![0,0,(mono6 (1) 0),0;(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (-1) 1),0]
  U := !![(mono6 (1) 0),0;0,(mono6 (-1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep42_24_1 : PolyHom 42 24 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_24 (b : Fin 3) : PolyHom 42 24 :=
  ![polyRep42_24_0,polyRep42_24_1,PolyHom.zero 42 24] b
theorem polyLiftFree42_24 : ∀ b : Fin 3, (polyLift42_24 b).freeBlock=basisInt (homKind 42 24) b := by decide
def polyRep42_25_0 : PolyHom 42 25 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_25 (b : Fin 3) : PolyHom 42 25 :=
  ![polyRep42_25_0,PolyHom.zero 42 25,PolyHom.zero 42 25] b
theorem polyLiftFree42_25 : ∀ b : Fin 3, (polyLift42_25 b).freeBlock=basisInt (homKind 42 25) b := by decide
def polyRep42_26_0 : PolyHom 42 26 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_26 (b : Fin 3) : PolyHom 42 26 :=
  ![polyRep42_26_0,PolyHom.zero 42 26,PolyHom.zero 42 26] b
theorem polyLiftFree42_26 : ∀ b : Fin 3, (polyLift42_26 b).freeBlock=basisInt (homKind 42 26) b := by decide
def polyRep42_27_0 : PolyHom 42 27 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_27 (b : Fin 3) : PolyHom 42 27 :=
  ![polyRep42_27_0,PolyHom.zero 42 27,PolyHom.zero 42 27] b
theorem polyLiftFree42_27 : ∀ b : Fin 3, (polyLift42_27 b).freeBlock=basisInt (homKind 42 27) b := by decide
def polyRep42_28_0 : PolyHom 42 28 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_28 (b : Fin 3) : PolyHom 42 28 :=
  ![polyRep42_28_0,PolyHom.zero 42 28,PolyHom.zero 42 28] b
theorem polyLiftFree42_28 : ∀ b : Fin 3, (polyLift42_28 b).freeBlock=basisInt (homKind 42 28) b := by decide
def polyLift42_29 (b : Fin 3) : PolyHom 42 29 :=
  ![PolyHom.zero 42 29,PolyHom.zero 42 29,PolyHom.zero 42 29] b
theorem polyLiftFree42_29 : ∀ b : Fin 3, (polyLift42_29 b).freeBlock=basisInt (homKind 42 29) b := by decide
def polyRep42_30_0 : PolyHom 42 30 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_30 (b : Fin 3) : PolyHom 42 30 :=
  ![polyRep42_30_0,PolyHom.zero 42 30,PolyHom.zero 42 30] b
theorem polyLiftFree42_30 : ∀ b : Fin 3, (polyLift42_30 b).freeBlock=basisInt (homKind 42 30) b := by decide
def polyRep42_31_0 : PolyHom 42 31 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_31 (b : Fin 3) : PolyHom 42 31 :=
  ![polyRep42_31_0,PolyHom.zero 42 31,PolyHom.zero 42 31] b
theorem polyLiftFree42_31 : ∀ b : Fin 3, (polyLift42_31 b).freeBlock=basisInt (homKind 42 31) b := by decide
def polyRep42_32_0 : PolyHom 42 32 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,(mono6 (1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_32 (b : Fin 3) : PolyHom 42 32 :=
  ![polyRep42_32_0,PolyHom.zero 42 32,PolyHom.zero 42 32] b
theorem polyLiftFree42_32 : ∀ b : Fin 3, (polyLift42_32 b).freeBlock=basisInt (homKind 42 32) b := by decide
def polyRep42_33_0 : PolyHom 42 33 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_33 (b : Fin 3) : PolyHom 42 33 :=
  ![polyRep42_33_0,PolyHom.zero 42 33,PolyHom.zero 42 33] b
theorem polyLiftFree42_33 : ∀ b : Fin 3, (polyLift42_33 b).freeBlock=basisInt (homKind 42 33) b := by decide
def polyRep42_34_0 : PolyHom 42 34 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_34 (b : Fin 3) : PolyHom 42 34 :=
  ![polyRep42_34_0,PolyHom.zero 42 34,PolyHom.zero 42 34] b
theorem polyLiftFree42_34 : ∀ b : Fin 3, (polyLift42_34 b).freeBlock=basisInt (homKind 42 34) b := by decide
def polyRep42_35_0 : PolyHom 42 35 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_35 (b : Fin 3) : PolyHom 42 35 :=
  ![polyRep42_35_0,PolyHom.zero 42 35,PolyHom.zero 42 35] b
theorem polyLiftFree42_35 : ∀ b : Fin 3, (polyLift42_35 b).freeBlock=basisInt (homKind 42 35) b := by decide
def polyRep42_36_0 : PolyHom 42 36 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_36 (b : Fin 3) : PolyHom 42 36 :=
  ![polyRep42_36_0,PolyHom.zero 42 36,PolyHom.zero 42 36] b
theorem polyLiftFree42_36 : ∀ b : Fin 3, (polyLift42_36 b).freeBlock=basisInt (homKind 42 36) b := by decide
def polyRep42_37_0 : PolyHom 42 37 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_37 (b : Fin 3) : PolyHom 42 37 :=
  ![polyRep42_37_0,PolyHom.zero 42 37,PolyHom.zero 42 37] b
theorem polyLiftFree42_37 : ∀ b : Fin 3, (polyLift42_37 b).freeBlock=basisInt (homKind 42 37) b := by decide
def polyRep42_38_0 : PolyHom 42 38 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1)]
  U := !![0,0;(mono6 (1) 1),(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_38 (b : Fin 3) : PolyHom 42 38 :=
  ![polyRep42_38_0,PolyHom.zero 42 38,PolyHom.zero 42 38] b
theorem polyLiftFree42_38 : ∀ b : Fin 3, (polyLift42_38 b).freeBlock=basisInt (homKind 42 38) b := by decide
def polyRep42_39_0 : PolyHom 42 39 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,(mono6 (1) 0),0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_39 (b : Fin 3) : PolyHom 42 39 :=
  ![polyRep42_39_0,PolyHom.zero 42 39,PolyHom.zero 42 39] b
theorem polyLiftFree42_39 : ∀ b : Fin 3, (polyLift42_39 b).freeBlock=basisInt (homKind 42 39) b := by decide
def polyRep42_40_0 : PolyHom 42 40 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_40 (b : Fin 3) : PolyHom 42 40 :=
  ![polyRep42_40_0,PolyHom.zero 42 40,PolyHom.zero 42 40] b
theorem polyLiftFree42_40 : ∀ b : Fin 3, (polyLift42_40 b).freeBlock=basisInt (homKind 42 40) b := by decide
def polyRep42_41_0 : PolyHom 42 41 where
  M := !![(mono6 (1) 0),0,0,(mono6 (1) 0);0,0,0,0;0,0,(mono6 (1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_41 (b : Fin 3) : PolyHom 42 41 :=
  ![polyRep42_41_0,PolyHom.zero 42 41,PolyHom.zero 42 41] b
theorem polyLiftFree42_41 : ∀ b : Fin 3, (polyLift42_41 b).freeBlock=basisInt (homKind 42 41) b := by decide
def polyRep42_42_0 : PolyHom 42 42 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,(mono6 (1) 0)]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep42_42_1 : PolyHom 42 42 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_42 (b : Fin 3) : PolyHom 42 42 :=
  ![polyRep42_42_0,polyRep42_42_1,PolyHom.zero 42 42] b
theorem polyLiftFree42_42 : ∀ b : Fin 3, (polyLift42_42 b).freeBlock=basisInt (homKind 42 42) b := by decide
def polyRep42_43_0 : PolyHom 42 43 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep42_43_1 : PolyHom 42 43 where
  M := !![0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,(mono6 (1) 0)]
  U := !![0,0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_43 (b : Fin 3) : PolyHom 42 43 :=
  ![polyRep42_43_0,polyRep42_43_1,PolyHom.zero 42 43] b
theorem polyLiftFree42_43 : ∀ b : Fin 3, (polyLift42_43 b).freeBlock=basisInt (homKind 42 43) b := by decide
def polyRep42_44_0 : PolyHom 42 44 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,(mono6 (1) 0)]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep42_44_1 : PolyHom 42 44 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_44 (b : Fin 3) : PolyHom 42 44 :=
  ![polyRep42_44_0,polyRep42_44_1,PolyHom.zero 42 44] b
theorem polyLiftFree42_44 : ∀ b : Fin 3, (polyLift42_44 b).freeBlock=basisInt (homKind 42 44) b := by decide
def polyRep42_45_0 : PolyHom 42 45 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep42_45_1 : PolyHom 42 45 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift42_45 (b : Fin 3) : PolyHom 42 45 :=
  ![polyRep42_45_0,polyRep42_45_1,PolyHom.zero 42 45] b
theorem polyLiftFree42_45 : ∀ b : Fin 3, (polyLift42_45 b).freeBlock=basisInt (homKind 42 45) b := by decide
def polyLift42_46 (b : Fin 3) : PolyHom 42 46 :=
  ![PolyHom.zero 42 46,PolyHom.zero 42 46,PolyHom.zero 42 46] b
theorem polyLiftFree42_46 : ∀ b : Fin 3, (polyLift42_46 b).freeBlock=basisInt (homKind 42 46) b := by decide
def polyLiftRow42 (j : Fin 47) (b : Fin 3) : PolyHom 42 j :=
  match j with
  | ⟨0,_⟩ => polyLift42_0 b
  | ⟨1,_⟩ => polyLift42_1 b
  | ⟨2,_⟩ => polyLift42_2 b
  | ⟨3,_⟩ => polyLift42_3 b
  | ⟨4,_⟩ => polyLift42_4 b
  | ⟨5,_⟩ => polyLift42_5 b
  | ⟨6,_⟩ => polyLift42_6 b
  | ⟨7,_⟩ => polyLift42_7 b
  | ⟨8,_⟩ => polyLift42_8 b
  | ⟨9,_⟩ => polyLift42_9 b
  | ⟨10,_⟩ => polyLift42_10 b
  | ⟨11,_⟩ => polyLift42_11 b
  | ⟨12,_⟩ => polyLift42_12 b
  | ⟨13,_⟩ => polyLift42_13 b
  | ⟨14,_⟩ => polyLift42_14 b
  | ⟨15,_⟩ => polyLift42_15 b
  | ⟨16,_⟩ => polyLift42_16 b
  | ⟨17,_⟩ => polyLift42_17 b
  | ⟨18,_⟩ => polyLift42_18 b
  | ⟨19,_⟩ => polyLift42_19 b
  | ⟨20,_⟩ => polyLift42_20 b
  | ⟨21,_⟩ => polyLift42_21 b
  | ⟨22,_⟩ => polyLift42_22 b
  | ⟨23,_⟩ => polyLift42_23 b
  | ⟨24,_⟩ => polyLift42_24 b
  | ⟨25,_⟩ => polyLift42_25 b
  | ⟨26,_⟩ => polyLift42_26 b
  | ⟨27,_⟩ => polyLift42_27 b
  | ⟨28,_⟩ => polyLift42_28 b
  | ⟨29,_⟩ => polyLift42_29 b
  | ⟨30,_⟩ => polyLift42_30 b
  | ⟨31,_⟩ => polyLift42_31 b
  | ⟨32,_⟩ => polyLift42_32 b
  | ⟨33,_⟩ => polyLift42_33 b
  | ⟨34,_⟩ => polyLift42_34 b
  | ⟨35,_⟩ => polyLift42_35 b
  | ⟨36,_⟩ => polyLift42_36 b
  | ⟨37,_⟩ => polyLift42_37 b
  | ⟨38,_⟩ => polyLift42_38 b
  | ⟨39,_⟩ => polyLift42_39 b
  | ⟨40,_⟩ => polyLift42_40 b
  | ⟨41,_⟩ => polyLift42_41 b
  | ⟨42,_⟩ => polyLift42_42 b
  | ⟨43,_⟩ => polyLift42_43 b
  | ⟨44,_⟩ => polyLift42_44 b
  | ⟨45,_⟩ => polyLift42_45 b
  | ⟨46,_⟩ => polyLift42_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree42 (j : Fin 47) (b : Fin 3) : (polyLiftRow42 j b).freeBlock=basisInt (homKind 42 j) b := by
  fin_cases j
  · exact polyLiftFree42_0 b
  · exact polyLiftFree42_1 b
  · exact polyLiftFree42_2 b
  · exact polyLiftFree42_3 b
  · exact polyLiftFree42_4 b
  · exact polyLiftFree42_5 b
  · exact polyLiftFree42_6 b
  · exact polyLiftFree42_7 b
  · exact polyLiftFree42_8 b
  · exact polyLiftFree42_9 b
  · exact polyLiftFree42_10 b
  · exact polyLiftFree42_11 b
  · exact polyLiftFree42_12 b
  · exact polyLiftFree42_13 b
  · exact polyLiftFree42_14 b
  · exact polyLiftFree42_15 b
  · exact polyLiftFree42_16 b
  · exact polyLiftFree42_17 b
  · exact polyLiftFree42_18 b
  · exact polyLiftFree42_19 b
  · exact polyLiftFree42_20 b
  · exact polyLiftFree42_21 b
  · exact polyLiftFree42_22 b
  · exact polyLiftFree42_23 b
  · exact polyLiftFree42_24 b
  · exact polyLiftFree42_25 b
  · exact polyLiftFree42_26 b
  · exact polyLiftFree42_27 b
  · exact polyLiftFree42_28 b
  · exact polyLiftFree42_29 b
  · exact polyLiftFree42_30 b
  · exact polyLiftFree42_31 b
  · exact polyLiftFree42_32 b
  · exact polyLiftFree42_33 b
  · exact polyLiftFree42_34 b
  · exact polyLiftFree42_35 b
  · exact polyLiftFree42_36 b
  · exact polyLiftFree42_37 b
  · exact polyLiftFree42_38 b
  · exact polyLiftFree42_39 b
  · exact polyLiftFree42_40 b
  · exact polyLiftFree42_41 b
  · exact polyLiftFree42_42 b
  · exact polyLiftFree42_43 b
  · exact polyLiftFree42_44 b
  · exact polyLiftFree42_45 b
  · exact polyLiftFree42_46 b
end UniserialComputations.N6
