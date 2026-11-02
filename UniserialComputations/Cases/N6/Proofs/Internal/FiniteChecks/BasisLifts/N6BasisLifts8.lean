import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift8_0 (b : Fin 3) : PolyHom 8 0 :=
  ![PolyHom.zero 8 0,PolyHom.zero 8 0,PolyHom.zero 8 0] b
theorem polyLiftFree8_0 : ∀ b : Fin 3, (polyLift8_0 b).freeBlock=basisInt (homKind 8 0) b := by decide
def polyLift8_1 (b : Fin 3) : PolyHom 8 1 :=
  ![PolyHom.zero 8 1,PolyHom.zero 8 1,PolyHom.zero 8 1] b
theorem polyLiftFree8_1 : ∀ b : Fin 3, (polyLift8_1 b).freeBlock=basisInt (homKind 8 1) b := by decide
def polyLift8_2 (b : Fin 3) : PolyHom 8 2 :=
  ![PolyHom.zero 8 2,PolyHom.zero 8 2,PolyHom.zero 8 2] b
theorem polyLiftFree8_2 : ∀ b : Fin 3, (polyLift8_2 b).freeBlock=basisInt (homKind 8 2) b := by decide
def polyLift8_3 (b : Fin 3) : PolyHom 8 3 :=
  ![PolyHom.zero 8 3,PolyHom.zero 8 3,PolyHom.zero 8 3] b
theorem polyLiftFree8_3 : ∀ b : Fin 3, (polyLift8_3 b).freeBlock=basisInt (homKind 8 3) b := by decide
def polyLift8_4 (b : Fin 3) : PolyHom 8 4 :=
  ![PolyHom.zero 8 4,PolyHom.zero 8 4,PolyHom.zero 8 4] b
theorem polyLiftFree8_4 : ∀ b : Fin 3, (polyLift8_4 b).freeBlock=basisInt (homKind 8 4) b := by decide
def polyLift8_5 (b : Fin 3) : PolyHom 8 5 :=
  ![PolyHom.zero 8 5,PolyHom.zero 8 5,PolyHom.zero 8 5] b
theorem polyLiftFree8_5 : ∀ b : Fin 3, (polyLift8_5 b).freeBlock=basisInt (homKind 8 5) b := by decide
def polyRep8_6_0 : PolyHom 8 6 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_6 (b : Fin 3) : PolyHom 8 6 :=
  ![polyRep8_6_0,PolyHom.zero 8 6,PolyHom.zero 8 6] b
theorem polyLiftFree8_6 : ∀ b : Fin 3, (polyLift8_6 b).freeBlock=basisInt (homKind 8 6) b := by decide
def polyRep8_7_0 : PolyHom 8 7 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_7 (b : Fin 3) : PolyHom 8 7 :=
  ![polyRep8_7_0,PolyHom.zero 8 7,PolyHom.zero 8 7] b
theorem polyLiftFree8_7 : ∀ b : Fin 3, (polyLift8_7 b).freeBlock=basisInt (homKind 8 7) b := by decide
def polyRep8_8_0 : PolyHom 8 8 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_8 (b : Fin 3) : PolyHom 8 8 :=
  ![polyRep8_8_0,PolyHom.zero 8 8,PolyHom.zero 8 8] b
theorem polyLiftFree8_8 : ∀ b : Fin 3, (polyLift8_8 b).freeBlock=basisInt (homKind 8 8) b := by decide
def polyLift8_9 (b : Fin 3) : PolyHom 8 9 :=
  ![PolyHom.zero 8 9,PolyHom.zero 8 9,PolyHom.zero 8 9] b
theorem polyLiftFree8_9 : ∀ b : Fin 3, (polyLift8_9 b).freeBlock=basisInt (homKind 8 9) b := by decide
def polyRep8_10_0 : PolyHom 8 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_10 (b : Fin 3) : PolyHom 8 10 :=
  ![polyRep8_10_0,PolyHom.zero 8 10,PolyHom.zero 8 10] b
theorem polyLiftFree8_10 : ∀ b : Fin 3, (polyLift8_10 b).freeBlock=basisInt (homKind 8 10) b := by decide
def polyRep8_11_0 : PolyHom 8 11 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_11 (b : Fin 3) : PolyHom 8 11 :=
  ![polyRep8_11_0,PolyHom.zero 8 11,PolyHom.zero 8 11] b
theorem polyLiftFree8_11 : ∀ b : Fin 3, (polyLift8_11 b).freeBlock=basisInt (homKind 8 11) b := by decide
def polyRep8_12_0 : PolyHom 8 12 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_12 (b : Fin 3) : PolyHom 8 12 :=
  ![polyRep8_12_0,PolyHom.zero 8 12,PolyHom.zero 8 12] b
theorem polyLiftFree8_12 : ∀ b : Fin 3, (polyLift8_12 b).freeBlock=basisInt (homKind 8 12) b := by decide
def polyRep8_13_0 : PolyHom 8 13 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_13 (b : Fin 3) : PolyHom 8 13 :=
  ![polyRep8_13_0,PolyHom.zero 8 13,PolyHom.zero 8 13] b
theorem polyLiftFree8_13 : ∀ b : Fin 3, (polyLift8_13 b).freeBlock=basisInt (homKind 8 13) b := by decide
def polyLift8_14 (b : Fin 3) : PolyHom 8 14 :=
  ![PolyHom.zero 8 14,PolyHom.zero 8 14,PolyHom.zero 8 14] b
theorem polyLiftFree8_14 : ∀ b : Fin 3, (polyLift8_14 b).freeBlock=basisInt (homKind 8 14) b := by decide
def polyLift8_15 (b : Fin 3) : PolyHom 8 15 :=
  ![PolyHom.zero 8 15,PolyHom.zero 8 15,PolyHom.zero 8 15] b
theorem polyLiftFree8_15 : ∀ b : Fin 3, (polyLift8_15 b).freeBlock=basisInt (homKind 8 15) b := by decide
def polyRep8_16_0 : PolyHom 8 16 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_16 (b : Fin 3) : PolyHom 8 16 :=
  ![polyRep8_16_0,PolyHom.zero 8 16,PolyHom.zero 8 16] b
theorem polyLiftFree8_16 : ∀ b : Fin 3, (polyLift8_16 b).freeBlock=basisInt (homKind 8 16) b := by decide
def polyLift8_17 (b : Fin 3) : PolyHom 8 17 :=
  ![PolyHom.zero 8 17,PolyHom.zero 8 17,PolyHom.zero 8 17] b
theorem polyLiftFree8_17 : ∀ b : Fin 3, (polyLift8_17 b).freeBlock=basisInt (homKind 8 17) b := by decide
def polyRep8_18_0 : PolyHom 8 18 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_18 (b : Fin 3) : PolyHom 8 18 :=
  ![polyRep8_18_0,PolyHom.zero 8 18,PolyHom.zero 8 18] b
theorem polyLiftFree8_18 : ∀ b : Fin 3, (polyLift8_18 b).freeBlock=basisInt (homKind 8 18) b := by decide
def polyLift8_19 (b : Fin 3) : PolyHom 8 19 :=
  ![PolyHom.zero 8 19,PolyHom.zero 8 19,PolyHom.zero 8 19] b
theorem polyLiftFree8_19 : ∀ b : Fin 3, (polyLift8_19 b).freeBlock=basisInt (homKind 8 19) b := by decide
def polyLift8_20 (b : Fin 3) : PolyHom 8 20 :=
  ![PolyHom.zero 8 20,PolyHom.zero 8 20,PolyHom.zero 8 20] b
theorem polyLiftFree8_20 : ∀ b : Fin 3, (polyLift8_20 b).freeBlock=basisInt (homKind 8 20) b := by decide
def polyRep8_21_0 : PolyHom 8 21 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_21 (b : Fin 3) : PolyHom 8 21 :=
  ![polyRep8_21_0,PolyHom.zero 8 21,PolyHom.zero 8 21] b
theorem polyLiftFree8_21 : ∀ b : Fin 3, (polyLift8_21 b).freeBlock=basisInt (homKind 8 21) b := by decide
def polyRep8_22_0 : PolyHom 8 22 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_22 (b : Fin 3) : PolyHom 8 22 :=
  ![polyRep8_22_0,PolyHom.zero 8 22,PolyHom.zero 8 22] b
theorem polyLiftFree8_22 : ∀ b : Fin 3, (polyLift8_22 b).freeBlock=basisInt (homKind 8 22) b := by decide
def polyLift8_23 (b : Fin 3) : PolyHom 8 23 :=
  ![PolyHom.zero 8 23,PolyHom.zero 8 23,PolyHom.zero 8 23] b
theorem polyLiftFree8_23 : ∀ b : Fin 3, (polyLift8_23 b).freeBlock=basisInt (homKind 8 23) b := by decide
def polyRep8_24_0 : PolyHom 8 24 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_24 (b : Fin 3) : PolyHom 8 24 :=
  ![polyRep8_24_0,PolyHom.zero 8 24,PolyHom.zero 8 24] b
theorem polyLiftFree8_24 : ∀ b : Fin 3, (polyLift8_24 b).freeBlock=basisInt (homKind 8 24) b := by decide
def polyRep8_25_0 : PolyHom 8 25 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_25 (b : Fin 3) : PolyHom 8 25 :=
  ![polyRep8_25_0,PolyHom.zero 8 25,PolyHom.zero 8 25] b
theorem polyLiftFree8_25 : ∀ b : Fin 3, (polyLift8_25 b).freeBlock=basisInt (homKind 8 25) b := by decide
def polyRep8_26_0 : PolyHom 8 26 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_26 (b : Fin 3) : PolyHom 8 26 :=
  ![polyRep8_26_0,PolyHom.zero 8 26,PolyHom.zero 8 26] b
theorem polyLiftFree8_26 : ∀ b : Fin 3, (polyLift8_26 b).freeBlock=basisInt (homKind 8 26) b := by decide
def polyRep8_27_0 : PolyHom 8 27 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_27 (b : Fin 3) : PolyHom 8 27 :=
  ![polyRep8_27_0,PolyHom.zero 8 27,PolyHom.zero 8 27] b
theorem polyLiftFree8_27 : ∀ b : Fin 3, (polyLift8_27 b).freeBlock=basisInt (homKind 8 27) b := by decide
def polyLift8_28 (b : Fin 3) : PolyHom 8 28 :=
  ![PolyHom.zero 8 28,PolyHom.zero 8 28,PolyHom.zero 8 28] b
theorem polyLiftFree8_28 : ∀ b : Fin 3, (polyLift8_28 b).freeBlock=basisInt (homKind 8 28) b := by decide
def polyLift8_29 (b : Fin 3) : PolyHom 8 29 :=
  ![PolyHom.zero 8 29,PolyHom.zero 8 29,PolyHom.zero 8 29] b
theorem polyLiftFree8_29 : ∀ b : Fin 3, (polyLift8_29 b).freeBlock=basisInt (homKind 8 29) b := by decide
def polyRep8_30_0 : PolyHom 8 30 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_30 (b : Fin 3) : PolyHom 8 30 :=
  ![polyRep8_30_0,PolyHom.zero 8 30,PolyHom.zero 8 30] b
theorem polyLiftFree8_30 : ∀ b : Fin 3, (polyLift8_30 b).freeBlock=basisInt (homKind 8 30) b := by decide
def polyRep8_31_0 : PolyHom 8 31 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_31 (b : Fin 3) : PolyHom 8 31 :=
  ![polyRep8_31_0,PolyHom.zero 8 31,PolyHom.zero 8 31] b
theorem polyLiftFree8_31 : ∀ b : Fin 3, (polyLift8_31 b).freeBlock=basisInt (homKind 8 31) b := by decide
def polyRep8_32_0 : PolyHom 8 32 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_32 (b : Fin 3) : PolyHom 8 32 :=
  ![polyRep8_32_0,PolyHom.zero 8 32,PolyHom.zero 8 32] b
theorem polyLiftFree8_32 : ∀ b : Fin 3, (polyLift8_32 b).freeBlock=basisInt (homKind 8 32) b := by decide
def polyRep8_33_0 : PolyHom 8 33 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_33 (b : Fin 3) : PolyHom 8 33 :=
  ![polyRep8_33_0,PolyHom.zero 8 33,PolyHom.zero 8 33] b
theorem polyLiftFree8_33 : ∀ b : Fin 3, (polyLift8_33 b).freeBlock=basisInt (homKind 8 33) b := by decide
def polyRep8_34_0 : PolyHom 8 34 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_34 (b : Fin 3) : PolyHom 8 34 :=
  ![polyRep8_34_0,PolyHom.zero 8 34,PolyHom.zero 8 34] b
theorem polyLiftFree8_34 : ∀ b : Fin 3, (polyLift8_34 b).freeBlock=basisInt (homKind 8 34) b := by decide
def polyRep8_35_0 : PolyHom 8 35 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_35 (b : Fin 3) : PolyHom 8 35 :=
  ![polyRep8_35_0,PolyHom.zero 8 35,PolyHom.zero 8 35] b
theorem polyLiftFree8_35 : ∀ b : Fin 3, (polyLift8_35 b).freeBlock=basisInt (homKind 8 35) b := by decide
def polyRep8_36_0 : PolyHom 8 36 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_36 (b : Fin 3) : PolyHom 8 36 :=
  ![polyRep8_36_0,PolyHom.zero 8 36,PolyHom.zero 8 36] b
theorem polyLiftFree8_36 : ∀ b : Fin 3, (polyLift8_36 b).freeBlock=basisInt (homKind 8 36) b := by decide
def polyRep8_37_0 : PolyHom 8 37 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_37 (b : Fin 3) : PolyHom 8 37 :=
  ![polyRep8_37_0,PolyHom.zero 8 37,PolyHom.zero 8 37] b
theorem polyLiftFree8_37 : ∀ b : Fin 3, (polyLift8_37 b).freeBlock=basisInt (homKind 8 37) b := by decide
def polyRep8_38_0 : PolyHom 8 38 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_38 (b : Fin 3) : PolyHom 8 38 :=
  ![polyRep8_38_0,PolyHom.zero 8 38,PolyHom.zero 8 38] b
theorem polyLiftFree8_38 : ∀ b : Fin 3, (polyLift8_38 b).freeBlock=basisInt (homKind 8 38) b := by decide
def polyRep8_39_0 : PolyHom 8 39 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_39 (b : Fin 3) : PolyHom 8 39 :=
  ![polyRep8_39_0,PolyHom.zero 8 39,PolyHom.zero 8 39] b
theorem polyLiftFree8_39 : ∀ b : Fin 3, (polyLift8_39 b).freeBlock=basisInt (homKind 8 39) b := by decide
def polyRep8_40_0 : PolyHom 8 40 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_40 (b : Fin 3) : PolyHom 8 40 :=
  ![polyRep8_40_0,PolyHom.zero 8 40,PolyHom.zero 8 40] b
theorem polyLiftFree8_40 : ∀ b : Fin 3, (polyLift8_40 b).freeBlock=basisInt (homKind 8 40) b := by decide
def polyRep8_41_0 : PolyHom 8 41 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_41 (b : Fin 3) : PolyHom 8 41 :=
  ![polyRep8_41_0,PolyHom.zero 8 41,PolyHom.zero 8 41] b
theorem polyLiftFree8_41 : ∀ b : Fin 3, (polyLift8_41 b).freeBlock=basisInt (homKind 8 41) b := by decide
def polyRep8_42_0 : PolyHom 8 42 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_42 (b : Fin 3) : PolyHom 8 42 :=
  ![polyRep8_42_0,PolyHom.zero 8 42,PolyHom.zero 8 42] b
theorem polyLiftFree8_42 : ∀ b : Fin 3, (polyLift8_42 b).freeBlock=basisInt (homKind 8 42) b := by decide
def polyRep8_43_0 : PolyHom 8 43 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_43 (b : Fin 3) : PolyHom 8 43 :=
  ![polyRep8_43_0,PolyHom.zero 8 43,PolyHom.zero 8 43] b
theorem polyLiftFree8_43 : ∀ b : Fin 3, (polyLift8_43 b).freeBlock=basisInt (homKind 8 43) b := by decide
def polyRep8_44_0 : PolyHom 8 44 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_44 (b : Fin 3) : PolyHom 8 44 :=
  ![polyRep8_44_0,PolyHom.zero 8 44,PolyHom.zero 8 44] b
theorem polyLiftFree8_44 : ∀ b : Fin 3, (polyLift8_44 b).freeBlock=basisInt (homKind 8 44) b := by decide
def polyRep8_45_0 : PolyHom 8 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift8_45 (b : Fin 3) : PolyHom 8 45 :=
  ![polyRep8_45_0,PolyHom.zero 8 45,PolyHom.zero 8 45] b
theorem polyLiftFree8_45 : ∀ b : Fin 3, (polyLift8_45 b).freeBlock=basisInt (homKind 8 45) b := by decide
def polyLift8_46 (b : Fin 3) : PolyHom 8 46 :=
  ![PolyHom.zero 8 46,PolyHom.zero 8 46,PolyHom.zero 8 46] b
theorem polyLiftFree8_46 : ∀ b : Fin 3, (polyLift8_46 b).freeBlock=basisInt (homKind 8 46) b := by decide
def polyLiftRow8 (j : Fin 47) (b : Fin 3) : PolyHom 8 j :=
  match j with
  | ⟨0,_⟩ => polyLift8_0 b
  | ⟨1,_⟩ => polyLift8_1 b
  | ⟨2,_⟩ => polyLift8_2 b
  | ⟨3,_⟩ => polyLift8_3 b
  | ⟨4,_⟩ => polyLift8_4 b
  | ⟨5,_⟩ => polyLift8_5 b
  | ⟨6,_⟩ => polyLift8_6 b
  | ⟨7,_⟩ => polyLift8_7 b
  | ⟨8,_⟩ => polyLift8_8 b
  | ⟨9,_⟩ => polyLift8_9 b
  | ⟨10,_⟩ => polyLift8_10 b
  | ⟨11,_⟩ => polyLift8_11 b
  | ⟨12,_⟩ => polyLift8_12 b
  | ⟨13,_⟩ => polyLift8_13 b
  | ⟨14,_⟩ => polyLift8_14 b
  | ⟨15,_⟩ => polyLift8_15 b
  | ⟨16,_⟩ => polyLift8_16 b
  | ⟨17,_⟩ => polyLift8_17 b
  | ⟨18,_⟩ => polyLift8_18 b
  | ⟨19,_⟩ => polyLift8_19 b
  | ⟨20,_⟩ => polyLift8_20 b
  | ⟨21,_⟩ => polyLift8_21 b
  | ⟨22,_⟩ => polyLift8_22 b
  | ⟨23,_⟩ => polyLift8_23 b
  | ⟨24,_⟩ => polyLift8_24 b
  | ⟨25,_⟩ => polyLift8_25 b
  | ⟨26,_⟩ => polyLift8_26 b
  | ⟨27,_⟩ => polyLift8_27 b
  | ⟨28,_⟩ => polyLift8_28 b
  | ⟨29,_⟩ => polyLift8_29 b
  | ⟨30,_⟩ => polyLift8_30 b
  | ⟨31,_⟩ => polyLift8_31 b
  | ⟨32,_⟩ => polyLift8_32 b
  | ⟨33,_⟩ => polyLift8_33 b
  | ⟨34,_⟩ => polyLift8_34 b
  | ⟨35,_⟩ => polyLift8_35 b
  | ⟨36,_⟩ => polyLift8_36 b
  | ⟨37,_⟩ => polyLift8_37 b
  | ⟨38,_⟩ => polyLift8_38 b
  | ⟨39,_⟩ => polyLift8_39 b
  | ⟨40,_⟩ => polyLift8_40 b
  | ⟨41,_⟩ => polyLift8_41 b
  | ⟨42,_⟩ => polyLift8_42 b
  | ⟨43,_⟩ => polyLift8_43 b
  | ⟨44,_⟩ => polyLift8_44 b
  | ⟨45,_⟩ => polyLift8_45 b
  | ⟨46,_⟩ => polyLift8_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree8 (j : Fin 47) (b : Fin 3) : (polyLiftRow8 j b).freeBlock=basisInt (homKind 8 j) b := by
  fin_cases j
  · exact polyLiftFree8_0 b
  · exact polyLiftFree8_1 b
  · exact polyLiftFree8_2 b
  · exact polyLiftFree8_3 b
  · exact polyLiftFree8_4 b
  · exact polyLiftFree8_5 b
  · exact polyLiftFree8_6 b
  · exact polyLiftFree8_7 b
  · exact polyLiftFree8_8 b
  · exact polyLiftFree8_9 b
  · exact polyLiftFree8_10 b
  · exact polyLiftFree8_11 b
  · exact polyLiftFree8_12 b
  · exact polyLiftFree8_13 b
  · exact polyLiftFree8_14 b
  · exact polyLiftFree8_15 b
  · exact polyLiftFree8_16 b
  · exact polyLiftFree8_17 b
  · exact polyLiftFree8_18 b
  · exact polyLiftFree8_19 b
  · exact polyLiftFree8_20 b
  · exact polyLiftFree8_21 b
  · exact polyLiftFree8_22 b
  · exact polyLiftFree8_23 b
  · exact polyLiftFree8_24 b
  · exact polyLiftFree8_25 b
  · exact polyLiftFree8_26 b
  · exact polyLiftFree8_27 b
  · exact polyLiftFree8_28 b
  · exact polyLiftFree8_29 b
  · exact polyLiftFree8_30 b
  · exact polyLiftFree8_31 b
  · exact polyLiftFree8_32 b
  · exact polyLiftFree8_33 b
  · exact polyLiftFree8_34 b
  · exact polyLiftFree8_35 b
  · exact polyLiftFree8_36 b
  · exact polyLiftFree8_37 b
  · exact polyLiftFree8_38 b
  · exact polyLiftFree8_39 b
  · exact polyLiftFree8_40 b
  · exact polyLiftFree8_41 b
  · exact polyLiftFree8_42 b
  · exact polyLiftFree8_43 b
  · exact polyLiftFree8_44 b
  · exact polyLiftFree8_45 b
  · exact polyLiftFree8_46 b
end UniserialComputations.N6
