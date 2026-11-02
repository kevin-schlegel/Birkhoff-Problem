import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift20_0 (b : Fin 3) : PolyHom 20 0 :=
  ![PolyHom.zero 20 0,PolyHom.zero 20 0,PolyHom.zero 20 0] b
theorem polyLiftFree20_0 : ∀ b : Fin 3, (polyLift20_0 b).freeBlock=basisInt (homKind 20 0) b := by decide
def polyLift20_1 (b : Fin 3) : PolyHom 20 1 :=
  ![PolyHom.zero 20 1,PolyHom.zero 20 1,PolyHom.zero 20 1] b
theorem polyLiftFree20_1 : ∀ b : Fin 3, (polyLift20_1 b).freeBlock=basisInt (homKind 20 1) b := by decide
def polyLift20_2 (b : Fin 3) : PolyHom 20 2 :=
  ![PolyHom.zero 20 2,PolyHom.zero 20 2,PolyHom.zero 20 2] b
theorem polyLiftFree20_2 : ∀ b : Fin 3, (polyLift20_2 b).freeBlock=basisInt (homKind 20 2) b := by decide
def polyLift20_3 (b : Fin 3) : PolyHom 20 3 :=
  ![PolyHom.zero 20 3,PolyHom.zero 20 3,PolyHom.zero 20 3] b
theorem polyLiftFree20_3 : ∀ b : Fin 3, (polyLift20_3 b).freeBlock=basisInt (homKind 20 3) b := by decide
def polyLift20_4 (b : Fin 3) : PolyHom 20 4 :=
  ![PolyHom.zero 20 4,PolyHom.zero 20 4,PolyHom.zero 20 4] b
theorem polyLiftFree20_4 : ∀ b : Fin 3, (polyLift20_4 b).freeBlock=basisInt (homKind 20 4) b := by decide
def polyLift20_5 (b : Fin 3) : PolyHom 20 5 :=
  ![PolyHom.zero 20 5,PolyHom.zero 20 5,PolyHom.zero 20 5] b
theorem polyLiftFree20_5 : ∀ b : Fin 3, (polyLift20_5 b).freeBlock=basisInt (homKind 20 5) b := by decide
def polyRep20_6_0 : PolyHom 20 6 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_6 (b : Fin 3) : PolyHom 20 6 :=
  ![polyRep20_6_0,PolyHom.zero 20 6,PolyHom.zero 20 6] b
theorem polyLiftFree20_6 : ∀ b : Fin 3, (polyLift20_6 b).freeBlock=basisInt (homKind 20 6) b := by decide
def polyRep20_7_0 : PolyHom 20 7 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_7 (b : Fin 3) : PolyHom 20 7 :=
  ![polyRep20_7_0,PolyHom.zero 20 7,PolyHom.zero 20 7] b
theorem polyLiftFree20_7 : ∀ b : Fin 3, (polyLift20_7 b).freeBlock=basisInt (homKind 20 7) b := by decide
def polyRep20_8_0 : PolyHom 20 8 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_8 (b : Fin 3) : PolyHom 20 8 :=
  ![polyRep20_8_0,PolyHom.zero 20 8,PolyHom.zero 20 8] b
theorem polyLiftFree20_8 : ∀ b : Fin 3, (polyLift20_8 b).freeBlock=basisInt (homKind 20 8) b := by decide
def polyLift20_9 (b : Fin 3) : PolyHom 20 9 :=
  ![PolyHom.zero 20 9,PolyHom.zero 20 9,PolyHom.zero 20 9] b
theorem polyLiftFree20_9 : ∀ b : Fin 3, (polyLift20_9 b).freeBlock=basisInt (homKind 20 9) b := by decide
def polyRep20_10_0 : PolyHom 20 10 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_10 (b : Fin 3) : PolyHom 20 10 :=
  ![polyRep20_10_0,PolyHom.zero 20 10,PolyHom.zero 20 10] b
theorem polyLiftFree20_10 : ∀ b : Fin 3, (polyLift20_10 b).freeBlock=basisInt (homKind 20 10) b := by decide
def polyRep20_11_0 : PolyHom 20 11 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_11 (b : Fin 3) : PolyHom 20 11 :=
  ![polyRep20_11_0,PolyHom.zero 20 11,PolyHom.zero 20 11] b
theorem polyLiftFree20_11 : ∀ b : Fin 3, (polyLift20_11 b).freeBlock=basisInt (homKind 20 11) b := by decide
def polyRep20_12_0 : PolyHom 20 12 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_12 (b : Fin 3) : PolyHom 20 12 :=
  ![polyRep20_12_0,PolyHom.zero 20 12,PolyHom.zero 20 12] b
theorem polyLiftFree20_12 : ∀ b : Fin 3, (polyLift20_12 b).freeBlock=basisInt (homKind 20 12) b := by decide
def polyRep20_13_0 : PolyHom 20 13 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_13 (b : Fin 3) : PolyHom 20 13 :=
  ![polyRep20_13_0,PolyHom.zero 20 13,PolyHom.zero 20 13] b
theorem polyLiftFree20_13 : ∀ b : Fin 3, (polyLift20_13 b).freeBlock=basisInt (homKind 20 13) b := by decide
def polyLift20_14 (b : Fin 3) : PolyHom 20 14 :=
  ![PolyHom.zero 20 14,PolyHom.zero 20 14,PolyHom.zero 20 14] b
theorem polyLiftFree20_14 : ∀ b : Fin 3, (polyLift20_14 b).freeBlock=basisInt (homKind 20 14) b := by decide
def polyLift20_15 (b : Fin 3) : PolyHom 20 15 :=
  ![PolyHom.zero 20 15,PolyHom.zero 20 15,PolyHom.zero 20 15] b
theorem polyLiftFree20_15 : ∀ b : Fin 3, (polyLift20_15 b).freeBlock=basisInt (homKind 20 15) b := by decide
def polyRep20_16_0 : PolyHom 20 16 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_16 (b : Fin 3) : PolyHom 20 16 :=
  ![polyRep20_16_0,PolyHom.zero 20 16,PolyHom.zero 20 16] b
theorem polyLiftFree20_16 : ∀ b : Fin 3, (polyLift20_16 b).freeBlock=basisInt (homKind 20 16) b := by decide
def polyLift20_17 (b : Fin 3) : PolyHom 20 17 :=
  ![PolyHom.zero 20 17,PolyHom.zero 20 17,PolyHom.zero 20 17] b
theorem polyLiftFree20_17 : ∀ b : Fin 3, (polyLift20_17 b).freeBlock=basisInt (homKind 20 17) b := by decide
def polyRep20_18_0 : PolyHom 20 18 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_18 (b : Fin 3) : PolyHom 20 18 :=
  ![polyRep20_18_0,PolyHom.zero 20 18,PolyHom.zero 20 18] b
theorem polyLiftFree20_18 : ∀ b : Fin 3, (polyLift20_18 b).freeBlock=basisInt (homKind 20 18) b := by decide
def polyRep20_19_0 : PolyHom 20 19 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_19 (b : Fin 3) : PolyHom 20 19 :=
  ![polyRep20_19_0,PolyHom.zero 20 19,PolyHom.zero 20 19] b
theorem polyLiftFree20_19 : ∀ b : Fin 3, (polyLift20_19 b).freeBlock=basisInt (homKind 20 19) b := by decide
def polyRep20_20_0 : PolyHom 20 20 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_20 (b : Fin 3) : PolyHom 20 20 :=
  ![polyRep20_20_0,PolyHom.zero 20 20,PolyHom.zero 20 20] b
theorem polyLiftFree20_20 : ∀ b : Fin 3, (polyLift20_20 b).freeBlock=basisInt (homKind 20 20) b := by decide
def polyRep20_21_0 : PolyHom 20 21 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_21 (b : Fin 3) : PolyHom 20 21 :=
  ![polyRep20_21_0,PolyHom.zero 20 21,PolyHom.zero 20 21] b
theorem polyLiftFree20_21 : ∀ b : Fin 3, (polyLift20_21 b).freeBlock=basisInt (homKind 20 21) b := by decide
def polyRep20_22_0 : PolyHom 20 22 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_22 (b : Fin 3) : PolyHom 20 22 :=
  ![polyRep20_22_0,PolyHom.zero 20 22,PolyHom.zero 20 22] b
theorem polyLiftFree20_22 : ∀ b : Fin 3, (polyLift20_22 b).freeBlock=basisInt (homKind 20 22) b := by decide
def polyLift20_23 (b : Fin 3) : PolyHom 20 23 :=
  ![PolyHom.zero 20 23,PolyHom.zero 20 23,PolyHom.zero 20 23] b
theorem polyLiftFree20_23 : ∀ b : Fin 3, (polyLift20_23 b).freeBlock=basisInt (homKind 20 23) b := by decide
def polyRep20_24_0 : PolyHom 20 24 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_24 (b : Fin 3) : PolyHom 20 24 :=
  ![polyRep20_24_0,PolyHom.zero 20 24,PolyHom.zero 20 24] b
theorem polyLiftFree20_24 : ∀ b : Fin 3, (polyLift20_24 b).freeBlock=basisInt (homKind 20 24) b := by decide
def polyRep20_25_0 : PolyHom 20 25 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_25 (b : Fin 3) : PolyHom 20 25 :=
  ![polyRep20_25_0,PolyHom.zero 20 25,PolyHom.zero 20 25] b
theorem polyLiftFree20_25 : ∀ b : Fin 3, (polyLift20_25 b).freeBlock=basisInt (homKind 20 25) b := by decide
def polyRep20_26_0 : PolyHom 20 26 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_26 (b : Fin 3) : PolyHom 20 26 :=
  ![polyRep20_26_0,PolyHom.zero 20 26,PolyHom.zero 20 26] b
theorem polyLiftFree20_26 : ∀ b : Fin 3, (polyLift20_26 b).freeBlock=basisInt (homKind 20 26) b := by decide
def polyRep20_27_0 : PolyHom 20 27 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_27 (b : Fin 3) : PolyHom 20 27 :=
  ![polyRep20_27_0,PolyHom.zero 20 27,PolyHom.zero 20 27] b
theorem polyLiftFree20_27 : ∀ b : Fin 3, (polyLift20_27 b).freeBlock=basisInt (homKind 20 27) b := by decide
def polyRep20_28_0 : PolyHom 20 28 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_28 (b : Fin 3) : PolyHom 20 28 :=
  ![polyRep20_28_0,PolyHom.zero 20 28,PolyHom.zero 20 28] b
theorem polyLiftFree20_28 : ∀ b : Fin 3, (polyLift20_28 b).freeBlock=basisInt (homKind 20 28) b := by decide
def polyRep20_29_0 : PolyHom 20 29 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_29 (b : Fin 3) : PolyHom 20 29 :=
  ![polyRep20_29_0,PolyHom.zero 20 29,PolyHom.zero 20 29] b
theorem polyLiftFree20_29 : ∀ b : Fin 3, (polyLift20_29 b).freeBlock=basisInt (homKind 20 29) b := by decide
def polyRep20_30_0 : PolyHom 20 30 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_30 (b : Fin 3) : PolyHom 20 30 :=
  ![polyRep20_30_0,PolyHom.zero 20 30,PolyHom.zero 20 30] b
theorem polyLiftFree20_30 : ∀ b : Fin 3, (polyLift20_30 b).freeBlock=basisInt (homKind 20 30) b := by decide
def polyRep20_31_0 : PolyHom 20 31 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_31 (b : Fin 3) : PolyHom 20 31 :=
  ![polyRep20_31_0,PolyHom.zero 20 31,PolyHom.zero 20 31] b
theorem polyLiftFree20_31 : ∀ b : Fin 3, (polyLift20_31 b).freeBlock=basisInt (homKind 20 31) b := by decide
def polyRep20_32_0 : PolyHom 20 32 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_32 (b : Fin 3) : PolyHom 20 32 :=
  ![polyRep20_32_0,PolyHom.zero 20 32,PolyHom.zero 20 32] b
theorem polyLiftFree20_32 : ∀ b : Fin 3, (polyLift20_32 b).freeBlock=basisInt (homKind 20 32) b := by decide
def polyRep20_33_0 : PolyHom 20 33 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_33 (b : Fin 3) : PolyHom 20 33 :=
  ![polyRep20_33_0,PolyHom.zero 20 33,PolyHom.zero 20 33] b
theorem polyLiftFree20_33 : ∀ b : Fin 3, (polyLift20_33 b).freeBlock=basisInt (homKind 20 33) b := by decide
def polyRep20_34_0 : PolyHom 20 34 where
  M := !![0,(mono6 (-1) 2),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_34 (b : Fin 3) : PolyHom 20 34 :=
  ![polyRep20_34_0,PolyHom.zero 20 34,PolyHom.zero 20 34] b
theorem polyLiftFree20_34 : ∀ b : Fin 3, (polyLift20_34 b).freeBlock=basisInt (homKind 20 34) b := by decide
def polyRep20_35_0 : PolyHom 20 35 where
  M := !![0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_35 (b : Fin 3) : PolyHom 20 35 :=
  ![polyRep20_35_0,PolyHom.zero 20 35,PolyHom.zero 20 35] b
theorem polyLiftFree20_35 : ∀ b : Fin 3, (polyLift20_35 b).freeBlock=basisInt (homKind 20 35) b := by decide
def polyRep20_36_0 : PolyHom 20 36 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_36 (b : Fin 3) : PolyHom 20 36 :=
  ![polyRep20_36_0,PolyHom.zero 20 36,PolyHom.zero 20 36] b
theorem polyLiftFree20_36 : ∀ b : Fin 3, (polyLift20_36 b).freeBlock=basisInt (homKind 20 36) b := by decide
def polyRep20_37_0 : PolyHom 20 37 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_37 (b : Fin 3) : PolyHom 20 37 :=
  ![polyRep20_37_0,PolyHom.zero 20 37,PolyHom.zero 20 37] b
theorem polyLiftFree20_37 : ∀ b : Fin 3, (polyLift20_37 b).freeBlock=basisInt (homKind 20 37) b := by decide
def polyRep20_38_0 : PolyHom 20 38 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_38 (b : Fin 3) : PolyHom 20 38 :=
  ![polyRep20_38_0,PolyHom.zero 20 38,PolyHom.zero 20 38] b
theorem polyLiftFree20_38 : ∀ b : Fin 3, (polyLift20_38 b).freeBlock=basisInt (homKind 20 38) b := by decide
def polyRep20_39_0 : PolyHom 20 39 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_39 (b : Fin 3) : PolyHom 20 39 :=
  ![polyRep20_39_0,PolyHom.zero 20 39,PolyHom.zero 20 39] b
theorem polyLiftFree20_39 : ∀ b : Fin 3, (polyLift20_39 b).freeBlock=basisInt (homKind 20 39) b := by decide
def polyRep20_40_0 : PolyHom 20 40 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_40 (b : Fin 3) : PolyHom 20 40 :=
  ![polyRep20_40_0,PolyHom.zero 20 40,PolyHom.zero 20 40] b
theorem polyLiftFree20_40 : ∀ b : Fin 3, (polyLift20_40 b).freeBlock=basisInt (homKind 20 40) b := by decide
def polyRep20_41_0 : PolyHom 20 41 where
  M := !![0,(mono6 (-1) 1),0,(mono6 (1) 0);0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_41 (b : Fin 3) : PolyHom 20 41 :=
  ![polyRep20_41_0,PolyHom.zero 20 41,PolyHom.zero 20 41] b
theorem polyLiftFree20_41 : ∀ b : Fin 3, (polyLift20_41 b).freeBlock=basisInt (homKind 20 41) b := by decide
def polyRep20_42_0 : PolyHom 20 42 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep20_42_1 : PolyHom 20 42 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_42 (b : Fin 3) : PolyHom 20 42 :=
  ![polyRep20_42_0,polyRep20_42_1,PolyHom.zero 20 42] b
theorem polyLiftFree20_42 : ∀ b : Fin 3, (polyLift20_42 b).freeBlock=basisInt (homKind 20 42) b := by decide
def polyRep20_43_0 : PolyHom 20 43 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep20_43_1 : PolyHom 20 43 where
  M := !![0,(mono6 (-1) 1),0,0;0,(mono6 (1) 0),0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_43 (b : Fin 3) : PolyHom 20 43 :=
  ![polyRep20_43_0,polyRep20_43_1,PolyHom.zero 20 43] b
theorem polyLiftFree20_43 : ∀ b : Fin 3, (polyLift20_43 b).freeBlock=basisInt (homKind 20 43) b := by decide
def polyRep20_44_0 : PolyHom 20 44 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep20_44_1 : PolyHom 20 44 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_44 (b : Fin 3) : PolyHom 20 44 :=
  ![polyRep20_44_0,polyRep20_44_1,PolyHom.zero 20 44] b
theorem polyLiftFree20_44 : ∀ b : Fin 3, (polyLift20_44 b).freeBlock=basisInt (homKind 20 44) b := by decide
def polyRep20_45_0 : PolyHom 20 45 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift20_45 (b : Fin 3) : PolyHom 20 45 :=
  ![polyRep20_45_0,PolyHom.zero 20 45,PolyHom.zero 20 45] b
theorem polyLiftFree20_45 : ∀ b : Fin 3, (polyLift20_45 b).freeBlock=basisInt (homKind 20 45) b := by decide
def polyLift20_46 (b : Fin 3) : PolyHom 20 46 :=
  ![PolyHom.zero 20 46,PolyHom.zero 20 46,PolyHom.zero 20 46] b
theorem polyLiftFree20_46 : ∀ b : Fin 3, (polyLift20_46 b).freeBlock=basisInt (homKind 20 46) b := by decide
def polyLiftRow20 (j : Fin 47) (b : Fin 3) : PolyHom 20 j :=
  match j with
  | ⟨0,_⟩ => polyLift20_0 b
  | ⟨1,_⟩ => polyLift20_1 b
  | ⟨2,_⟩ => polyLift20_2 b
  | ⟨3,_⟩ => polyLift20_3 b
  | ⟨4,_⟩ => polyLift20_4 b
  | ⟨5,_⟩ => polyLift20_5 b
  | ⟨6,_⟩ => polyLift20_6 b
  | ⟨7,_⟩ => polyLift20_7 b
  | ⟨8,_⟩ => polyLift20_8 b
  | ⟨9,_⟩ => polyLift20_9 b
  | ⟨10,_⟩ => polyLift20_10 b
  | ⟨11,_⟩ => polyLift20_11 b
  | ⟨12,_⟩ => polyLift20_12 b
  | ⟨13,_⟩ => polyLift20_13 b
  | ⟨14,_⟩ => polyLift20_14 b
  | ⟨15,_⟩ => polyLift20_15 b
  | ⟨16,_⟩ => polyLift20_16 b
  | ⟨17,_⟩ => polyLift20_17 b
  | ⟨18,_⟩ => polyLift20_18 b
  | ⟨19,_⟩ => polyLift20_19 b
  | ⟨20,_⟩ => polyLift20_20 b
  | ⟨21,_⟩ => polyLift20_21 b
  | ⟨22,_⟩ => polyLift20_22 b
  | ⟨23,_⟩ => polyLift20_23 b
  | ⟨24,_⟩ => polyLift20_24 b
  | ⟨25,_⟩ => polyLift20_25 b
  | ⟨26,_⟩ => polyLift20_26 b
  | ⟨27,_⟩ => polyLift20_27 b
  | ⟨28,_⟩ => polyLift20_28 b
  | ⟨29,_⟩ => polyLift20_29 b
  | ⟨30,_⟩ => polyLift20_30 b
  | ⟨31,_⟩ => polyLift20_31 b
  | ⟨32,_⟩ => polyLift20_32 b
  | ⟨33,_⟩ => polyLift20_33 b
  | ⟨34,_⟩ => polyLift20_34 b
  | ⟨35,_⟩ => polyLift20_35 b
  | ⟨36,_⟩ => polyLift20_36 b
  | ⟨37,_⟩ => polyLift20_37 b
  | ⟨38,_⟩ => polyLift20_38 b
  | ⟨39,_⟩ => polyLift20_39 b
  | ⟨40,_⟩ => polyLift20_40 b
  | ⟨41,_⟩ => polyLift20_41 b
  | ⟨42,_⟩ => polyLift20_42 b
  | ⟨43,_⟩ => polyLift20_43 b
  | ⟨44,_⟩ => polyLift20_44 b
  | ⟨45,_⟩ => polyLift20_45 b
  | ⟨46,_⟩ => polyLift20_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree20 (j : Fin 47) (b : Fin 3) : (polyLiftRow20 j b).freeBlock=basisInt (homKind 20 j) b := by
  fin_cases j
  · exact polyLiftFree20_0 b
  · exact polyLiftFree20_1 b
  · exact polyLiftFree20_2 b
  · exact polyLiftFree20_3 b
  · exact polyLiftFree20_4 b
  · exact polyLiftFree20_5 b
  · exact polyLiftFree20_6 b
  · exact polyLiftFree20_7 b
  · exact polyLiftFree20_8 b
  · exact polyLiftFree20_9 b
  · exact polyLiftFree20_10 b
  · exact polyLiftFree20_11 b
  · exact polyLiftFree20_12 b
  · exact polyLiftFree20_13 b
  · exact polyLiftFree20_14 b
  · exact polyLiftFree20_15 b
  · exact polyLiftFree20_16 b
  · exact polyLiftFree20_17 b
  · exact polyLiftFree20_18 b
  · exact polyLiftFree20_19 b
  · exact polyLiftFree20_20 b
  · exact polyLiftFree20_21 b
  · exact polyLiftFree20_22 b
  · exact polyLiftFree20_23 b
  · exact polyLiftFree20_24 b
  · exact polyLiftFree20_25 b
  · exact polyLiftFree20_26 b
  · exact polyLiftFree20_27 b
  · exact polyLiftFree20_28 b
  · exact polyLiftFree20_29 b
  · exact polyLiftFree20_30 b
  · exact polyLiftFree20_31 b
  · exact polyLiftFree20_32 b
  · exact polyLiftFree20_33 b
  · exact polyLiftFree20_34 b
  · exact polyLiftFree20_35 b
  · exact polyLiftFree20_36 b
  · exact polyLiftFree20_37 b
  · exact polyLiftFree20_38 b
  · exact polyLiftFree20_39 b
  · exact polyLiftFree20_40 b
  · exact polyLiftFree20_41 b
  · exact polyLiftFree20_42 b
  · exact polyLiftFree20_43 b
  · exact polyLiftFree20_44 b
  · exact polyLiftFree20_45 b
  · exact polyLiftFree20_46 b
end UniserialComputations.N6
