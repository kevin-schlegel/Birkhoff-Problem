import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift19_0 (b : Fin 3) : PolyHom 19 0 :=
  ![PolyHom.zero 19 0,PolyHom.zero 19 0,PolyHom.zero 19 0] b
theorem polyLiftFree19_0 : ∀ b : Fin 3, (polyLift19_0 b).freeBlock=basisInt (homKind 19 0) b := by decide
def polyLift19_1 (b : Fin 3) : PolyHom 19 1 :=
  ![PolyHom.zero 19 1,PolyHom.zero 19 1,PolyHom.zero 19 1] b
theorem polyLiftFree19_1 : ∀ b : Fin 3, (polyLift19_1 b).freeBlock=basisInt (homKind 19 1) b := by decide
def polyLift19_2 (b : Fin 3) : PolyHom 19 2 :=
  ![PolyHom.zero 19 2,PolyHom.zero 19 2,PolyHom.zero 19 2] b
theorem polyLiftFree19_2 : ∀ b : Fin 3, (polyLift19_2 b).freeBlock=basisInt (homKind 19 2) b := by decide
def polyLift19_3 (b : Fin 3) : PolyHom 19 3 :=
  ![PolyHom.zero 19 3,PolyHom.zero 19 3,PolyHom.zero 19 3] b
theorem polyLiftFree19_3 : ∀ b : Fin 3, (polyLift19_3 b).freeBlock=basisInt (homKind 19 3) b := by decide
def polyLift19_4 (b : Fin 3) : PolyHom 19 4 :=
  ![PolyHom.zero 19 4,PolyHom.zero 19 4,PolyHom.zero 19 4] b
theorem polyLiftFree19_4 : ∀ b : Fin 3, (polyLift19_4 b).freeBlock=basisInt (homKind 19 4) b := by decide
def polyLift19_5 (b : Fin 3) : PolyHom 19 5 :=
  ![PolyHom.zero 19 5,PolyHom.zero 19 5,PolyHom.zero 19 5] b
theorem polyLiftFree19_5 : ∀ b : Fin 3, (polyLift19_5 b).freeBlock=basisInt (homKind 19 5) b := by decide
def polyRep19_6_0 : PolyHom 19 6 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_6 (b : Fin 3) : PolyHom 19 6 :=
  ![polyRep19_6_0,PolyHom.zero 19 6,PolyHom.zero 19 6] b
theorem polyLiftFree19_6 : ∀ b : Fin 3, (polyLift19_6 b).freeBlock=basisInt (homKind 19 6) b := by decide
def polyRep19_7_0 : PolyHom 19 7 where
  M := !![(mono6 (1) 2),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_7 (b : Fin 3) : PolyHom 19 7 :=
  ![polyRep19_7_0,PolyHom.zero 19 7,PolyHom.zero 19 7] b
theorem polyLiftFree19_7 : ∀ b : Fin 3, (polyLift19_7 b).freeBlock=basisInt (homKind 19 7) b := by decide
def polyLift19_8 (b : Fin 3) : PolyHom 19 8 :=
  ![PolyHom.zero 19 8,PolyHom.zero 19 8,PolyHom.zero 19 8] b
theorem polyLiftFree19_8 : ∀ b : Fin 3, (polyLift19_8 b).freeBlock=basisInt (homKind 19 8) b := by decide
def polyLift19_9 (b : Fin 3) : PolyHom 19 9 :=
  ![PolyHom.zero 19 9,PolyHom.zero 19 9,PolyHom.zero 19 9] b
theorem polyLiftFree19_9 : ∀ b : Fin 3, (polyLift19_9 b).freeBlock=basisInt (homKind 19 9) b := by decide
def polyRep19_10_0 : PolyHom 19 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_10 (b : Fin 3) : PolyHom 19 10 :=
  ![polyRep19_10_0,PolyHom.zero 19 10,PolyHom.zero 19 10] b
theorem polyLiftFree19_10 : ∀ b : Fin 3, (polyLift19_10 b).freeBlock=basisInt (homKind 19 10) b := by decide
def polyRep19_11_0 : PolyHom 19 11 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_11 (b : Fin 3) : PolyHom 19 11 :=
  ![polyRep19_11_0,PolyHom.zero 19 11,PolyHom.zero 19 11] b
theorem polyLiftFree19_11 : ∀ b : Fin 3, (polyLift19_11 b).freeBlock=basisInt (homKind 19 11) b := by decide
def polyRep19_12_0 : PolyHom 19 12 where
  M := !![(mono6 (1) 2),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_12 (b : Fin 3) : PolyHom 19 12 :=
  ![polyRep19_12_0,PolyHom.zero 19 12,PolyHom.zero 19 12] b
theorem polyLiftFree19_12 : ∀ b : Fin 3, (polyLift19_12 b).freeBlock=basisInt (homKind 19 12) b := by decide
def polyLift19_13 (b : Fin 3) : PolyHom 19 13 :=
  ![PolyHom.zero 19 13,PolyHom.zero 19 13,PolyHom.zero 19 13] b
theorem polyLiftFree19_13 : ∀ b : Fin 3, (polyLift19_13 b).freeBlock=basisInt (homKind 19 13) b := by decide
def polyLift19_14 (b : Fin 3) : PolyHom 19 14 :=
  ![PolyHom.zero 19 14,PolyHom.zero 19 14,PolyHom.zero 19 14] b
theorem polyLiftFree19_14 : ∀ b : Fin 3, (polyLift19_14 b).freeBlock=basisInt (homKind 19 14) b := by decide
def polyLift19_15 (b : Fin 3) : PolyHom 19 15 :=
  ![PolyHom.zero 19 15,PolyHom.zero 19 15,PolyHom.zero 19 15] b
theorem polyLiftFree19_15 : ∀ b : Fin 3, (polyLift19_15 b).freeBlock=basisInt (homKind 19 15) b := by decide
def polyRep19_16_0 : PolyHom 19 16 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_16 (b : Fin 3) : PolyHom 19 16 :=
  ![polyRep19_16_0,PolyHom.zero 19 16,PolyHom.zero 19 16] b
theorem polyLiftFree19_16 : ∀ b : Fin 3, (polyLift19_16 b).freeBlock=basisInt (homKind 19 16) b := by decide
def polyLift19_17 (b : Fin 3) : PolyHom 19 17 :=
  ![PolyHom.zero 19 17,PolyHom.zero 19 17,PolyHom.zero 19 17] b
theorem polyLiftFree19_17 : ∀ b : Fin 3, (polyLift19_17 b).freeBlock=basisInt (homKind 19 17) b := by decide
def polyRep19_18_0 : PolyHom 19 18 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_18 (b : Fin 3) : PolyHom 19 18 :=
  ![polyRep19_18_0,PolyHom.zero 19 18,PolyHom.zero 19 18] b
theorem polyLiftFree19_18 : ∀ b : Fin 3, (polyLift19_18 b).freeBlock=basisInt (homKind 19 18) b := by decide
def polyRep19_19_0 : PolyHom 19 19 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_19 (b : Fin 3) : PolyHom 19 19 :=
  ![polyRep19_19_0,PolyHom.zero 19 19,PolyHom.zero 19 19] b
theorem polyLiftFree19_19 : ∀ b : Fin 3, (polyLift19_19 b).freeBlock=basisInt (homKind 19 19) b := by decide
def polyLift19_20 (b : Fin 3) : PolyHom 19 20 :=
  ![PolyHom.zero 19 20,PolyHom.zero 19 20,PolyHom.zero 19 20] b
theorem polyLiftFree19_20 : ∀ b : Fin 3, (polyLift19_20 b).freeBlock=basisInt (homKind 19 20) b := by decide
def polyRep19_21_0 : PolyHom 19 21 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_21 (b : Fin 3) : PolyHom 19 21 :=
  ![polyRep19_21_0,PolyHom.zero 19 21,PolyHom.zero 19 21] b
theorem polyLiftFree19_21 : ∀ b : Fin 3, (polyLift19_21 b).freeBlock=basisInt (homKind 19 21) b := by decide
def polyRep19_22_0 : PolyHom 19 22 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_22 (b : Fin 3) : PolyHom 19 22 :=
  ![polyRep19_22_0,PolyHom.zero 19 22,PolyHom.zero 19 22] b
theorem polyLiftFree19_22 : ∀ b : Fin 3, (polyLift19_22 b).freeBlock=basisInt (homKind 19 22) b := by decide
def polyLift19_23 (b : Fin 3) : PolyHom 19 23 :=
  ![PolyHom.zero 19 23,PolyHom.zero 19 23,PolyHom.zero 19 23] b
theorem polyLiftFree19_23 : ∀ b : Fin 3, (polyLift19_23 b).freeBlock=basisInt (homKind 19 23) b := by decide
def polyRep19_24_0 : PolyHom 19 24 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_24 (b : Fin 3) : PolyHom 19 24 :=
  ![polyRep19_24_0,PolyHom.zero 19 24,PolyHom.zero 19 24] b
theorem polyLiftFree19_24 : ∀ b : Fin 3, (polyLift19_24 b).freeBlock=basisInt (homKind 19 24) b := by decide
def polyRep19_25_0 : PolyHom 19 25 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_25 (b : Fin 3) : PolyHom 19 25 :=
  ![polyRep19_25_0,PolyHom.zero 19 25,PolyHom.zero 19 25] b
theorem polyLiftFree19_25 : ∀ b : Fin 3, (polyLift19_25 b).freeBlock=basisInt (homKind 19 25) b := by decide
def polyRep19_26_0 : PolyHom 19 26 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_26 (b : Fin 3) : PolyHom 19 26 :=
  ![polyRep19_26_0,PolyHom.zero 19 26,PolyHom.zero 19 26] b
theorem polyLiftFree19_26 : ∀ b : Fin 3, (polyLift19_26 b).freeBlock=basisInt (homKind 19 26) b := by decide
def polyRep19_27_0 : PolyHom 19 27 where
  M := !![(mono6 (1) 1),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_27 (b : Fin 3) : PolyHom 19 27 :=
  ![polyRep19_27_0,PolyHom.zero 19 27,PolyHom.zero 19 27] b
theorem polyLiftFree19_27 : ∀ b : Fin 3, (polyLift19_27 b).freeBlock=basisInt (homKind 19 27) b := by decide
def polyRep19_28_0 : PolyHom 19 28 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_28 (b : Fin 3) : PolyHom 19 28 :=
  ![polyRep19_28_0,PolyHom.zero 19 28,PolyHom.zero 19 28] b
theorem polyLiftFree19_28 : ∀ b : Fin 3, (polyLift19_28 b).freeBlock=basisInt (homKind 19 28) b := by decide
def polyLift19_29 (b : Fin 3) : PolyHom 19 29 :=
  ![PolyHom.zero 19 29,PolyHom.zero 19 29,PolyHom.zero 19 29] b
theorem polyLiftFree19_29 : ∀ b : Fin 3, (polyLift19_29 b).freeBlock=basisInt (homKind 19 29) b := by decide
def polyRep19_30_0 : PolyHom 19 30 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_30 (b : Fin 3) : PolyHom 19 30 :=
  ![polyRep19_30_0,PolyHom.zero 19 30,PolyHom.zero 19 30] b
theorem polyLiftFree19_30 : ∀ b : Fin 3, (polyLift19_30 b).freeBlock=basisInt (homKind 19 30) b := by decide
def polyRep19_31_0 : PolyHom 19 31 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_31 (b : Fin 3) : PolyHom 19 31 :=
  ![polyRep19_31_0,PolyHom.zero 19 31,PolyHom.zero 19 31] b
theorem polyLiftFree19_31 : ∀ b : Fin 3, (polyLift19_31 b).freeBlock=basisInt (homKind 19 31) b := by decide
def polyRep19_32_0 : PolyHom 19 32 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_32 (b : Fin 3) : PolyHom 19 32 :=
  ![polyRep19_32_0,PolyHom.zero 19 32,PolyHom.zero 19 32] b
theorem polyLiftFree19_32 : ∀ b : Fin 3, (polyLift19_32 b).freeBlock=basisInt (homKind 19 32) b := by decide
def polyRep19_33_0 : PolyHom 19 33 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_33 (b : Fin 3) : PolyHom 19 33 :=
  ![polyRep19_33_0,PolyHom.zero 19 33,PolyHom.zero 19 33] b
theorem polyLiftFree19_33 : ∀ b : Fin 3, (polyLift19_33 b).freeBlock=basisInt (homKind 19 33) b := by decide
def polyRep19_34_0 : PolyHom 19 34 where
  M := !![0,(mono6 (-1) 2),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_34 (b : Fin 3) : PolyHom 19 34 :=
  ![polyRep19_34_0,PolyHom.zero 19 34,PolyHom.zero 19 34] b
theorem polyLiftFree19_34 : ∀ b : Fin 3, (polyLift19_34 b).freeBlock=basisInt (homKind 19 34) b := by decide
def polyLift19_35 (b : Fin 3) : PolyHom 19 35 :=
  ![PolyHom.zero 19 35,PolyHom.zero 19 35,PolyHom.zero 19 35] b
theorem polyLiftFree19_35 : ∀ b : Fin 3, (polyLift19_35 b).freeBlock=basisInt (homKind 19 35) b := by decide
def polyRep19_36_0 : PolyHom 19 36 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_36 (b : Fin 3) : PolyHom 19 36 :=
  ![polyRep19_36_0,PolyHom.zero 19 36,PolyHom.zero 19 36] b
theorem polyLiftFree19_36 : ∀ b : Fin 3, (polyLift19_36 b).freeBlock=basisInt (homKind 19 36) b := by decide
def polyRep19_37_0 : PolyHom 19 37 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_37 (b : Fin 3) : PolyHom 19 37 :=
  ![polyRep19_37_0,PolyHom.zero 19 37,PolyHom.zero 19 37] b
theorem polyLiftFree19_37 : ∀ b : Fin 3, (polyLift19_37 b).freeBlock=basisInt (homKind 19 37) b := by decide
def polyRep19_38_0 : PolyHom 19 38 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_38 (b : Fin 3) : PolyHom 19 38 :=
  ![polyRep19_38_0,PolyHom.zero 19 38,PolyHom.zero 19 38] b
theorem polyLiftFree19_38 : ∀ b : Fin 3, (polyLift19_38 b).freeBlock=basisInt (homKind 19 38) b := by decide
def polyRep19_39_0 : PolyHom 19 39 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_39 (b : Fin 3) : PolyHom 19 39 :=
  ![polyRep19_39_0,PolyHom.zero 19 39,PolyHom.zero 19 39] b
theorem polyLiftFree19_39 : ∀ b : Fin 3, (polyLift19_39 b).freeBlock=basisInt (homKind 19 39) b := by decide
def polyRep19_40_0 : PolyHom 19 40 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_40 (b : Fin 3) : PolyHom 19 40 :=
  ![polyRep19_40_0,PolyHom.zero 19 40,PolyHom.zero 19 40] b
theorem polyLiftFree19_40 : ∀ b : Fin 3, (polyLift19_40 b).freeBlock=basisInt (homKind 19 40) b := by decide
def polyRep19_41_0 : PolyHom 19 41 where
  M := !![0,(mono6 (-1) 1),0,(mono6 (1) 0);0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_41 (b : Fin 3) : PolyHom 19 41 :=
  ![polyRep19_41_0,PolyHom.zero 19 41,PolyHom.zero 19 41] b
theorem polyLiftFree19_41 : ∀ b : Fin 3, (polyLift19_41 b).freeBlock=basisInt (homKind 19 41) b := by decide
def polyRep19_42_0 : PolyHom 19 42 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_42 (b : Fin 3) : PolyHom 19 42 :=
  ![polyRep19_42_0,PolyHom.zero 19 42,PolyHom.zero 19 42] b
theorem polyLiftFree19_42 : ∀ b : Fin 3, (polyLift19_42 b).freeBlock=basisInt (homKind 19 42) b := by decide
def polyRep19_43_0 : PolyHom 19 43 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_43 (b : Fin 3) : PolyHom 19 43 :=
  ![polyRep19_43_0,PolyHom.zero 19 43,PolyHom.zero 19 43] b
theorem polyLiftFree19_43 : ∀ b : Fin 3, (polyLift19_43 b).freeBlock=basisInt (homKind 19 43) b := by decide
def polyRep19_44_0 : PolyHom 19 44 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_44 (b : Fin 3) : PolyHom 19 44 :=
  ![polyRep19_44_0,PolyHom.zero 19 44,PolyHom.zero 19 44] b
theorem polyLiftFree19_44 : ∀ b : Fin 3, (polyLift19_44 b).freeBlock=basisInt (homKind 19 44) b := by decide
def polyRep19_45_0 : PolyHom 19 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift19_45 (b : Fin 3) : PolyHom 19 45 :=
  ![polyRep19_45_0,PolyHom.zero 19 45,PolyHom.zero 19 45] b
theorem polyLiftFree19_45 : ∀ b : Fin 3, (polyLift19_45 b).freeBlock=basisInt (homKind 19 45) b := by decide
def polyLift19_46 (b : Fin 3) : PolyHom 19 46 :=
  ![PolyHom.zero 19 46,PolyHom.zero 19 46,PolyHom.zero 19 46] b
theorem polyLiftFree19_46 : ∀ b : Fin 3, (polyLift19_46 b).freeBlock=basisInt (homKind 19 46) b := by decide
def polyLiftRow19 (j : Fin 47) (b : Fin 3) : PolyHom 19 j :=
  match j with
  | ⟨0,_⟩ => polyLift19_0 b
  | ⟨1,_⟩ => polyLift19_1 b
  | ⟨2,_⟩ => polyLift19_2 b
  | ⟨3,_⟩ => polyLift19_3 b
  | ⟨4,_⟩ => polyLift19_4 b
  | ⟨5,_⟩ => polyLift19_5 b
  | ⟨6,_⟩ => polyLift19_6 b
  | ⟨7,_⟩ => polyLift19_7 b
  | ⟨8,_⟩ => polyLift19_8 b
  | ⟨9,_⟩ => polyLift19_9 b
  | ⟨10,_⟩ => polyLift19_10 b
  | ⟨11,_⟩ => polyLift19_11 b
  | ⟨12,_⟩ => polyLift19_12 b
  | ⟨13,_⟩ => polyLift19_13 b
  | ⟨14,_⟩ => polyLift19_14 b
  | ⟨15,_⟩ => polyLift19_15 b
  | ⟨16,_⟩ => polyLift19_16 b
  | ⟨17,_⟩ => polyLift19_17 b
  | ⟨18,_⟩ => polyLift19_18 b
  | ⟨19,_⟩ => polyLift19_19 b
  | ⟨20,_⟩ => polyLift19_20 b
  | ⟨21,_⟩ => polyLift19_21 b
  | ⟨22,_⟩ => polyLift19_22 b
  | ⟨23,_⟩ => polyLift19_23 b
  | ⟨24,_⟩ => polyLift19_24 b
  | ⟨25,_⟩ => polyLift19_25 b
  | ⟨26,_⟩ => polyLift19_26 b
  | ⟨27,_⟩ => polyLift19_27 b
  | ⟨28,_⟩ => polyLift19_28 b
  | ⟨29,_⟩ => polyLift19_29 b
  | ⟨30,_⟩ => polyLift19_30 b
  | ⟨31,_⟩ => polyLift19_31 b
  | ⟨32,_⟩ => polyLift19_32 b
  | ⟨33,_⟩ => polyLift19_33 b
  | ⟨34,_⟩ => polyLift19_34 b
  | ⟨35,_⟩ => polyLift19_35 b
  | ⟨36,_⟩ => polyLift19_36 b
  | ⟨37,_⟩ => polyLift19_37 b
  | ⟨38,_⟩ => polyLift19_38 b
  | ⟨39,_⟩ => polyLift19_39 b
  | ⟨40,_⟩ => polyLift19_40 b
  | ⟨41,_⟩ => polyLift19_41 b
  | ⟨42,_⟩ => polyLift19_42 b
  | ⟨43,_⟩ => polyLift19_43 b
  | ⟨44,_⟩ => polyLift19_44 b
  | ⟨45,_⟩ => polyLift19_45 b
  | ⟨46,_⟩ => polyLift19_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree19 (j : Fin 47) (b : Fin 3) : (polyLiftRow19 j b).freeBlock=basisInt (homKind 19 j) b := by
  fin_cases j
  · exact polyLiftFree19_0 b
  · exact polyLiftFree19_1 b
  · exact polyLiftFree19_2 b
  · exact polyLiftFree19_3 b
  · exact polyLiftFree19_4 b
  · exact polyLiftFree19_5 b
  · exact polyLiftFree19_6 b
  · exact polyLiftFree19_7 b
  · exact polyLiftFree19_8 b
  · exact polyLiftFree19_9 b
  · exact polyLiftFree19_10 b
  · exact polyLiftFree19_11 b
  · exact polyLiftFree19_12 b
  · exact polyLiftFree19_13 b
  · exact polyLiftFree19_14 b
  · exact polyLiftFree19_15 b
  · exact polyLiftFree19_16 b
  · exact polyLiftFree19_17 b
  · exact polyLiftFree19_18 b
  · exact polyLiftFree19_19 b
  · exact polyLiftFree19_20 b
  · exact polyLiftFree19_21 b
  · exact polyLiftFree19_22 b
  · exact polyLiftFree19_23 b
  · exact polyLiftFree19_24 b
  · exact polyLiftFree19_25 b
  · exact polyLiftFree19_26 b
  · exact polyLiftFree19_27 b
  · exact polyLiftFree19_28 b
  · exact polyLiftFree19_29 b
  · exact polyLiftFree19_30 b
  · exact polyLiftFree19_31 b
  · exact polyLiftFree19_32 b
  · exact polyLiftFree19_33 b
  · exact polyLiftFree19_34 b
  · exact polyLiftFree19_35 b
  · exact polyLiftFree19_36 b
  · exact polyLiftFree19_37 b
  · exact polyLiftFree19_38 b
  · exact polyLiftFree19_39 b
  · exact polyLiftFree19_40 b
  · exact polyLiftFree19_41 b
  · exact polyLiftFree19_42 b
  · exact polyLiftFree19_43 b
  · exact polyLiftFree19_44 b
  · exact polyLiftFree19_45 b
  · exact polyLiftFree19_46 b
end UniserialComputations.N6
