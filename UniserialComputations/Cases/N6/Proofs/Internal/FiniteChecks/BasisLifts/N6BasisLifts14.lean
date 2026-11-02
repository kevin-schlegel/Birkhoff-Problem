import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift14_0 (b : Fin 3) : PolyHom 14 0 :=
  ![PolyHom.zero 14 0,PolyHom.zero 14 0,PolyHom.zero 14 0] b
theorem polyLiftFree14_0 : ∀ b : Fin 3, (polyLift14_0 b).freeBlock=basisInt (homKind 14 0) b := by decide
def polyLift14_1 (b : Fin 3) : PolyHom 14 1 :=
  ![PolyHom.zero 14 1,PolyHom.zero 14 1,PolyHom.zero 14 1] b
theorem polyLiftFree14_1 : ∀ b : Fin 3, (polyLift14_1 b).freeBlock=basisInt (homKind 14 1) b := by decide
def polyLift14_2 (b : Fin 3) : PolyHom 14 2 :=
  ![PolyHom.zero 14 2,PolyHom.zero 14 2,PolyHom.zero 14 2] b
theorem polyLiftFree14_2 : ∀ b : Fin 3, (polyLift14_2 b).freeBlock=basisInt (homKind 14 2) b := by decide
def polyLift14_3 (b : Fin 3) : PolyHom 14 3 :=
  ![PolyHom.zero 14 3,PolyHom.zero 14 3,PolyHom.zero 14 3] b
theorem polyLiftFree14_3 : ∀ b : Fin 3, (polyLift14_3 b).freeBlock=basisInt (homKind 14 3) b := by decide
def polyLift14_4 (b : Fin 3) : PolyHom 14 4 :=
  ![PolyHom.zero 14 4,PolyHom.zero 14 4,PolyHom.zero 14 4] b
theorem polyLiftFree14_4 : ∀ b : Fin 3, (polyLift14_4 b).freeBlock=basisInt (homKind 14 4) b := by decide
def polyLift14_5 (b : Fin 3) : PolyHom 14 5 :=
  ![PolyHom.zero 14 5,PolyHom.zero 14 5,PolyHom.zero 14 5] b
theorem polyLiftFree14_5 : ∀ b : Fin 3, (polyLift14_5 b).freeBlock=basisInt (homKind 14 5) b := by decide
def polyLift14_6 (b : Fin 3) : PolyHom 14 6 :=
  ![PolyHom.zero 14 6,PolyHom.zero 14 6,PolyHom.zero 14 6] b
theorem polyLiftFree14_6 : ∀ b : Fin 3, (polyLift14_6 b).freeBlock=basisInt (homKind 14 6) b := by decide
def polyLift14_7 (b : Fin 3) : PolyHom 14 7 :=
  ![PolyHom.zero 14 7,PolyHom.zero 14 7,PolyHom.zero 14 7] b
theorem polyLiftFree14_7 : ∀ b : Fin 3, (polyLift14_7 b).freeBlock=basisInt (homKind 14 7) b := by decide
def polyLift14_8 (b : Fin 3) : PolyHom 14 8 :=
  ![PolyHom.zero 14 8,PolyHom.zero 14 8,PolyHom.zero 14 8] b
theorem polyLiftFree14_8 : ∀ b : Fin 3, (polyLift14_8 b).freeBlock=basisInt (homKind 14 8) b := by decide
def polyLift14_9 (b : Fin 3) : PolyHom 14 9 :=
  ![PolyHom.zero 14 9,PolyHom.zero 14 9,PolyHom.zero 14 9] b
theorem polyLiftFree14_9 : ∀ b : Fin 3, (polyLift14_9 b).freeBlock=basisInt (homKind 14 9) b := by decide
def polyRep14_10_0 : PolyHom 14 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 4),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_10 (b : Fin 3) : PolyHom 14 10 :=
  ![polyRep14_10_0,PolyHom.zero 14 10,PolyHom.zero 14 10] b
theorem polyLiftFree14_10 : ∀ b : Fin 3, (polyLift14_10 b).freeBlock=basisInt (homKind 14 10) b := by decide
def polyRep14_11_0 : PolyHom 14 11 where
  M := !![(mono6 (1) 3),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_11 (b : Fin 3) : PolyHom 14 11 :=
  ![polyRep14_11_0,PolyHom.zero 14 11,PolyHom.zero 14 11] b
theorem polyLiftFree14_11 : ∀ b : Fin 3, (polyLift14_11 b).freeBlock=basisInt (homKind 14 11) b := by decide
def polyRep14_12_0 : PolyHom 14 12 where
  M := !![(mono6 (1) 2),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_12 (b : Fin 3) : PolyHom 14 12 :=
  ![polyRep14_12_0,PolyHom.zero 14 12,PolyHom.zero 14 12] b
theorem polyLiftFree14_12 : ∀ b : Fin 3, (polyLift14_12 b).freeBlock=basisInt (homKind 14 12) b := by decide
def polyRep14_13_0 : PolyHom 14 13 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_13 (b : Fin 3) : PolyHom 14 13 :=
  ![polyRep14_13_0,PolyHom.zero 14 13,PolyHom.zero 14 13] b
theorem polyLiftFree14_13 : ∀ b : Fin 3, (polyLift14_13 b).freeBlock=basisInt (homKind 14 13) b := by decide
def polyRep14_14_0 : PolyHom 14 14 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_14 (b : Fin 3) : PolyHom 14 14 :=
  ![polyRep14_14_0,PolyHom.zero 14 14,PolyHom.zero 14 14] b
theorem polyLiftFree14_14 : ∀ b : Fin 3, (polyLift14_14 b).freeBlock=basisInt (homKind 14 14) b := by decide
def polyLift14_15 (b : Fin 3) : PolyHom 14 15 :=
  ![PolyHom.zero 14 15,PolyHom.zero 14 15,PolyHom.zero 14 15] b
theorem polyLiftFree14_15 : ∀ b : Fin 3, (polyLift14_15 b).freeBlock=basisInt (homKind 14 15) b := by decide
def polyLift14_16 (b : Fin 3) : PolyHom 14 16 :=
  ![PolyHom.zero 14 16,PolyHom.zero 14 16,PolyHom.zero 14 16] b
theorem polyLiftFree14_16 : ∀ b : Fin 3, (polyLift14_16 b).freeBlock=basisInt (homKind 14 16) b := by decide
def polyLift14_17 (b : Fin 3) : PolyHom 14 17 :=
  ![PolyHom.zero 14 17,PolyHom.zero 14 17,PolyHom.zero 14 17] b
theorem polyLiftFree14_17 : ∀ b : Fin 3, (polyLift14_17 b).freeBlock=basisInt (homKind 14 17) b := by decide
def polyLift14_18 (b : Fin 3) : PolyHom 14 18 :=
  ![PolyHom.zero 14 18,PolyHom.zero 14 18,PolyHom.zero 14 18] b
theorem polyLiftFree14_18 : ∀ b : Fin 3, (polyLift14_18 b).freeBlock=basisInt (homKind 14 18) b := by decide
def polyLift14_19 (b : Fin 3) : PolyHom 14 19 :=
  ![PolyHom.zero 14 19,PolyHom.zero 14 19,PolyHom.zero 14 19] b
theorem polyLiftFree14_19 : ∀ b : Fin 3, (polyLift14_19 b).freeBlock=basisInt (homKind 14 19) b := by decide
def polyLift14_20 (b : Fin 3) : PolyHom 14 20 :=
  ![PolyHom.zero 14 20,PolyHom.zero 14 20,PolyHom.zero 14 20] b
theorem polyLiftFree14_20 : ∀ b : Fin 3, (polyLift14_20 b).freeBlock=basisInt (homKind 14 20) b := by decide
def polyRep14_21_0 : PolyHom 14 21 where
  M := !![(mono6 (1) 2),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_21 (b : Fin 3) : PolyHom 14 21 :=
  ![polyRep14_21_0,PolyHom.zero 14 21,PolyHom.zero 14 21] b
theorem polyLiftFree14_21 : ∀ b : Fin 3, (polyLift14_21 b).freeBlock=basisInt (homKind 14 21) b := by decide
def polyRep14_22_0 : PolyHom 14 22 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_22 (b : Fin 3) : PolyHom 14 22 :=
  ![polyRep14_22_0,PolyHom.zero 14 22,PolyHom.zero 14 22] b
theorem polyLiftFree14_22 : ∀ b : Fin 3, (polyLift14_22 b).freeBlock=basisInt (homKind 14 22) b := by decide
def polyRep14_23_0 : PolyHom 14 23 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_23 (b : Fin 3) : PolyHom 14 23 :=
  ![polyRep14_23_0,PolyHom.zero 14 23,PolyHom.zero 14 23] b
theorem polyLiftFree14_23 : ∀ b : Fin 3, (polyLift14_23 b).freeBlock=basisInt (homKind 14 23) b := by decide
def polyRep14_24_0 : PolyHom 14 24 where
  M := !![(mono6 (1) 2),0,0,0;0,(mono6 (1) 0),(mono6 (1) 2),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),(mono6 (1) 2);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_24 (b : Fin 3) : PolyHom 14 24 :=
  ![polyRep14_24_0,PolyHom.zero 14 24,PolyHom.zero 14 24] b
theorem polyLiftFree14_24 : ∀ b : Fin 3, (polyLift14_24 b).freeBlock=basisInt (homKind 14 24) b := by decide
def polyRep14_25_0 : PolyHom 14 25 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_25 (b : Fin 3) : PolyHom 14 25 :=
  ![polyRep14_25_0,PolyHom.zero 14 25,PolyHom.zero 14 25] b
theorem polyLiftFree14_25 : ∀ b : Fin 3, (polyLift14_25 b).freeBlock=basisInt (homKind 14 25) b := by decide
def polyRep14_26_0 : PolyHom 14 26 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_26 (b : Fin 3) : PolyHom 14 26 :=
  ![polyRep14_26_0,PolyHom.zero 14 26,PolyHom.zero 14 26] b
theorem polyLiftFree14_26 : ∀ b : Fin 3, (polyLift14_26 b).freeBlock=basisInt (homKind 14 26) b := by decide
def polyRep14_27_0 : PolyHom 14 27 where
  M := !![(mono6 (1) 1),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_27 (b : Fin 3) : PolyHom 14 27 :=
  ![polyRep14_27_0,PolyHom.zero 14 27,PolyHom.zero 14 27] b
theorem polyLiftFree14_27 : ∀ b : Fin 3, (polyLift14_27 b).freeBlock=basisInt (homKind 14 27) b := by decide
def polyRep14_28_0 : PolyHom 14 28 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_28 (b : Fin 3) : PolyHom 14 28 :=
  ![polyRep14_28_0,PolyHom.zero 14 28,PolyHom.zero 14 28] b
theorem polyLiftFree14_28 : ∀ b : Fin 3, (polyLift14_28 b).freeBlock=basisInt (homKind 14 28) b := by decide
def polyRep14_29_0 : PolyHom 14 29 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_29 (b : Fin 3) : PolyHom 14 29 :=
  ![polyRep14_29_0,PolyHom.zero 14 29,PolyHom.zero 14 29] b
theorem polyLiftFree14_29 : ∀ b : Fin 3, (polyLift14_29 b).freeBlock=basisInt (homKind 14 29) b := by decide
def polyRep14_30_0 : PolyHom 14 30 where
  M := !![(mono6 (1) 2),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),(mono6 (1) 2);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_30 (b : Fin 3) : PolyHom 14 30 :=
  ![polyRep14_30_0,PolyHom.zero 14 30,PolyHom.zero 14 30] b
theorem polyLiftFree14_30 : ∀ b : Fin 3, (polyLift14_30 b).freeBlock=basisInt (homKind 14 30) b := by decide
def polyRep14_31_0 : PolyHom 14 31 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_31 (b : Fin 3) : PolyHom 14 31 :=
  ![polyRep14_31_0,PolyHom.zero 14 31,PolyHom.zero 14 31] b
theorem polyLiftFree14_31 : ∀ b : Fin 3, (polyLift14_31 b).freeBlock=basisInt (homKind 14 31) b := by decide
def polyRep14_32_0 : PolyHom 14 32 where
  M := !![(mono6 (1) 1),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_32 (b : Fin 3) : PolyHom 14 32 :=
  ![polyRep14_32_0,PolyHom.zero 14 32,PolyHom.zero 14 32] b
theorem polyLiftFree14_32 : ∀ b : Fin 3, (polyLift14_32 b).freeBlock=basisInt (homKind 14 32) b := by decide
def polyRep14_33_0 : PolyHom 14 33 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_33 (b : Fin 3) : PolyHom 14 33 :=
  ![polyRep14_33_0,PolyHom.zero 14 33,PolyHom.zero 14 33] b
theorem polyLiftFree14_33 : ∀ b : Fin 3, (polyLift14_33 b).freeBlock=basisInt (homKind 14 33) b := by decide
def polyRep14_34_0 : PolyHom 14 34 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_34 (b : Fin 3) : PolyHom 14 34 :=
  ![polyRep14_34_0,PolyHom.zero 14 34,PolyHom.zero 14 34] b
theorem polyLiftFree14_34 : ∀ b : Fin 3, (polyLift14_34 b).freeBlock=basisInt (homKind 14 34) b := by decide
def polyRep14_35_0 : PolyHom 14 35 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_35 (b : Fin 3) : PolyHom 14 35 :=
  ![polyRep14_35_0,PolyHom.zero 14 35,PolyHom.zero 14 35] b
theorem polyLiftFree14_35 : ∀ b : Fin 3, (polyLift14_35 b).freeBlock=basisInt (homKind 14 35) b := by decide
def polyRep14_36_0 : PolyHom 14 36 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_36 (b : Fin 3) : PolyHom 14 36 :=
  ![polyRep14_36_0,PolyHom.zero 14 36,PolyHom.zero 14 36] b
theorem polyLiftFree14_36 : ∀ b : Fin 3, (polyLift14_36 b).freeBlock=basisInt (homKind 14 36) b := by decide
def polyRep14_37_0 : PolyHom 14 37 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),(mono6 (1) 2);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_37 (b : Fin 3) : PolyHom 14 37 :=
  ![polyRep14_37_0,PolyHom.zero 14 37,PolyHom.zero 14 37] b
theorem polyLiftFree14_37 : ∀ b : Fin 3, (polyLift14_37 b).freeBlock=basisInt (homKind 14 37) b := by decide
def polyRep14_38_0 : PolyHom 14 38 where
  M := !![(mono6 (1) 1),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 2);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_38 (b : Fin 3) : PolyHom 14 38 :=
  ![polyRep14_38_0,PolyHom.zero 14 38,PolyHom.zero 14 38] b
theorem polyLiftFree14_38 : ∀ b : Fin 3, (polyLift14_38 b).freeBlock=basisInt (homKind 14 38) b := by decide
def polyRep14_39_0 : PolyHom 14 39 where
  M := !![(mono6 (1) 1),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_39 (b : Fin 3) : PolyHom 14 39 :=
  ![polyRep14_39_0,PolyHom.zero 14 39,PolyHom.zero 14 39] b
theorem polyLiftFree14_39 : ∀ b : Fin 3, (polyLift14_39 b).freeBlock=basisInt (homKind 14 39) b := by decide
def polyRep14_40_0 : PolyHom 14 40 where
  M := !![(mono6 (1) 1),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),(mono6 (1) 2);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_40 (b : Fin 3) : PolyHom 14 40 :=
  ![polyRep14_40_0,PolyHom.zero 14 40,PolyHom.zero 14 40] b
theorem polyLiftFree14_40 : ∀ b : Fin 3, (polyLift14_40 b).freeBlock=basisInt (homKind 14 40) b := by decide
def polyRep14_41_0 : PolyHom 14 41 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_41 (b : Fin 3) : PolyHom 14 41 :=
  ![polyRep14_41_0,PolyHom.zero 14 41,PolyHom.zero 14 41] b
theorem polyLiftFree14_41 : ∀ b : Fin 3, (polyLift14_41 b).freeBlock=basisInt (homKind 14 41) b := by decide
def polyRep14_42_0 : PolyHom 14 42 where
  M := !![0,(mono6 (1) 2),0,0;0,0,(mono6 (1) 0),(mono6 (-1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),(mono6 (-1) 2);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_42 (b : Fin 3) : PolyHom 14 42 :=
  ![polyRep14_42_0,PolyHom.zero 14 42,PolyHom.zero 14 42] b
theorem polyLiftFree14_42 : ∀ b : Fin 3, (polyLift14_42 b).freeBlock=basisInt (homKind 14 42) b := by decide
def polyRep14_43_0 : PolyHom 14 43 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_43 (b : Fin 3) : PolyHom 14 43 :=
  ![polyRep14_43_0,PolyHom.zero 14 43,PolyHom.zero 14 43] b
theorem polyLiftFree14_43 : ∀ b : Fin 3, (polyLift14_43 b).freeBlock=basisInt (homKind 14 43) b := by decide
def polyRep14_44_0 : PolyHom 14 44 where
  M := !![(mono6 (1) 1),(mono6 (1) 2),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep14_44_1 : PolyHom 14 44 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_44 (b : Fin 3) : PolyHom 14 44 :=
  ![polyRep14_44_0,polyRep14_44_1,PolyHom.zero 14 44] b
theorem polyLiftFree14_44 : ∀ b : Fin 3, (polyLift14_44 b).freeBlock=basisInt (homKind 14 44) b := by decide
def polyRep14_45_0 : PolyHom 14 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift14_45 (b : Fin 3) : PolyHom 14 45 :=
  ![polyRep14_45_0,PolyHom.zero 14 45,PolyHom.zero 14 45] b
theorem polyLiftFree14_45 : ∀ b : Fin 3, (polyLift14_45 b).freeBlock=basisInt (homKind 14 45) b := by decide
def polyLift14_46 (b : Fin 3) : PolyHom 14 46 :=
  ![PolyHom.zero 14 46,PolyHom.zero 14 46,PolyHom.zero 14 46] b
theorem polyLiftFree14_46 : ∀ b : Fin 3, (polyLift14_46 b).freeBlock=basisInt (homKind 14 46) b := by decide
def polyLiftRow14 (j : Fin 47) (b : Fin 3) : PolyHom 14 j :=
  match j with
  | ⟨0,_⟩ => polyLift14_0 b
  | ⟨1,_⟩ => polyLift14_1 b
  | ⟨2,_⟩ => polyLift14_2 b
  | ⟨3,_⟩ => polyLift14_3 b
  | ⟨4,_⟩ => polyLift14_4 b
  | ⟨5,_⟩ => polyLift14_5 b
  | ⟨6,_⟩ => polyLift14_6 b
  | ⟨7,_⟩ => polyLift14_7 b
  | ⟨8,_⟩ => polyLift14_8 b
  | ⟨9,_⟩ => polyLift14_9 b
  | ⟨10,_⟩ => polyLift14_10 b
  | ⟨11,_⟩ => polyLift14_11 b
  | ⟨12,_⟩ => polyLift14_12 b
  | ⟨13,_⟩ => polyLift14_13 b
  | ⟨14,_⟩ => polyLift14_14 b
  | ⟨15,_⟩ => polyLift14_15 b
  | ⟨16,_⟩ => polyLift14_16 b
  | ⟨17,_⟩ => polyLift14_17 b
  | ⟨18,_⟩ => polyLift14_18 b
  | ⟨19,_⟩ => polyLift14_19 b
  | ⟨20,_⟩ => polyLift14_20 b
  | ⟨21,_⟩ => polyLift14_21 b
  | ⟨22,_⟩ => polyLift14_22 b
  | ⟨23,_⟩ => polyLift14_23 b
  | ⟨24,_⟩ => polyLift14_24 b
  | ⟨25,_⟩ => polyLift14_25 b
  | ⟨26,_⟩ => polyLift14_26 b
  | ⟨27,_⟩ => polyLift14_27 b
  | ⟨28,_⟩ => polyLift14_28 b
  | ⟨29,_⟩ => polyLift14_29 b
  | ⟨30,_⟩ => polyLift14_30 b
  | ⟨31,_⟩ => polyLift14_31 b
  | ⟨32,_⟩ => polyLift14_32 b
  | ⟨33,_⟩ => polyLift14_33 b
  | ⟨34,_⟩ => polyLift14_34 b
  | ⟨35,_⟩ => polyLift14_35 b
  | ⟨36,_⟩ => polyLift14_36 b
  | ⟨37,_⟩ => polyLift14_37 b
  | ⟨38,_⟩ => polyLift14_38 b
  | ⟨39,_⟩ => polyLift14_39 b
  | ⟨40,_⟩ => polyLift14_40 b
  | ⟨41,_⟩ => polyLift14_41 b
  | ⟨42,_⟩ => polyLift14_42 b
  | ⟨43,_⟩ => polyLift14_43 b
  | ⟨44,_⟩ => polyLift14_44 b
  | ⟨45,_⟩ => polyLift14_45 b
  | ⟨46,_⟩ => polyLift14_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree14 (j : Fin 47) (b : Fin 3) : (polyLiftRow14 j b).freeBlock=basisInt (homKind 14 j) b := by
  fin_cases j
  · exact polyLiftFree14_0 b
  · exact polyLiftFree14_1 b
  · exact polyLiftFree14_2 b
  · exact polyLiftFree14_3 b
  · exact polyLiftFree14_4 b
  · exact polyLiftFree14_5 b
  · exact polyLiftFree14_6 b
  · exact polyLiftFree14_7 b
  · exact polyLiftFree14_8 b
  · exact polyLiftFree14_9 b
  · exact polyLiftFree14_10 b
  · exact polyLiftFree14_11 b
  · exact polyLiftFree14_12 b
  · exact polyLiftFree14_13 b
  · exact polyLiftFree14_14 b
  · exact polyLiftFree14_15 b
  · exact polyLiftFree14_16 b
  · exact polyLiftFree14_17 b
  · exact polyLiftFree14_18 b
  · exact polyLiftFree14_19 b
  · exact polyLiftFree14_20 b
  · exact polyLiftFree14_21 b
  · exact polyLiftFree14_22 b
  · exact polyLiftFree14_23 b
  · exact polyLiftFree14_24 b
  · exact polyLiftFree14_25 b
  · exact polyLiftFree14_26 b
  · exact polyLiftFree14_27 b
  · exact polyLiftFree14_28 b
  · exact polyLiftFree14_29 b
  · exact polyLiftFree14_30 b
  · exact polyLiftFree14_31 b
  · exact polyLiftFree14_32 b
  · exact polyLiftFree14_33 b
  · exact polyLiftFree14_34 b
  · exact polyLiftFree14_35 b
  · exact polyLiftFree14_36 b
  · exact polyLiftFree14_37 b
  · exact polyLiftFree14_38 b
  · exact polyLiftFree14_39 b
  · exact polyLiftFree14_40 b
  · exact polyLiftFree14_41 b
  · exact polyLiftFree14_42 b
  · exact polyLiftFree14_43 b
  · exact polyLiftFree14_44 b
  · exact polyLiftFree14_45 b
  · exact polyLiftFree14_46 b
end UniserialComputations.N6
