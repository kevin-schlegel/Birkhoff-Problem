import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift23_0 (b : Fin 3) : PolyHom 23 0 :=
  ![PolyHom.zero 23 0,PolyHom.zero 23 0,PolyHom.zero 23 0] b
theorem polyLiftFree23_0 : ∀ b : Fin 3, (polyLift23_0 b).freeBlock=basisInt (homKind 23 0) b := by decide
def polyLift23_1 (b : Fin 3) : PolyHom 23 1 :=
  ![PolyHom.zero 23 1,PolyHom.zero 23 1,PolyHom.zero 23 1] b
theorem polyLiftFree23_1 : ∀ b : Fin 3, (polyLift23_1 b).freeBlock=basisInt (homKind 23 1) b := by decide
def polyLift23_2 (b : Fin 3) : PolyHom 23 2 :=
  ![PolyHom.zero 23 2,PolyHom.zero 23 2,PolyHom.zero 23 2] b
theorem polyLiftFree23_2 : ∀ b : Fin 3, (polyLift23_2 b).freeBlock=basisInt (homKind 23 2) b := by decide
def polyLift23_3 (b : Fin 3) : PolyHom 23 3 :=
  ![PolyHom.zero 23 3,PolyHom.zero 23 3,PolyHom.zero 23 3] b
theorem polyLiftFree23_3 : ∀ b : Fin 3, (polyLift23_3 b).freeBlock=basisInt (homKind 23 3) b := by decide
def polyLift23_4 (b : Fin 3) : PolyHom 23 4 :=
  ![PolyHom.zero 23 4,PolyHom.zero 23 4,PolyHom.zero 23 4] b
theorem polyLiftFree23_4 : ∀ b : Fin 3, (polyLift23_4 b).freeBlock=basisInt (homKind 23 4) b := by decide
def polyLift23_5 (b : Fin 3) : PolyHom 23 5 :=
  ![PolyHom.zero 23 5,PolyHom.zero 23 5,PolyHom.zero 23 5] b
theorem polyLiftFree23_5 : ∀ b : Fin 3, (polyLift23_5 b).freeBlock=basisInt (homKind 23 5) b := by decide
def polyLift23_6 (b : Fin 3) : PolyHom 23 6 :=
  ![PolyHom.zero 23 6,PolyHom.zero 23 6,PolyHom.zero 23 6] b
theorem polyLiftFree23_6 : ∀ b : Fin 3, (polyLift23_6 b).freeBlock=basisInt (homKind 23 6) b := by decide
def polyLift23_7 (b : Fin 3) : PolyHom 23 7 :=
  ![PolyHom.zero 23 7,PolyHom.zero 23 7,PolyHom.zero 23 7] b
theorem polyLiftFree23_7 : ∀ b : Fin 3, (polyLift23_7 b).freeBlock=basisInt (homKind 23 7) b := by decide
def polyLift23_8 (b : Fin 3) : PolyHom 23 8 :=
  ![PolyHom.zero 23 8,PolyHom.zero 23 8,PolyHom.zero 23 8] b
theorem polyLiftFree23_8 : ∀ b : Fin 3, (polyLift23_8 b).freeBlock=basisInt (homKind 23 8) b := by decide
def polyLift23_9 (b : Fin 3) : PolyHom 23 9 :=
  ![PolyHom.zero 23 9,PolyHom.zero 23 9,PolyHom.zero 23 9] b
theorem polyLiftFree23_9 : ∀ b : Fin 3, (polyLift23_9 b).freeBlock=basisInt (homKind 23 9) b := by decide
def polyRep23_10_0 : PolyHom 23 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_10 (b : Fin 3) : PolyHom 23 10 :=
  ![polyRep23_10_0,PolyHom.zero 23 10,PolyHom.zero 23 10] b
theorem polyLiftFree23_10 : ∀ b : Fin 3, (polyLift23_10 b).freeBlock=basisInt (homKind 23 10) b := by decide
def polyRep23_11_0 : PolyHom 23 11 where
  M := !![(mono6 (1) 3),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_11 (b : Fin 3) : PolyHom 23 11 :=
  ![polyRep23_11_0,PolyHom.zero 23 11,PolyHom.zero 23 11] b
theorem polyLiftFree23_11 : ∀ b : Fin 3, (polyLift23_11 b).freeBlock=basisInt (homKind 23 11) b := by decide
def polyRep23_12_0 : PolyHom 23 12 where
  M := !![(mono6 (1) 2),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_12 (b : Fin 3) : PolyHom 23 12 :=
  ![polyRep23_12_0,PolyHom.zero 23 12,PolyHom.zero 23 12] b
theorem polyLiftFree23_12 : ∀ b : Fin 3, (polyLift23_12 b).freeBlock=basisInt (homKind 23 12) b := by decide
def polyRep23_13_0 : PolyHom 23 13 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_13 (b : Fin 3) : PolyHom 23 13 :=
  ![polyRep23_13_0,PolyHom.zero 23 13,PolyHom.zero 23 13] b
theorem polyLiftFree23_13 : ∀ b : Fin 3, (polyLift23_13 b).freeBlock=basisInt (homKind 23 13) b := by decide
def polyLift23_14 (b : Fin 3) : PolyHom 23 14 :=
  ![PolyHom.zero 23 14,PolyHom.zero 23 14,PolyHom.zero 23 14] b
theorem polyLiftFree23_14 : ∀ b : Fin 3, (polyLift23_14 b).freeBlock=basisInt (homKind 23 14) b := by decide
def polyLift23_15 (b : Fin 3) : PolyHom 23 15 :=
  ![PolyHom.zero 23 15,PolyHom.zero 23 15,PolyHom.zero 23 15] b
theorem polyLiftFree23_15 : ∀ b : Fin 3, (polyLift23_15 b).freeBlock=basisInt (homKind 23 15) b := by decide
def polyLift23_16 (b : Fin 3) : PolyHom 23 16 :=
  ![PolyHom.zero 23 16,PolyHom.zero 23 16,PolyHom.zero 23 16] b
theorem polyLiftFree23_16 : ∀ b : Fin 3, (polyLift23_16 b).freeBlock=basisInt (homKind 23 16) b := by decide
def polyLift23_17 (b : Fin 3) : PolyHom 23 17 :=
  ![PolyHom.zero 23 17,PolyHom.zero 23 17,PolyHom.zero 23 17] b
theorem polyLiftFree23_17 : ∀ b : Fin 3, (polyLift23_17 b).freeBlock=basisInt (homKind 23 17) b := by decide
def polyLift23_18 (b : Fin 3) : PolyHom 23 18 :=
  ![PolyHom.zero 23 18,PolyHom.zero 23 18,PolyHom.zero 23 18] b
theorem polyLiftFree23_18 : ∀ b : Fin 3, (polyLift23_18 b).freeBlock=basisInt (homKind 23 18) b := by decide
def polyLift23_19 (b : Fin 3) : PolyHom 23 19 :=
  ![PolyHom.zero 23 19,PolyHom.zero 23 19,PolyHom.zero 23 19] b
theorem polyLiftFree23_19 : ∀ b : Fin 3, (polyLift23_19 b).freeBlock=basisInt (homKind 23 19) b := by decide
def polyLift23_20 (b : Fin 3) : PolyHom 23 20 :=
  ![PolyHom.zero 23 20,PolyHom.zero 23 20,PolyHom.zero 23 20] b
theorem polyLiftFree23_20 : ∀ b : Fin 3, (polyLift23_20 b).freeBlock=basisInt (homKind 23 20) b := by decide
def polyRep23_21_0 : PolyHom 23 21 where
  M := !![(mono6 (1) 2),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_21 (b : Fin 3) : PolyHom 23 21 :=
  ![polyRep23_21_0,PolyHom.zero 23 21,PolyHom.zero 23 21] b
theorem polyLiftFree23_21 : ∀ b : Fin 3, (polyLift23_21 b).freeBlock=basisInt (homKind 23 21) b := by decide
def polyRep23_22_0 : PolyHom 23 22 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_22 (b : Fin 3) : PolyHom 23 22 :=
  ![polyRep23_22_0,PolyHom.zero 23 22,PolyHom.zero 23 22] b
theorem polyLiftFree23_22 : ∀ b : Fin 3, (polyLift23_22 b).freeBlock=basisInt (homKind 23 22) b := by decide
def polyRep23_23_0 : PolyHom 23 23 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_23 (b : Fin 3) : PolyHom 23 23 :=
  ![polyRep23_23_0,PolyHom.zero 23 23,PolyHom.zero 23 23] b
theorem polyLiftFree23_23 : ∀ b : Fin 3, (polyLift23_23 b).freeBlock=basisInt (homKind 23 23) b := by decide
def polyRep23_24_0 : PolyHom 23 24 where
  M := !![(mono6 (1) 2),0,(mono6 (1) 1),0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_24 (b : Fin 3) : PolyHom 23 24 :=
  ![polyRep23_24_0,PolyHom.zero 23 24,PolyHom.zero 23 24] b
theorem polyLiftFree23_24 : ∀ b : Fin 3, (polyLift23_24 b).freeBlock=basisInt (homKind 23 24) b := by decide
def polyRep23_25_0 : PolyHom 23 25 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_25 (b : Fin 3) : PolyHom 23 25 :=
  ![polyRep23_25_0,PolyHom.zero 23 25,PolyHom.zero 23 25] b
theorem polyLiftFree23_25 : ∀ b : Fin 3, (polyLift23_25 b).freeBlock=basisInt (homKind 23 25) b := by decide
def polyRep23_26_0 : PolyHom 23 26 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_26 (b : Fin 3) : PolyHom 23 26 :=
  ![polyRep23_26_0,PolyHom.zero 23 26,PolyHom.zero 23 26] b
theorem polyLiftFree23_26 : ∀ b : Fin 3, (polyLift23_26 b).freeBlock=basisInt (homKind 23 26) b := by decide
def polyRep23_27_0 : PolyHom 23 27 where
  M := !![(mono6 (1) 1),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_27 (b : Fin 3) : PolyHom 23 27 :=
  ![polyRep23_27_0,PolyHom.zero 23 27,PolyHom.zero 23 27] b
theorem polyLiftFree23_27 : ∀ b : Fin 3, (polyLift23_27 b).freeBlock=basisInt (homKind 23 27) b := by decide
def polyRep23_28_0 : PolyHom 23 28 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_28 (b : Fin 3) : PolyHom 23 28 :=
  ![polyRep23_28_0,PolyHom.zero 23 28,PolyHom.zero 23 28] b
theorem polyLiftFree23_28 : ∀ b : Fin 3, (polyLift23_28 b).freeBlock=basisInt (homKind 23 28) b := by decide
def polyRep23_29_0 : PolyHom 23 29 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_29 (b : Fin 3) : PolyHom 23 29 :=
  ![polyRep23_29_0,PolyHom.zero 23 29,PolyHom.zero 23 29] b
theorem polyLiftFree23_29 : ∀ b : Fin 3, (polyLift23_29 b).freeBlock=basisInt (homKind 23 29) b := by decide
def polyRep23_30_0 : PolyHom 23 30 where
  M := !![(mono6 (1) 2),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_30 (b : Fin 3) : PolyHom 23 30 :=
  ![polyRep23_30_0,PolyHom.zero 23 30,PolyHom.zero 23 30] b
theorem polyLiftFree23_30 : ∀ b : Fin 3, (polyLift23_30 b).freeBlock=basisInt (homKind 23 30) b := by decide
def polyRep23_31_0 : PolyHom 23 31 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_31 (b : Fin 3) : PolyHom 23 31 :=
  ![polyRep23_31_0,PolyHom.zero 23 31,PolyHom.zero 23 31] b
theorem polyLiftFree23_31 : ∀ b : Fin 3, (polyLift23_31 b).freeBlock=basisInt (homKind 23 31) b := by decide
def polyRep23_32_0 : PolyHom 23 32 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_32 (b : Fin 3) : PolyHom 23 32 :=
  ![polyRep23_32_0,PolyHom.zero 23 32,PolyHom.zero 23 32] b
theorem polyLiftFree23_32 : ∀ b : Fin 3, (polyLift23_32 b).freeBlock=basisInt (homKind 23 32) b := by decide
def polyRep23_33_0 : PolyHom 23 33 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_33 (b : Fin 3) : PolyHom 23 33 :=
  ![polyRep23_33_0,PolyHom.zero 23 33,PolyHom.zero 23 33] b
theorem polyLiftFree23_33 : ∀ b : Fin 3, (polyLift23_33 b).freeBlock=basisInt (homKind 23 33) b := by decide
def polyRep23_34_0 : PolyHom 23 34 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_34 (b : Fin 3) : PolyHom 23 34 :=
  ![polyRep23_34_0,PolyHom.zero 23 34,PolyHom.zero 23 34] b
theorem polyLiftFree23_34 : ∀ b : Fin 3, (polyLift23_34 b).freeBlock=basisInt (homKind 23 34) b := by decide
def polyRep23_35_0 : PolyHom 23 35 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_35 (b : Fin 3) : PolyHom 23 35 :=
  ![polyRep23_35_0,PolyHom.zero 23 35,PolyHom.zero 23 35] b
theorem polyLiftFree23_35 : ∀ b : Fin 3, (polyLift23_35 b).freeBlock=basisInt (homKind 23 35) b := by decide
def polyRep23_36_0 : PolyHom 23 36 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_36 (b : Fin 3) : PolyHom 23 36 :=
  ![polyRep23_36_0,PolyHom.zero 23 36,PolyHom.zero 23 36] b
theorem polyLiftFree23_36 : ∀ b : Fin 3, (polyLift23_36 b).freeBlock=basisInt (homKind 23 36) b := by decide
def polyRep23_37_0 : PolyHom 23 37 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_37 (b : Fin 3) : PolyHom 23 37 :=
  ![polyRep23_37_0,PolyHom.zero 23 37,PolyHom.zero 23 37] b
theorem polyLiftFree23_37 : ∀ b : Fin 3, (polyLift23_37 b).freeBlock=basisInt (homKind 23 37) b := by decide
def polyRep23_38_0 : PolyHom 23 38 where
  M := !![(mono6 (1) 1),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_38 (b : Fin 3) : PolyHom 23 38 :=
  ![polyRep23_38_0,PolyHom.zero 23 38,PolyHom.zero 23 38] b
theorem polyLiftFree23_38 : ∀ b : Fin 3, (polyLift23_38 b).freeBlock=basisInt (homKind 23 38) b := by decide
def polyRep23_39_0 : PolyHom 23 39 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_39 (b : Fin 3) : PolyHom 23 39 :=
  ![polyRep23_39_0,PolyHom.zero 23 39,PolyHom.zero 23 39] b
theorem polyLiftFree23_39 : ∀ b : Fin 3, (polyLift23_39 b).freeBlock=basisInt (homKind 23 39) b := by decide
def polyRep23_40_0 : PolyHom 23 40 where
  M := !![(mono6 (1) 1),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_40 (b : Fin 3) : PolyHom 23 40 :=
  ![polyRep23_40_0,PolyHom.zero 23 40,PolyHom.zero 23 40] b
theorem polyLiftFree23_40 : ∀ b : Fin 3, (polyLift23_40 b).freeBlock=basisInt (homKind 23 40) b := by decide
def polyRep23_41_0 : PolyHom 23 41 where
  M := !![(mono6 (1) 0),0,0,(mono6 (1) 0);0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_41 (b : Fin 3) : PolyHom 23 41 :=
  ![polyRep23_41_0,PolyHom.zero 23 41,PolyHom.zero 23 41] b
theorem polyLiftFree23_41 : ∀ b : Fin 3, (polyLift23_41 b).freeBlock=basisInt (homKind 23 41) b := by decide
def polyRep23_42_0 : PolyHom 23 42 where
  M := !![0,(mono6 (1) 2),0,0;0,0,(mono6 (1) 0),(mono6 (-1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (-1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_42 (b : Fin 3) : PolyHom 23 42 :=
  ![polyRep23_42_0,PolyHom.zero 23 42,PolyHom.zero 23 42] b
theorem polyLiftFree23_42 : ∀ b : Fin 3, (polyLift23_42 b).freeBlock=basisInt (homKind 23 42) b := by decide
def polyRep23_43_0 : PolyHom 23 43 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_43 (b : Fin 3) : PolyHom 23 43 :=
  ![polyRep23_43_0,PolyHom.zero 23 43,PolyHom.zero 23 43] b
theorem polyLiftFree23_43 : ∀ b : Fin 3, (polyLift23_43 b).freeBlock=basisInt (homKind 23 43) b := by decide
def polyRep23_44_0 : PolyHom 23 44 where
  M := !![(mono6 (1) 1),(mono6 (1) 2),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep23_44_1 : PolyHom 23 44 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0]
  U := !![0,(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_44 (b : Fin 3) : PolyHom 23 44 :=
  ![polyRep23_44_0,polyRep23_44_1,PolyHom.zero 23 44] b
theorem polyLiftFree23_44 : ∀ b : Fin 3, (polyLift23_44 b).freeBlock=basisInt (homKind 23 44) b := by decide
def polyRep23_45_0 : PolyHom 23 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift23_45 (b : Fin 3) : PolyHom 23 45 :=
  ![polyRep23_45_0,PolyHom.zero 23 45,PolyHom.zero 23 45] b
theorem polyLiftFree23_45 : ∀ b : Fin 3, (polyLift23_45 b).freeBlock=basisInt (homKind 23 45) b := by decide
def polyLift23_46 (b : Fin 3) : PolyHom 23 46 :=
  ![PolyHom.zero 23 46,PolyHom.zero 23 46,PolyHom.zero 23 46] b
theorem polyLiftFree23_46 : ∀ b : Fin 3, (polyLift23_46 b).freeBlock=basisInt (homKind 23 46) b := by decide
def polyLiftRow23 (j : Fin 47) (b : Fin 3) : PolyHom 23 j :=
  match j with
  | ⟨0,_⟩ => polyLift23_0 b
  | ⟨1,_⟩ => polyLift23_1 b
  | ⟨2,_⟩ => polyLift23_2 b
  | ⟨3,_⟩ => polyLift23_3 b
  | ⟨4,_⟩ => polyLift23_4 b
  | ⟨5,_⟩ => polyLift23_5 b
  | ⟨6,_⟩ => polyLift23_6 b
  | ⟨7,_⟩ => polyLift23_7 b
  | ⟨8,_⟩ => polyLift23_8 b
  | ⟨9,_⟩ => polyLift23_9 b
  | ⟨10,_⟩ => polyLift23_10 b
  | ⟨11,_⟩ => polyLift23_11 b
  | ⟨12,_⟩ => polyLift23_12 b
  | ⟨13,_⟩ => polyLift23_13 b
  | ⟨14,_⟩ => polyLift23_14 b
  | ⟨15,_⟩ => polyLift23_15 b
  | ⟨16,_⟩ => polyLift23_16 b
  | ⟨17,_⟩ => polyLift23_17 b
  | ⟨18,_⟩ => polyLift23_18 b
  | ⟨19,_⟩ => polyLift23_19 b
  | ⟨20,_⟩ => polyLift23_20 b
  | ⟨21,_⟩ => polyLift23_21 b
  | ⟨22,_⟩ => polyLift23_22 b
  | ⟨23,_⟩ => polyLift23_23 b
  | ⟨24,_⟩ => polyLift23_24 b
  | ⟨25,_⟩ => polyLift23_25 b
  | ⟨26,_⟩ => polyLift23_26 b
  | ⟨27,_⟩ => polyLift23_27 b
  | ⟨28,_⟩ => polyLift23_28 b
  | ⟨29,_⟩ => polyLift23_29 b
  | ⟨30,_⟩ => polyLift23_30 b
  | ⟨31,_⟩ => polyLift23_31 b
  | ⟨32,_⟩ => polyLift23_32 b
  | ⟨33,_⟩ => polyLift23_33 b
  | ⟨34,_⟩ => polyLift23_34 b
  | ⟨35,_⟩ => polyLift23_35 b
  | ⟨36,_⟩ => polyLift23_36 b
  | ⟨37,_⟩ => polyLift23_37 b
  | ⟨38,_⟩ => polyLift23_38 b
  | ⟨39,_⟩ => polyLift23_39 b
  | ⟨40,_⟩ => polyLift23_40 b
  | ⟨41,_⟩ => polyLift23_41 b
  | ⟨42,_⟩ => polyLift23_42 b
  | ⟨43,_⟩ => polyLift23_43 b
  | ⟨44,_⟩ => polyLift23_44 b
  | ⟨45,_⟩ => polyLift23_45 b
  | ⟨46,_⟩ => polyLift23_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree23 (j : Fin 47) (b : Fin 3) : (polyLiftRow23 j b).freeBlock=basisInt (homKind 23 j) b := by
  fin_cases j
  · exact polyLiftFree23_0 b
  · exact polyLiftFree23_1 b
  · exact polyLiftFree23_2 b
  · exact polyLiftFree23_3 b
  · exact polyLiftFree23_4 b
  · exact polyLiftFree23_5 b
  · exact polyLiftFree23_6 b
  · exact polyLiftFree23_7 b
  · exact polyLiftFree23_8 b
  · exact polyLiftFree23_9 b
  · exact polyLiftFree23_10 b
  · exact polyLiftFree23_11 b
  · exact polyLiftFree23_12 b
  · exact polyLiftFree23_13 b
  · exact polyLiftFree23_14 b
  · exact polyLiftFree23_15 b
  · exact polyLiftFree23_16 b
  · exact polyLiftFree23_17 b
  · exact polyLiftFree23_18 b
  · exact polyLiftFree23_19 b
  · exact polyLiftFree23_20 b
  · exact polyLiftFree23_21 b
  · exact polyLiftFree23_22 b
  · exact polyLiftFree23_23 b
  · exact polyLiftFree23_24 b
  · exact polyLiftFree23_25 b
  · exact polyLiftFree23_26 b
  · exact polyLiftFree23_27 b
  · exact polyLiftFree23_28 b
  · exact polyLiftFree23_29 b
  · exact polyLiftFree23_30 b
  · exact polyLiftFree23_31 b
  · exact polyLiftFree23_32 b
  · exact polyLiftFree23_33 b
  · exact polyLiftFree23_34 b
  · exact polyLiftFree23_35 b
  · exact polyLiftFree23_36 b
  · exact polyLiftFree23_37 b
  · exact polyLiftFree23_38 b
  · exact polyLiftFree23_39 b
  · exact polyLiftFree23_40 b
  · exact polyLiftFree23_41 b
  · exact polyLiftFree23_42 b
  · exact polyLiftFree23_43 b
  · exact polyLiftFree23_44 b
  · exact polyLiftFree23_45 b
  · exact polyLiftFree23_46 b
end UniserialComputations.N6
