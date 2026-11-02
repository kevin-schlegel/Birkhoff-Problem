import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift35_0 (b : Fin 3) : PolyHom 35 0 :=
  ![PolyHom.zero 35 0,PolyHom.zero 35 0,PolyHom.zero 35 0] b
theorem polyLiftFree35_0 : ∀ b : Fin 3, (polyLift35_0 b).freeBlock=basisInt (homKind 35 0) b := by decide
def polyLift35_1 (b : Fin 3) : PolyHom 35 1 :=
  ![PolyHom.zero 35 1,PolyHom.zero 35 1,PolyHom.zero 35 1] b
theorem polyLiftFree35_1 : ∀ b : Fin 3, (polyLift35_1 b).freeBlock=basisInt (homKind 35 1) b := by decide
def polyLift35_2 (b : Fin 3) : PolyHom 35 2 :=
  ![PolyHom.zero 35 2,PolyHom.zero 35 2,PolyHom.zero 35 2] b
theorem polyLiftFree35_2 : ∀ b : Fin 3, (polyLift35_2 b).freeBlock=basisInt (homKind 35 2) b := by decide
def polyLift35_3 (b : Fin 3) : PolyHom 35 3 :=
  ![PolyHom.zero 35 3,PolyHom.zero 35 3,PolyHom.zero 35 3] b
theorem polyLiftFree35_3 : ∀ b : Fin 3, (polyLift35_3 b).freeBlock=basisInt (homKind 35 3) b := by decide
def polyLift35_4 (b : Fin 3) : PolyHom 35 4 :=
  ![PolyHom.zero 35 4,PolyHom.zero 35 4,PolyHom.zero 35 4] b
theorem polyLiftFree35_4 : ∀ b : Fin 3, (polyLift35_4 b).freeBlock=basisInt (homKind 35 4) b := by decide
def polyLift35_5 (b : Fin 3) : PolyHom 35 5 :=
  ![PolyHom.zero 35 5,PolyHom.zero 35 5,PolyHom.zero 35 5] b
theorem polyLiftFree35_5 : ∀ b : Fin 3, (polyLift35_5 b).freeBlock=basisInt (homKind 35 5) b := by decide
def polyLift35_6 (b : Fin 3) : PolyHom 35 6 :=
  ![PolyHom.zero 35 6,PolyHom.zero 35 6,PolyHom.zero 35 6] b
theorem polyLiftFree35_6 : ∀ b : Fin 3, (polyLift35_6 b).freeBlock=basisInt (homKind 35 6) b := by decide
def polyLift35_7 (b : Fin 3) : PolyHom 35 7 :=
  ![PolyHom.zero 35 7,PolyHom.zero 35 7,PolyHom.zero 35 7] b
theorem polyLiftFree35_7 : ∀ b : Fin 3, (polyLift35_7 b).freeBlock=basisInt (homKind 35 7) b := by decide
def polyLift35_8 (b : Fin 3) : PolyHom 35 8 :=
  ![PolyHom.zero 35 8,PolyHom.zero 35 8,PolyHom.zero 35 8] b
theorem polyLiftFree35_8 : ∀ b : Fin 3, (polyLift35_8 b).freeBlock=basisInt (homKind 35 8) b := by decide
def polyLift35_9 (b : Fin 3) : PolyHom 35 9 :=
  ![PolyHom.zero 35 9,PolyHom.zero 35 9,PolyHom.zero 35 9] b
theorem polyLiftFree35_9 : ∀ b : Fin 3, (polyLift35_9 b).freeBlock=basisInt (homKind 35 9) b := by decide
def polyRep35_10_0 : PolyHom 35 10 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_10 (b : Fin 3) : PolyHom 35 10 :=
  ![polyRep35_10_0,PolyHom.zero 35 10,PolyHom.zero 35 10] b
theorem polyLiftFree35_10 : ∀ b : Fin 3, (polyLift35_10 b).freeBlock=basisInt (homKind 35 10) b := by decide
def polyRep35_11_0 : PolyHom 35 11 where
  M := !![(mono6 (1) 3),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_11 (b : Fin 3) : PolyHom 35 11 :=
  ![polyRep35_11_0,PolyHom.zero 35 11,PolyHom.zero 35 11] b
theorem polyLiftFree35_11 : ∀ b : Fin 3, (polyLift35_11 b).freeBlock=basisInt (homKind 35 11) b := by decide
def polyRep35_12_0 : PolyHom 35 12 where
  M := !![(mono6 (1) 2),0,0,0;(mono6 (-1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_12 (b : Fin 3) : PolyHom 35 12 :=
  ![polyRep35_12_0,PolyHom.zero 35 12,PolyHom.zero 35 12] b
theorem polyLiftFree35_12 : ∀ b : Fin 3, (polyLift35_12 b).freeBlock=basisInt (homKind 35 12) b := by decide
def polyRep35_13_0 : PolyHom 35 13 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_13 (b : Fin 3) : PolyHom 35 13 :=
  ![polyRep35_13_0,PolyHom.zero 35 13,PolyHom.zero 35 13] b
theorem polyLiftFree35_13 : ∀ b : Fin 3, (polyLift35_13 b).freeBlock=basisInt (homKind 35 13) b := by decide
def polyLift35_14 (b : Fin 3) : PolyHom 35 14 :=
  ![PolyHom.zero 35 14,PolyHom.zero 35 14,PolyHom.zero 35 14] b
theorem polyLiftFree35_14 : ∀ b : Fin 3, (polyLift35_14 b).freeBlock=basisInt (homKind 35 14) b := by decide
def polyLift35_15 (b : Fin 3) : PolyHom 35 15 :=
  ![PolyHom.zero 35 15,PolyHom.zero 35 15,PolyHom.zero 35 15] b
theorem polyLiftFree35_15 : ∀ b : Fin 3, (polyLift35_15 b).freeBlock=basisInt (homKind 35 15) b := by decide
def polyLift35_16 (b : Fin 3) : PolyHom 35 16 :=
  ![PolyHom.zero 35 16,PolyHom.zero 35 16,PolyHom.zero 35 16] b
theorem polyLiftFree35_16 : ∀ b : Fin 3, (polyLift35_16 b).freeBlock=basisInt (homKind 35 16) b := by decide
def polyLift35_17 (b : Fin 3) : PolyHom 35 17 :=
  ![PolyHom.zero 35 17,PolyHom.zero 35 17,PolyHom.zero 35 17] b
theorem polyLiftFree35_17 : ∀ b : Fin 3, (polyLift35_17 b).freeBlock=basisInt (homKind 35 17) b := by decide
def polyLift35_18 (b : Fin 3) : PolyHom 35 18 :=
  ![PolyHom.zero 35 18,PolyHom.zero 35 18,PolyHom.zero 35 18] b
theorem polyLiftFree35_18 : ∀ b : Fin 3, (polyLift35_18 b).freeBlock=basisInt (homKind 35 18) b := by decide
def polyLift35_19 (b : Fin 3) : PolyHom 35 19 :=
  ![PolyHom.zero 35 19,PolyHom.zero 35 19,PolyHom.zero 35 19] b
theorem polyLiftFree35_19 : ∀ b : Fin 3, (polyLift35_19 b).freeBlock=basisInt (homKind 35 19) b := by decide
def polyLift35_20 (b : Fin 3) : PolyHom 35 20 :=
  ![PolyHom.zero 35 20,PolyHom.zero 35 20,PolyHom.zero 35 20] b
theorem polyLiftFree35_20 : ∀ b : Fin 3, (polyLift35_20 b).freeBlock=basisInt (homKind 35 20) b := by decide
def polyRep35_21_0 : PolyHom 35 21 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_21 (b : Fin 3) : PolyHom 35 21 :=
  ![polyRep35_21_0,PolyHom.zero 35 21,PolyHom.zero 35 21] b
theorem polyLiftFree35_21 : ∀ b : Fin 3, (polyLift35_21 b).freeBlock=basisInt (homKind 35 21) b := by decide
def polyRep35_22_0 : PolyHom 35 22 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_22 (b : Fin 3) : PolyHom 35 22 :=
  ![polyRep35_22_0,PolyHom.zero 35 22,PolyHom.zero 35 22] b
theorem polyLiftFree35_22 : ∀ b : Fin 3, (polyLift35_22 b).freeBlock=basisInt (homKind 35 22) b := by decide
def polyLift35_23 (b : Fin 3) : PolyHom 35 23 :=
  ![PolyHom.zero 35 23,PolyHom.zero 35 23,PolyHom.zero 35 23] b
theorem polyLiftFree35_23 : ∀ b : Fin 3, (polyLift35_23 b).freeBlock=basisInt (homKind 35 23) b := by decide
def polyRep35_24_0 : PolyHom 35 24 where
  M := !![(mono6 (1) 2),0,(mono6 (1) 1),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_24 (b : Fin 3) : PolyHom 35 24 :=
  ![polyRep35_24_0,PolyHom.zero 35 24,PolyHom.zero 35 24] b
theorem polyLiftFree35_24 : ∀ b : Fin 3, (polyLift35_24 b).freeBlock=basisInt (homKind 35 24) b := by decide
def polyRep35_25_0 : PolyHom 35 25 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_25 (b : Fin 3) : PolyHom 35 25 :=
  ![polyRep35_25_0,PolyHom.zero 35 25,PolyHom.zero 35 25] b
theorem polyLiftFree35_25 : ∀ b : Fin 3, (polyLift35_25 b).freeBlock=basisInt (homKind 35 25) b := by decide
def polyRep35_26_0 : PolyHom 35 26 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_26 (b : Fin 3) : PolyHom 35 26 :=
  ![polyRep35_26_0,PolyHom.zero 35 26,PolyHom.zero 35 26] b
theorem polyLiftFree35_26 : ∀ b : Fin 3, (polyLift35_26 b).freeBlock=basisInt (homKind 35 26) b := by decide
def polyRep35_27_0 : PolyHom 35 27 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_27 (b : Fin 3) : PolyHom 35 27 :=
  ![polyRep35_27_0,PolyHom.zero 35 27,PolyHom.zero 35 27] b
theorem polyLiftFree35_27 : ∀ b : Fin 3, (polyLift35_27 b).freeBlock=basisInt (homKind 35 27) b := by decide
def polyLift35_28 (b : Fin 3) : PolyHom 35 28 :=
  ![PolyHom.zero 35 28,PolyHom.zero 35 28,PolyHom.zero 35 28] b
theorem polyLiftFree35_28 : ∀ b : Fin 3, (polyLift35_28 b).freeBlock=basisInt (homKind 35 28) b := by decide
def polyLift35_29 (b : Fin 3) : PolyHom 35 29 :=
  ![PolyHom.zero 35 29,PolyHom.zero 35 29,PolyHom.zero 35 29] b
theorem polyLiftFree35_29 : ∀ b : Fin 3, (polyLift35_29 b).freeBlock=basisInt (homKind 35 29) b := by decide
def polyRep35_30_0 : PolyHom 35 30 where
  M := !![(mono6 (1) 2),0,0,0;(mono6 (-1) 1),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_30 (b : Fin 3) : PolyHom 35 30 :=
  ![polyRep35_30_0,PolyHom.zero 35 30,PolyHom.zero 35 30] b
theorem polyLiftFree35_30 : ∀ b : Fin 3, (polyLift35_30 b).freeBlock=basisInt (homKind 35 30) b := by decide
def polyRep35_31_0 : PolyHom 35 31 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_31 (b : Fin 3) : PolyHom 35 31 :=
  ![polyRep35_31_0,PolyHom.zero 35 31,PolyHom.zero 35 31] b
theorem polyLiftFree35_31 : ∀ b : Fin 3, (polyLift35_31 b).freeBlock=basisInt (homKind 35 31) b := by decide
def polyRep35_32_0 : PolyHom 35 32 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_32 (b : Fin 3) : PolyHom 35 32 :=
  ![polyRep35_32_0,PolyHom.zero 35 32,PolyHom.zero 35 32] b
theorem polyLiftFree35_32 : ∀ b : Fin 3, (polyLift35_32 b).freeBlock=basisInt (homKind 35 32) b := by decide
def polyRep35_33_0 : PolyHom 35 33 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_33 (b : Fin 3) : PolyHom 35 33 :=
  ![polyRep35_33_0,PolyHom.zero 35 33,PolyHom.zero 35 33] b
theorem polyLiftFree35_33 : ∀ b : Fin 3, (polyLift35_33 b).freeBlock=basisInt (homKind 35 33) b := by decide
def polyRep35_34_0 : PolyHom 35 34 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_34 (b : Fin 3) : PolyHom 35 34 :=
  ![polyRep35_34_0,PolyHom.zero 35 34,PolyHom.zero 35 34] b
theorem polyLiftFree35_34 : ∀ b : Fin 3, (polyLift35_34 b).freeBlock=basisInt (homKind 35 34) b := by decide
def polyRep35_35_0 : PolyHom 35 35 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_35 (b : Fin 3) : PolyHom 35 35 :=
  ![polyRep35_35_0,PolyHom.zero 35 35,PolyHom.zero 35 35] b
theorem polyLiftFree35_35 : ∀ b : Fin 3, (polyLift35_35 b).freeBlock=basisInt (homKind 35 35) b := by decide
def polyRep35_36_0 : PolyHom 35 36 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_36 (b : Fin 3) : PolyHom 35 36 :=
  ![polyRep35_36_0,PolyHom.zero 35 36,PolyHom.zero 35 36] b
theorem polyLiftFree35_36 : ∀ b : Fin 3, (polyLift35_36 b).freeBlock=basisInt (homKind 35 36) b := by decide
def polyRep35_37_0 : PolyHom 35 37 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_37 (b : Fin 3) : PolyHom 35 37 :=
  ![polyRep35_37_0,PolyHom.zero 35 37,PolyHom.zero 35 37] b
theorem polyLiftFree35_37 : ∀ b : Fin 3, (polyLift35_37 b).freeBlock=basisInt (homKind 35 37) b := by decide
def polyRep35_38_0 : PolyHom 35 38 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_38 (b : Fin 3) : PolyHom 35 38 :=
  ![polyRep35_38_0,PolyHom.zero 35 38,PolyHom.zero 35 38] b
theorem polyLiftFree35_38 : ∀ b : Fin 3, (polyLift35_38 b).freeBlock=basisInt (homKind 35 38) b := by decide
def polyRep35_39_0 : PolyHom 35 39 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_39 (b : Fin 3) : PolyHom 35 39 :=
  ![polyRep35_39_0,PolyHom.zero 35 39,PolyHom.zero 35 39] b
theorem polyLiftFree35_39 : ∀ b : Fin 3, (polyLift35_39 b).freeBlock=basisInt (homKind 35 39) b := by decide
def polyRep35_40_0 : PolyHom 35 40 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_40 (b : Fin 3) : PolyHom 35 40 :=
  ![polyRep35_40_0,PolyHom.zero 35 40,PolyHom.zero 35 40] b
theorem polyLiftFree35_40 : ∀ b : Fin 3, (polyLift35_40 b).freeBlock=basisInt (homKind 35 40) b := by decide
def polyRep35_41_0 : PolyHom 35 41 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_41 (b : Fin 3) : PolyHom 35 41 :=
  ![polyRep35_41_0,PolyHom.zero 35 41,PolyHom.zero 35 41] b
theorem polyLiftFree35_41 : ∀ b : Fin 3, (polyLift35_41 b).freeBlock=basisInt (homKind 35 41) b := by decide
def polyRep35_42_0 : PolyHom 35 42 where
  M := !![0,(mono6 (1) 2),0,0;0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),(mono6 (-1) 1);0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (-1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_42 (b : Fin 3) : PolyHom 35 42 :=
  ![polyRep35_42_0,PolyHom.zero 35 42,PolyHom.zero 35 42] b
theorem polyLiftFree35_42 : ∀ b : Fin 3, (polyLift35_42 b).freeBlock=basisInt (homKind 35 42) b := by decide
def polyLift35_43 (b : Fin 3) : PolyHom 35 43 :=
  ![PolyHom.zero 35 43,PolyHom.zero 35 43,PolyHom.zero 35 43] b
theorem polyLiftFree35_43 : ∀ b : Fin 3, (polyLift35_43 b).freeBlock=basisInt (homKind 35 43) b := by decide
def polyRep35_44_0 : PolyHom 35 44 where
  M := !![(mono6 (1) 1),(mono6 (1) 2),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_44 (b : Fin 3) : PolyHom 35 44 :=
  ![polyRep35_44_0,PolyHom.zero 35 44,PolyHom.zero 35 44] b
theorem polyLiftFree35_44 : ∀ b : Fin 3, (polyLift35_44 b).freeBlock=basisInt (homKind 35 44) b := by decide
def polyRep35_45_0 : PolyHom 35 45 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift35_45 (b : Fin 3) : PolyHom 35 45 :=
  ![polyRep35_45_0,PolyHom.zero 35 45,PolyHom.zero 35 45] b
theorem polyLiftFree35_45 : ∀ b : Fin 3, (polyLift35_45 b).freeBlock=basisInt (homKind 35 45) b := by decide
def polyLift35_46 (b : Fin 3) : PolyHom 35 46 :=
  ![PolyHom.zero 35 46,PolyHom.zero 35 46,PolyHom.zero 35 46] b
theorem polyLiftFree35_46 : ∀ b : Fin 3, (polyLift35_46 b).freeBlock=basisInt (homKind 35 46) b := by decide
def polyLiftRow35 (j : Fin 47) (b : Fin 3) : PolyHom 35 j :=
  match j with
  | ⟨0,_⟩ => polyLift35_0 b
  | ⟨1,_⟩ => polyLift35_1 b
  | ⟨2,_⟩ => polyLift35_2 b
  | ⟨3,_⟩ => polyLift35_3 b
  | ⟨4,_⟩ => polyLift35_4 b
  | ⟨5,_⟩ => polyLift35_5 b
  | ⟨6,_⟩ => polyLift35_6 b
  | ⟨7,_⟩ => polyLift35_7 b
  | ⟨8,_⟩ => polyLift35_8 b
  | ⟨9,_⟩ => polyLift35_9 b
  | ⟨10,_⟩ => polyLift35_10 b
  | ⟨11,_⟩ => polyLift35_11 b
  | ⟨12,_⟩ => polyLift35_12 b
  | ⟨13,_⟩ => polyLift35_13 b
  | ⟨14,_⟩ => polyLift35_14 b
  | ⟨15,_⟩ => polyLift35_15 b
  | ⟨16,_⟩ => polyLift35_16 b
  | ⟨17,_⟩ => polyLift35_17 b
  | ⟨18,_⟩ => polyLift35_18 b
  | ⟨19,_⟩ => polyLift35_19 b
  | ⟨20,_⟩ => polyLift35_20 b
  | ⟨21,_⟩ => polyLift35_21 b
  | ⟨22,_⟩ => polyLift35_22 b
  | ⟨23,_⟩ => polyLift35_23 b
  | ⟨24,_⟩ => polyLift35_24 b
  | ⟨25,_⟩ => polyLift35_25 b
  | ⟨26,_⟩ => polyLift35_26 b
  | ⟨27,_⟩ => polyLift35_27 b
  | ⟨28,_⟩ => polyLift35_28 b
  | ⟨29,_⟩ => polyLift35_29 b
  | ⟨30,_⟩ => polyLift35_30 b
  | ⟨31,_⟩ => polyLift35_31 b
  | ⟨32,_⟩ => polyLift35_32 b
  | ⟨33,_⟩ => polyLift35_33 b
  | ⟨34,_⟩ => polyLift35_34 b
  | ⟨35,_⟩ => polyLift35_35 b
  | ⟨36,_⟩ => polyLift35_36 b
  | ⟨37,_⟩ => polyLift35_37 b
  | ⟨38,_⟩ => polyLift35_38 b
  | ⟨39,_⟩ => polyLift35_39 b
  | ⟨40,_⟩ => polyLift35_40 b
  | ⟨41,_⟩ => polyLift35_41 b
  | ⟨42,_⟩ => polyLift35_42 b
  | ⟨43,_⟩ => polyLift35_43 b
  | ⟨44,_⟩ => polyLift35_44 b
  | ⟨45,_⟩ => polyLift35_45 b
  | ⟨46,_⟩ => polyLift35_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree35 (j : Fin 47) (b : Fin 3) : (polyLiftRow35 j b).freeBlock=basisInt (homKind 35 j) b := by
  fin_cases j
  · exact polyLiftFree35_0 b
  · exact polyLiftFree35_1 b
  · exact polyLiftFree35_2 b
  · exact polyLiftFree35_3 b
  · exact polyLiftFree35_4 b
  · exact polyLiftFree35_5 b
  · exact polyLiftFree35_6 b
  · exact polyLiftFree35_7 b
  · exact polyLiftFree35_8 b
  · exact polyLiftFree35_9 b
  · exact polyLiftFree35_10 b
  · exact polyLiftFree35_11 b
  · exact polyLiftFree35_12 b
  · exact polyLiftFree35_13 b
  · exact polyLiftFree35_14 b
  · exact polyLiftFree35_15 b
  · exact polyLiftFree35_16 b
  · exact polyLiftFree35_17 b
  · exact polyLiftFree35_18 b
  · exact polyLiftFree35_19 b
  · exact polyLiftFree35_20 b
  · exact polyLiftFree35_21 b
  · exact polyLiftFree35_22 b
  · exact polyLiftFree35_23 b
  · exact polyLiftFree35_24 b
  · exact polyLiftFree35_25 b
  · exact polyLiftFree35_26 b
  · exact polyLiftFree35_27 b
  · exact polyLiftFree35_28 b
  · exact polyLiftFree35_29 b
  · exact polyLiftFree35_30 b
  · exact polyLiftFree35_31 b
  · exact polyLiftFree35_32 b
  · exact polyLiftFree35_33 b
  · exact polyLiftFree35_34 b
  · exact polyLiftFree35_35 b
  · exact polyLiftFree35_36 b
  · exact polyLiftFree35_37 b
  · exact polyLiftFree35_38 b
  · exact polyLiftFree35_39 b
  · exact polyLiftFree35_40 b
  · exact polyLiftFree35_41 b
  · exact polyLiftFree35_42 b
  · exact polyLiftFree35_43 b
  · exact polyLiftFree35_44 b
  · exact polyLiftFree35_45 b
  · exact polyLiftFree35_46 b
end UniserialComputations.N6
