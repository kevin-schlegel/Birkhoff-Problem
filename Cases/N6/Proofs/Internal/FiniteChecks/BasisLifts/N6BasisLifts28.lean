import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift28_0 (b : Fin 3) : PolyHom 28 0 :=
  ![PolyHom.zero 28 0,PolyHom.zero 28 0,PolyHom.zero 28 0] b
theorem polyLiftFree28_0 : ∀ b : Fin 3, (polyLift28_0 b).freeBlock=basisInt (homKind 28 0) b := by decide
def polyLift28_1 (b : Fin 3) : PolyHom 28 1 :=
  ![PolyHom.zero 28 1,PolyHom.zero 28 1,PolyHom.zero 28 1] b
theorem polyLiftFree28_1 : ∀ b : Fin 3, (polyLift28_1 b).freeBlock=basisInt (homKind 28 1) b := by decide
def polyLift28_2 (b : Fin 3) : PolyHom 28 2 :=
  ![PolyHom.zero 28 2,PolyHom.zero 28 2,PolyHom.zero 28 2] b
theorem polyLiftFree28_2 : ∀ b : Fin 3, (polyLift28_2 b).freeBlock=basisInt (homKind 28 2) b := by decide
def polyLift28_3 (b : Fin 3) : PolyHom 28 3 :=
  ![PolyHom.zero 28 3,PolyHom.zero 28 3,PolyHom.zero 28 3] b
theorem polyLiftFree28_3 : ∀ b : Fin 3, (polyLift28_3 b).freeBlock=basisInt (homKind 28 3) b := by decide
def polyLift28_4 (b : Fin 3) : PolyHom 28 4 :=
  ![PolyHom.zero 28 4,PolyHom.zero 28 4,PolyHom.zero 28 4] b
theorem polyLiftFree28_4 : ∀ b : Fin 3, (polyLift28_4 b).freeBlock=basisInt (homKind 28 4) b := by decide
def polyLift28_5 (b : Fin 3) : PolyHom 28 5 :=
  ![PolyHom.zero 28 5,PolyHom.zero 28 5,PolyHom.zero 28 5] b
theorem polyLiftFree28_5 : ∀ b : Fin 3, (polyLift28_5 b).freeBlock=basisInt (homKind 28 5) b := by decide
def polyLift28_6 (b : Fin 3) : PolyHom 28 6 :=
  ![PolyHom.zero 28 6,PolyHom.zero 28 6,PolyHom.zero 28 6] b
theorem polyLiftFree28_6 : ∀ b : Fin 3, (polyLift28_6 b).freeBlock=basisInt (homKind 28 6) b := by decide
def polyLift28_7 (b : Fin 3) : PolyHom 28 7 :=
  ![PolyHom.zero 28 7,PolyHom.zero 28 7,PolyHom.zero 28 7] b
theorem polyLiftFree28_7 : ∀ b : Fin 3, (polyLift28_7 b).freeBlock=basisInt (homKind 28 7) b := by decide
def polyLift28_8 (b : Fin 3) : PolyHom 28 8 :=
  ![PolyHom.zero 28 8,PolyHom.zero 28 8,PolyHom.zero 28 8] b
theorem polyLiftFree28_8 : ∀ b : Fin 3, (polyLift28_8 b).freeBlock=basisInt (homKind 28 8) b := by decide
def polyLift28_9 (b : Fin 3) : PolyHom 28 9 :=
  ![PolyHom.zero 28 9,PolyHom.zero 28 9,PolyHom.zero 28 9] b
theorem polyLiftFree28_9 : ∀ b : Fin 3, (polyLift28_9 b).freeBlock=basisInt (homKind 28 9) b := by decide
def polyRep28_10_0 : PolyHom 28 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_10 (b : Fin 3) : PolyHom 28 10 :=
  ![polyRep28_10_0,PolyHom.zero 28 10,PolyHom.zero 28 10] b
theorem polyLiftFree28_10 : ∀ b : Fin 3, (polyLift28_10 b).freeBlock=basisInt (homKind 28 10) b := by decide
def polyRep28_11_0 : PolyHom 28 11 where
  M := !![(mono6 (1) 3),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_11 (b : Fin 3) : PolyHom 28 11 :=
  ![polyRep28_11_0,PolyHom.zero 28 11,PolyHom.zero 28 11] b
theorem polyLiftFree28_11 : ∀ b : Fin 3, (polyLift28_11 b).freeBlock=basisInt (homKind 28 11) b := by decide
def polyRep28_12_0 : PolyHom 28 12 where
  M := !![(mono6 (1) 2),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_12 (b : Fin 3) : PolyHom 28 12 :=
  ![polyRep28_12_0,PolyHom.zero 28 12,PolyHom.zero 28 12] b
theorem polyLiftFree28_12 : ∀ b : Fin 3, (polyLift28_12 b).freeBlock=basisInt (homKind 28 12) b := by decide
def polyLift28_13 (b : Fin 3) : PolyHom 28 13 :=
  ![PolyHom.zero 28 13,PolyHom.zero 28 13,PolyHom.zero 28 13] b
theorem polyLiftFree28_13 : ∀ b : Fin 3, (polyLift28_13 b).freeBlock=basisInt (homKind 28 13) b := by decide
def polyLift28_14 (b : Fin 3) : PolyHom 28 14 :=
  ![PolyHom.zero 28 14,PolyHom.zero 28 14,PolyHom.zero 28 14] b
theorem polyLiftFree28_14 : ∀ b : Fin 3, (polyLift28_14 b).freeBlock=basisInt (homKind 28 14) b := by decide
def polyLift28_15 (b : Fin 3) : PolyHom 28 15 :=
  ![PolyHom.zero 28 15,PolyHom.zero 28 15,PolyHom.zero 28 15] b
theorem polyLiftFree28_15 : ∀ b : Fin 3, (polyLift28_15 b).freeBlock=basisInt (homKind 28 15) b := by decide
def polyLift28_16 (b : Fin 3) : PolyHom 28 16 :=
  ![PolyHom.zero 28 16,PolyHom.zero 28 16,PolyHom.zero 28 16] b
theorem polyLiftFree28_16 : ∀ b : Fin 3, (polyLift28_16 b).freeBlock=basisInt (homKind 28 16) b := by decide
def polyLift28_17 (b : Fin 3) : PolyHom 28 17 :=
  ![PolyHom.zero 28 17,PolyHom.zero 28 17,PolyHom.zero 28 17] b
theorem polyLiftFree28_17 : ∀ b : Fin 3, (polyLift28_17 b).freeBlock=basisInt (homKind 28 17) b := by decide
def polyLift28_18 (b : Fin 3) : PolyHom 28 18 :=
  ![PolyHom.zero 28 18,PolyHom.zero 28 18,PolyHom.zero 28 18] b
theorem polyLiftFree28_18 : ∀ b : Fin 3, (polyLift28_18 b).freeBlock=basisInt (homKind 28 18) b := by decide
def polyLift28_19 (b : Fin 3) : PolyHom 28 19 :=
  ![PolyHom.zero 28 19,PolyHom.zero 28 19,PolyHom.zero 28 19] b
theorem polyLiftFree28_19 : ∀ b : Fin 3, (polyLift28_19 b).freeBlock=basisInt (homKind 28 19) b := by decide
def polyLift28_20 (b : Fin 3) : PolyHom 28 20 :=
  ![PolyHom.zero 28 20,PolyHom.zero 28 20,PolyHom.zero 28 20] b
theorem polyLiftFree28_20 : ∀ b : Fin 3, (polyLift28_20 b).freeBlock=basisInt (homKind 28 20) b := by decide
def polyRep28_21_0 : PolyHom 28 21 where
  M := !![(mono6 (1) 2),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_21 (b : Fin 3) : PolyHom 28 21 :=
  ![polyRep28_21_0,PolyHom.zero 28 21,PolyHom.zero 28 21] b
theorem polyLiftFree28_21 : ∀ b : Fin 3, (polyLift28_21 b).freeBlock=basisInt (homKind 28 21) b := by decide
def polyRep28_22_0 : PolyHom 28 22 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_22 (b : Fin 3) : PolyHom 28 22 :=
  ![polyRep28_22_0,PolyHom.zero 28 22,PolyHom.zero 28 22] b
theorem polyLiftFree28_22 : ∀ b : Fin 3, (polyLift28_22 b).freeBlock=basisInt (homKind 28 22) b := by decide
def polyLift28_23 (b : Fin 3) : PolyHom 28 23 :=
  ![PolyHom.zero 28 23,PolyHom.zero 28 23,PolyHom.zero 28 23] b
theorem polyLiftFree28_23 : ∀ b : Fin 3, (polyLift28_23 b).freeBlock=basisInt (homKind 28 23) b := by decide
def polyRep28_24_0 : PolyHom 28 24 where
  M := !![(mono6 (1) 2),0,(mono6 (1) 1),0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_24 (b : Fin 3) : PolyHom 28 24 :=
  ![polyRep28_24_0,PolyHom.zero 28 24,PolyHom.zero 28 24] b
theorem polyLiftFree28_24 : ∀ b : Fin 3, (polyLift28_24 b).freeBlock=basisInt (homKind 28 24) b := by decide
def polyRep28_25_0 : PolyHom 28 25 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_25 (b : Fin 3) : PolyHom 28 25 :=
  ![polyRep28_25_0,PolyHom.zero 28 25,PolyHom.zero 28 25] b
theorem polyLiftFree28_25 : ∀ b : Fin 3, (polyLift28_25 b).freeBlock=basisInt (homKind 28 25) b := by decide
def polyRep28_26_0 : PolyHom 28 26 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_26 (b : Fin 3) : PolyHom 28 26 :=
  ![polyRep28_26_0,PolyHom.zero 28 26,PolyHom.zero 28 26] b
theorem polyLiftFree28_26 : ∀ b : Fin 3, (polyLift28_26 b).freeBlock=basisInt (homKind 28 26) b := by decide
def polyRep28_27_0 : PolyHom 28 27 where
  M := !![(mono6 (1) 1),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_27 (b : Fin 3) : PolyHom 28 27 :=
  ![polyRep28_27_0,PolyHom.zero 28 27,PolyHom.zero 28 27] b
theorem polyLiftFree28_27 : ∀ b : Fin 3, (polyLift28_27 b).freeBlock=basisInt (homKind 28 27) b := by decide
def polyRep28_28_0 : PolyHom 28 28 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_28 (b : Fin 3) : PolyHom 28 28 :=
  ![polyRep28_28_0,PolyHom.zero 28 28,PolyHom.zero 28 28] b
theorem polyLiftFree28_28 : ∀ b : Fin 3, (polyLift28_28 b).freeBlock=basisInt (homKind 28 28) b := by decide
def polyLift28_29 (b : Fin 3) : PolyHom 28 29 :=
  ![PolyHom.zero 28 29,PolyHom.zero 28 29,PolyHom.zero 28 29] b
theorem polyLiftFree28_29 : ∀ b : Fin 3, (polyLift28_29 b).freeBlock=basisInt (homKind 28 29) b := by decide
def polyRep28_30_0 : PolyHom 28 30 where
  M := !![(mono6 (1) 2),0,(mono6 (1) 0),0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_30 (b : Fin 3) : PolyHom 28 30 :=
  ![polyRep28_30_0,PolyHom.zero 28 30,PolyHom.zero 28 30] b
theorem polyLiftFree28_30 : ∀ b : Fin 3, (polyLift28_30 b).freeBlock=basisInt (homKind 28 30) b := by decide
def polyRep28_31_0 : PolyHom 28 31 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_31 (b : Fin 3) : PolyHom 28 31 :=
  ![polyRep28_31_0,PolyHom.zero 28 31,PolyHom.zero 28 31] b
theorem polyLiftFree28_31 : ∀ b : Fin 3, (polyLift28_31 b).freeBlock=basisInt (homKind 28 31) b := by decide
def polyRep28_32_0 : PolyHom 28 32 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_32 (b : Fin 3) : PolyHom 28 32 :=
  ![polyRep28_32_0,PolyHom.zero 28 32,PolyHom.zero 28 32] b
theorem polyLiftFree28_32 : ∀ b : Fin 3, (polyLift28_32 b).freeBlock=basisInt (homKind 28 32) b := by decide
def polyRep28_33_0 : PolyHom 28 33 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_33 (b : Fin 3) : PolyHom 28 33 :=
  ![polyRep28_33_0,PolyHom.zero 28 33,PolyHom.zero 28 33] b
theorem polyLiftFree28_33 : ∀ b : Fin 3, (polyLift28_33 b).freeBlock=basisInt (homKind 28 33) b := by decide
def polyRep28_34_0 : PolyHom 28 34 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_34 (b : Fin 3) : PolyHom 28 34 :=
  ![polyRep28_34_0,PolyHom.zero 28 34,PolyHom.zero 28 34] b
theorem polyLiftFree28_34 : ∀ b : Fin 3, (polyLift28_34 b).freeBlock=basisInt (homKind 28 34) b := by decide
def polyLift28_35 (b : Fin 3) : PolyHom 28 35 :=
  ![PolyHom.zero 28 35,PolyHom.zero 28 35,PolyHom.zero 28 35] b
theorem polyLiftFree28_35 : ∀ b : Fin 3, (polyLift28_35 b).freeBlock=basisInt (homKind 28 35) b := by decide
def polyRep28_36_0 : PolyHom 28 36 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_36 (b : Fin 3) : PolyHom 28 36 :=
  ![polyRep28_36_0,PolyHom.zero 28 36,PolyHom.zero 28 36] b
theorem polyLiftFree28_36 : ∀ b : Fin 3, (polyLift28_36 b).freeBlock=basisInt (homKind 28 36) b := by decide
def polyRep28_37_0 : PolyHom 28 37 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_37 (b : Fin 3) : PolyHom 28 37 :=
  ![polyRep28_37_0,PolyHom.zero 28 37,PolyHom.zero 28 37] b
theorem polyLiftFree28_37 : ∀ b : Fin 3, (polyLift28_37 b).freeBlock=basisInt (homKind 28 37) b := by decide
def polyRep28_38_0 : PolyHom 28 38 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_38 (b : Fin 3) : PolyHom 28 38 :=
  ![polyRep28_38_0,PolyHom.zero 28 38,PolyHom.zero 28 38] b
theorem polyLiftFree28_38 : ∀ b : Fin 3, (polyLift28_38 b).freeBlock=basisInt (homKind 28 38) b := by decide
def polyRep28_39_0 : PolyHom 28 39 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_39 (b : Fin 3) : PolyHom 28 39 :=
  ![polyRep28_39_0,PolyHom.zero 28 39,PolyHom.zero 28 39] b
theorem polyLiftFree28_39 : ∀ b : Fin 3, (polyLift28_39 b).freeBlock=basisInt (homKind 28 39) b := by decide
def polyRep28_40_0 : PolyHom 28 40 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_40 (b : Fin 3) : PolyHom 28 40 :=
  ![polyRep28_40_0,PolyHom.zero 28 40,PolyHom.zero 28 40] b
theorem polyLiftFree28_40 : ∀ b : Fin 3, (polyLift28_40 b).freeBlock=basisInt (homKind 28 40) b := by decide
def polyRep28_41_0 : PolyHom 28 41 where
  M := !![(mono6 (1) 0),0,0,(mono6 (1) 0);0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_41 (b : Fin 3) : PolyHom 28 41 :=
  ![polyRep28_41_0,PolyHom.zero 28 41,PolyHom.zero 28 41] b
theorem polyLiftFree28_41 : ∀ b : Fin 3, (polyLift28_41 b).freeBlock=basisInt (homKind 28 41) b := by decide
def polyRep28_42_0 : PolyHom 28 42 where
  M := !![0,(mono6 (1) 2),0,(mono6 (-1) 0);0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_42 (b : Fin 3) : PolyHom 28 42 :=
  ![polyRep28_42_0,PolyHom.zero 28 42,PolyHom.zero 28 42] b
theorem polyLiftFree28_42 : ∀ b : Fin 3, (polyLift28_42 b).freeBlock=basisInt (homKind 28 42) b := by decide
def polyLift28_43 (b : Fin 3) : PolyHom 28 43 :=
  ![PolyHom.zero 28 43,PolyHom.zero 28 43,PolyHom.zero 28 43] b
theorem polyLiftFree28_43 : ∀ b : Fin 3, (polyLift28_43 b).freeBlock=basisInt (homKind 28 43) b := by decide
def polyRep28_44_0 : PolyHom 28 44 where
  M := !![(mono6 (1) 1),(mono6 (1) 2),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_44 (b : Fin 3) : PolyHom 28 44 :=
  ![polyRep28_44_0,PolyHom.zero 28 44,PolyHom.zero 28 44] b
theorem polyLiftFree28_44 : ∀ b : Fin 3, (polyLift28_44 b).freeBlock=basisInt (homKind 28 44) b := by decide
def polyRep28_45_0 : PolyHom 28 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift28_45 (b : Fin 3) : PolyHom 28 45 :=
  ![polyRep28_45_0,PolyHom.zero 28 45,PolyHom.zero 28 45] b
theorem polyLiftFree28_45 : ∀ b : Fin 3, (polyLift28_45 b).freeBlock=basisInt (homKind 28 45) b := by decide
def polyLift28_46 (b : Fin 3) : PolyHom 28 46 :=
  ![PolyHom.zero 28 46,PolyHom.zero 28 46,PolyHom.zero 28 46] b
theorem polyLiftFree28_46 : ∀ b : Fin 3, (polyLift28_46 b).freeBlock=basisInt (homKind 28 46) b := by decide
def polyLiftRow28 (j : Fin 47) (b : Fin 3) : PolyHom 28 j :=
  match j with
  | ⟨0,_⟩ => polyLift28_0 b
  | ⟨1,_⟩ => polyLift28_1 b
  | ⟨2,_⟩ => polyLift28_2 b
  | ⟨3,_⟩ => polyLift28_3 b
  | ⟨4,_⟩ => polyLift28_4 b
  | ⟨5,_⟩ => polyLift28_5 b
  | ⟨6,_⟩ => polyLift28_6 b
  | ⟨7,_⟩ => polyLift28_7 b
  | ⟨8,_⟩ => polyLift28_8 b
  | ⟨9,_⟩ => polyLift28_9 b
  | ⟨10,_⟩ => polyLift28_10 b
  | ⟨11,_⟩ => polyLift28_11 b
  | ⟨12,_⟩ => polyLift28_12 b
  | ⟨13,_⟩ => polyLift28_13 b
  | ⟨14,_⟩ => polyLift28_14 b
  | ⟨15,_⟩ => polyLift28_15 b
  | ⟨16,_⟩ => polyLift28_16 b
  | ⟨17,_⟩ => polyLift28_17 b
  | ⟨18,_⟩ => polyLift28_18 b
  | ⟨19,_⟩ => polyLift28_19 b
  | ⟨20,_⟩ => polyLift28_20 b
  | ⟨21,_⟩ => polyLift28_21 b
  | ⟨22,_⟩ => polyLift28_22 b
  | ⟨23,_⟩ => polyLift28_23 b
  | ⟨24,_⟩ => polyLift28_24 b
  | ⟨25,_⟩ => polyLift28_25 b
  | ⟨26,_⟩ => polyLift28_26 b
  | ⟨27,_⟩ => polyLift28_27 b
  | ⟨28,_⟩ => polyLift28_28 b
  | ⟨29,_⟩ => polyLift28_29 b
  | ⟨30,_⟩ => polyLift28_30 b
  | ⟨31,_⟩ => polyLift28_31 b
  | ⟨32,_⟩ => polyLift28_32 b
  | ⟨33,_⟩ => polyLift28_33 b
  | ⟨34,_⟩ => polyLift28_34 b
  | ⟨35,_⟩ => polyLift28_35 b
  | ⟨36,_⟩ => polyLift28_36 b
  | ⟨37,_⟩ => polyLift28_37 b
  | ⟨38,_⟩ => polyLift28_38 b
  | ⟨39,_⟩ => polyLift28_39 b
  | ⟨40,_⟩ => polyLift28_40 b
  | ⟨41,_⟩ => polyLift28_41 b
  | ⟨42,_⟩ => polyLift28_42 b
  | ⟨43,_⟩ => polyLift28_43 b
  | ⟨44,_⟩ => polyLift28_44 b
  | ⟨45,_⟩ => polyLift28_45 b
  | ⟨46,_⟩ => polyLift28_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree28 (j : Fin 47) (b : Fin 3) : (polyLiftRow28 j b).freeBlock=basisInt (homKind 28 j) b := by
  fin_cases j
  · exact polyLiftFree28_0 b
  · exact polyLiftFree28_1 b
  · exact polyLiftFree28_2 b
  · exact polyLiftFree28_3 b
  · exact polyLiftFree28_4 b
  · exact polyLiftFree28_5 b
  · exact polyLiftFree28_6 b
  · exact polyLiftFree28_7 b
  · exact polyLiftFree28_8 b
  · exact polyLiftFree28_9 b
  · exact polyLiftFree28_10 b
  · exact polyLiftFree28_11 b
  · exact polyLiftFree28_12 b
  · exact polyLiftFree28_13 b
  · exact polyLiftFree28_14 b
  · exact polyLiftFree28_15 b
  · exact polyLiftFree28_16 b
  · exact polyLiftFree28_17 b
  · exact polyLiftFree28_18 b
  · exact polyLiftFree28_19 b
  · exact polyLiftFree28_20 b
  · exact polyLiftFree28_21 b
  · exact polyLiftFree28_22 b
  · exact polyLiftFree28_23 b
  · exact polyLiftFree28_24 b
  · exact polyLiftFree28_25 b
  · exact polyLiftFree28_26 b
  · exact polyLiftFree28_27 b
  · exact polyLiftFree28_28 b
  · exact polyLiftFree28_29 b
  · exact polyLiftFree28_30 b
  · exact polyLiftFree28_31 b
  · exact polyLiftFree28_32 b
  · exact polyLiftFree28_33 b
  · exact polyLiftFree28_34 b
  · exact polyLiftFree28_35 b
  · exact polyLiftFree28_36 b
  · exact polyLiftFree28_37 b
  · exact polyLiftFree28_38 b
  · exact polyLiftFree28_39 b
  · exact polyLiftFree28_40 b
  · exact polyLiftFree28_41 b
  · exact polyLiftFree28_42 b
  · exact polyLiftFree28_43 b
  · exact polyLiftFree28_44 b
  · exact polyLiftFree28_45 b
  · exact polyLiftFree28_46 b
end UniserialComputations.N6
