import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift36_0 (b : Fin 3) : PolyHom 36 0 :=
  ![PolyHom.zero 36 0,PolyHom.zero 36 0,PolyHom.zero 36 0] b
theorem polyLiftFree36_0 : ∀ b : Fin 3, (polyLift36_0 b).freeBlock=basisInt (homKind 36 0) b := by decide
def polyLift36_1 (b : Fin 3) : PolyHom 36 1 :=
  ![PolyHom.zero 36 1,PolyHom.zero 36 1,PolyHom.zero 36 1] b
theorem polyLiftFree36_1 : ∀ b : Fin 3, (polyLift36_1 b).freeBlock=basisInt (homKind 36 1) b := by decide
def polyLift36_2 (b : Fin 3) : PolyHom 36 2 :=
  ![PolyHom.zero 36 2,PolyHom.zero 36 2,PolyHom.zero 36 2] b
theorem polyLiftFree36_2 : ∀ b : Fin 3, (polyLift36_2 b).freeBlock=basisInt (homKind 36 2) b := by decide
def polyLift36_3 (b : Fin 3) : PolyHom 36 3 :=
  ![PolyHom.zero 36 3,PolyHom.zero 36 3,PolyHom.zero 36 3] b
theorem polyLiftFree36_3 : ∀ b : Fin 3, (polyLift36_3 b).freeBlock=basisInt (homKind 36 3) b := by decide
def polyLift36_4 (b : Fin 3) : PolyHom 36 4 :=
  ![PolyHom.zero 36 4,PolyHom.zero 36 4,PolyHom.zero 36 4] b
theorem polyLiftFree36_4 : ∀ b : Fin 3, (polyLift36_4 b).freeBlock=basisInt (homKind 36 4) b := by decide
def polyLift36_5 (b : Fin 3) : PolyHom 36 5 :=
  ![PolyHom.zero 36 5,PolyHom.zero 36 5,PolyHom.zero 36 5] b
theorem polyLiftFree36_5 : ∀ b : Fin 3, (polyLift36_5 b).freeBlock=basisInt (homKind 36 5) b := by decide
def polyLift36_6 (b : Fin 3) : PolyHom 36 6 :=
  ![PolyHom.zero 36 6,PolyHom.zero 36 6,PolyHom.zero 36 6] b
theorem polyLiftFree36_6 : ∀ b : Fin 3, (polyLift36_6 b).freeBlock=basisInt (homKind 36 6) b := by decide
def polyLift36_7 (b : Fin 3) : PolyHom 36 7 :=
  ![PolyHom.zero 36 7,PolyHom.zero 36 7,PolyHom.zero 36 7] b
theorem polyLiftFree36_7 : ∀ b : Fin 3, (polyLift36_7 b).freeBlock=basisInt (homKind 36 7) b := by decide
def polyLift36_8 (b : Fin 3) : PolyHom 36 8 :=
  ![PolyHom.zero 36 8,PolyHom.zero 36 8,PolyHom.zero 36 8] b
theorem polyLiftFree36_8 : ∀ b : Fin 3, (polyLift36_8 b).freeBlock=basisInt (homKind 36 8) b := by decide
def polyLift36_9 (b : Fin 3) : PolyHom 36 9 :=
  ![PolyHom.zero 36 9,PolyHom.zero 36 9,PolyHom.zero 36 9] b
theorem polyLiftFree36_9 : ∀ b : Fin 3, (polyLift36_9 b).freeBlock=basisInt (homKind 36 9) b := by decide
def polyRep36_10_0 : PolyHom 36 10 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift36_10 (b : Fin 3) : PolyHom 36 10 :=
  ![polyRep36_10_0,PolyHom.zero 36 10,PolyHom.zero 36 10] b
theorem polyLiftFree36_10 : ∀ b : Fin 3, (polyLift36_10 b).freeBlock=basisInt (homKind 36 10) b := by decide
def polyRep36_11_0 : PolyHom 36 11 where
  M := !![(mono6 (1) 3),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift36_11 (b : Fin 3) : PolyHom 36 11 :=
  ![polyRep36_11_0,PolyHom.zero 36 11,PolyHom.zero 36 11] b
theorem polyLiftFree36_11 : ∀ b : Fin 3, (polyLift36_11 b).freeBlock=basisInt (homKind 36 11) b := by decide
def polyRep36_12_0 : PolyHom 36 12 where
  M := !![(mono6 (1) 2),0,0,0;(mono6 (-1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift36_12 (b : Fin 3) : PolyHom 36 12 :=
  ![polyRep36_12_0,PolyHom.zero 36 12,PolyHom.zero 36 12] b
theorem polyLiftFree36_12 : ∀ b : Fin 3, (polyLift36_12 b).freeBlock=basisInt (homKind 36 12) b := by decide
def polyLift36_13 (b : Fin 3) : PolyHom 36 13 :=
  ![PolyHom.zero 36 13,PolyHom.zero 36 13,PolyHom.zero 36 13] b
theorem polyLiftFree36_13 : ∀ b : Fin 3, (polyLift36_13 b).freeBlock=basisInt (homKind 36 13) b := by decide
def polyLift36_14 (b : Fin 3) : PolyHom 36 14 :=
  ![PolyHom.zero 36 14,PolyHom.zero 36 14,PolyHom.zero 36 14] b
theorem polyLiftFree36_14 : ∀ b : Fin 3, (polyLift36_14 b).freeBlock=basisInt (homKind 36 14) b := by decide
def polyLift36_15 (b : Fin 3) : PolyHom 36 15 :=
  ![PolyHom.zero 36 15,PolyHom.zero 36 15,PolyHom.zero 36 15] b
theorem polyLiftFree36_15 : ∀ b : Fin 3, (polyLift36_15 b).freeBlock=basisInt (homKind 36 15) b := by decide
def polyLift36_16 (b : Fin 3) : PolyHom 36 16 :=
  ![PolyHom.zero 36 16,PolyHom.zero 36 16,PolyHom.zero 36 16] b
theorem polyLiftFree36_16 : ∀ b : Fin 3, (polyLift36_16 b).freeBlock=basisInt (homKind 36 16) b := by decide
def polyLift36_17 (b : Fin 3) : PolyHom 36 17 :=
  ![PolyHom.zero 36 17,PolyHom.zero 36 17,PolyHom.zero 36 17] b
theorem polyLiftFree36_17 : ∀ b : Fin 3, (polyLift36_17 b).freeBlock=basisInt (homKind 36 17) b := by decide
def polyLift36_18 (b : Fin 3) : PolyHom 36 18 :=
  ![PolyHom.zero 36 18,PolyHom.zero 36 18,PolyHom.zero 36 18] b
theorem polyLiftFree36_18 : ∀ b : Fin 3, (polyLift36_18 b).freeBlock=basisInt (homKind 36 18) b := by decide
def polyLift36_19 (b : Fin 3) : PolyHom 36 19 :=
  ![PolyHom.zero 36 19,PolyHom.zero 36 19,PolyHom.zero 36 19] b
theorem polyLiftFree36_19 : ∀ b : Fin 3, (polyLift36_19 b).freeBlock=basisInt (homKind 36 19) b := by decide
def polyLift36_20 (b : Fin 3) : PolyHom 36 20 :=
  ![PolyHom.zero 36 20,PolyHom.zero 36 20,PolyHom.zero 36 20] b
theorem polyLiftFree36_20 : ∀ b : Fin 3, (polyLift36_20 b).freeBlock=basisInt (homKind 36 20) b := by decide
def polyRep36_21_0 : PolyHom 36 21 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift36_21 (b : Fin 3) : PolyHom 36 21 :=
  ![polyRep36_21_0,PolyHom.zero 36 21,PolyHom.zero 36 21] b
theorem polyLiftFree36_21 : ∀ b : Fin 3, (polyLift36_21 b).freeBlock=basisInt (homKind 36 21) b := by decide
def polyRep36_22_0 : PolyHom 36 22 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift36_22 (b : Fin 3) : PolyHom 36 22 :=
  ![polyRep36_22_0,PolyHom.zero 36 22,PolyHom.zero 36 22] b
theorem polyLiftFree36_22 : ∀ b : Fin 3, (polyLift36_22 b).freeBlock=basisInt (homKind 36 22) b := by decide
def polyLift36_23 (b : Fin 3) : PolyHom 36 23 :=
  ![PolyHom.zero 36 23,PolyHom.zero 36 23,PolyHom.zero 36 23] b
theorem polyLiftFree36_23 : ∀ b : Fin 3, (polyLift36_23 b).freeBlock=basisInt (homKind 36 23) b := by decide
def polyRep36_24_0 : PolyHom 36 24 where
  M := !![(mono6 (1) 2),0,(mono6 (1) 1),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift36_24 (b : Fin 3) : PolyHom 36 24 :=
  ![polyRep36_24_0,PolyHom.zero 36 24,PolyHom.zero 36 24] b
theorem polyLiftFree36_24 : ∀ b : Fin 3, (polyLift36_24 b).freeBlock=basisInt (homKind 36 24) b := by decide
def polyRep36_25_0 : PolyHom 36 25 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift36_25 (b : Fin 3) : PolyHom 36 25 :=
  ![polyRep36_25_0,PolyHom.zero 36 25,PolyHom.zero 36 25] b
theorem polyLiftFree36_25 : ∀ b : Fin 3, (polyLift36_25 b).freeBlock=basisInt (homKind 36 25) b := by decide
def polyLift36_26 (b : Fin 3) : PolyHom 36 26 :=
  ![PolyHom.zero 36 26,PolyHom.zero 36 26,PolyHom.zero 36 26] b
theorem polyLiftFree36_26 : ∀ b : Fin 3, (polyLift36_26 b).freeBlock=basisInt (homKind 36 26) b := by decide
def polyRep36_27_0 : PolyHom 36 27 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift36_27 (b : Fin 3) : PolyHom 36 27 :=
  ![polyRep36_27_0,PolyHom.zero 36 27,PolyHom.zero 36 27] b
theorem polyLiftFree36_27 : ∀ b : Fin 3, (polyLift36_27 b).freeBlock=basisInt (homKind 36 27) b := by decide
def polyLift36_28 (b : Fin 3) : PolyHom 36 28 :=
  ![PolyHom.zero 36 28,PolyHom.zero 36 28,PolyHom.zero 36 28] b
theorem polyLiftFree36_28 : ∀ b : Fin 3, (polyLift36_28 b).freeBlock=basisInt (homKind 36 28) b := by decide
def polyLift36_29 (b : Fin 3) : PolyHom 36 29 :=
  ![PolyHom.zero 36 29,PolyHom.zero 36 29,PolyHom.zero 36 29] b
theorem polyLiftFree36_29 : ∀ b : Fin 3, (polyLift36_29 b).freeBlock=basisInt (homKind 36 29) b := by decide
def polyRep36_30_0 : PolyHom 36 30 where
  M := !![(mono6 (1) 2),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift36_30 (b : Fin 3) : PolyHom 36 30 :=
  ![polyRep36_30_0,PolyHom.zero 36 30,PolyHom.zero 36 30] b
theorem polyLiftFree36_30 : ∀ b : Fin 3, (polyLift36_30 b).freeBlock=basisInt (homKind 36 30) b := by decide
def polyRep36_31_0 : PolyHom 36 31 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift36_31 (b : Fin 3) : PolyHom 36 31 :=
  ![polyRep36_31_0,PolyHom.zero 36 31,PolyHom.zero 36 31] b
theorem polyLiftFree36_31 : ∀ b : Fin 3, (polyLift36_31 b).freeBlock=basisInt (homKind 36 31) b := by decide
def polyRep36_32_0 : PolyHom 36 32 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift36_32 (b : Fin 3) : PolyHom 36 32 :=
  ![polyRep36_32_0,PolyHom.zero 36 32,PolyHom.zero 36 32] b
theorem polyLiftFree36_32 : ∀ b : Fin 3, (polyLift36_32 b).freeBlock=basisInt (homKind 36 32) b := by decide
def polyRep36_33_0 : PolyHom 36 33 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift36_33 (b : Fin 3) : PolyHom 36 33 :=
  ![polyRep36_33_0,PolyHom.zero 36 33,PolyHom.zero 36 33] b
theorem polyLiftFree36_33 : ∀ b : Fin 3, (polyLift36_33 b).freeBlock=basisInt (homKind 36 33) b := by decide
def polyRep36_34_0 : PolyHom 36 34 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift36_34 (b : Fin 3) : PolyHom 36 34 :=
  ![polyRep36_34_0,PolyHom.zero 36 34,PolyHom.zero 36 34] b
theorem polyLiftFree36_34 : ∀ b : Fin 3, (polyLift36_34 b).freeBlock=basisInt (homKind 36 34) b := by decide
def polyLift36_35 (b : Fin 3) : PolyHom 36 35 :=
  ![PolyHom.zero 36 35,PolyHom.zero 36 35,PolyHom.zero 36 35] b
theorem polyLiftFree36_35 : ∀ b : Fin 3, (polyLift36_35 b).freeBlock=basisInt (homKind 36 35) b := by decide
def polyRep36_36_0 : PolyHom 36 36 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift36_36 (b : Fin 3) : PolyHom 36 36 :=
  ![polyRep36_36_0,PolyHom.zero 36 36,PolyHom.zero 36 36] b
theorem polyLiftFree36_36 : ∀ b : Fin 3, (polyLift36_36 b).freeBlock=basisInt (homKind 36 36) b := by decide
def polyRep36_37_0 : PolyHom 36 37 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift36_37 (b : Fin 3) : PolyHom 36 37 :=
  ![polyRep36_37_0,PolyHom.zero 36 37,PolyHom.zero 36 37] b
theorem polyLiftFree36_37 : ∀ b : Fin 3, (polyLift36_37 b).freeBlock=basisInt (homKind 36 37) b := by decide
def polyRep36_38_0 : PolyHom 36 38 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift36_38 (b : Fin 3) : PolyHom 36 38 :=
  ![polyRep36_38_0,PolyHom.zero 36 38,PolyHom.zero 36 38] b
theorem polyLiftFree36_38 : ∀ b : Fin 3, (polyLift36_38 b).freeBlock=basisInt (homKind 36 38) b := by decide
def polyRep36_39_0 : PolyHom 36 39 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift36_39 (b : Fin 3) : PolyHom 36 39 :=
  ![polyRep36_39_0,PolyHom.zero 36 39,PolyHom.zero 36 39] b
theorem polyLiftFree36_39 : ∀ b : Fin 3, (polyLift36_39 b).freeBlock=basisInt (homKind 36 39) b := by decide
def polyRep36_40_0 : PolyHom 36 40 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift36_40 (b : Fin 3) : PolyHom 36 40 :=
  ![polyRep36_40_0,PolyHom.zero 36 40,PolyHom.zero 36 40] b
theorem polyLiftFree36_40 : ∀ b : Fin 3, (polyLift36_40 b).freeBlock=basisInt (homKind 36 40) b := by decide
def polyLift36_41 (b : Fin 3) : PolyHom 36 41 :=
  ![PolyHom.zero 36 41,PolyHom.zero 36 41,PolyHom.zero 36 41] b
theorem polyLiftFree36_41 : ∀ b : Fin 3, (polyLift36_41 b).freeBlock=basisInt (homKind 36 41) b := by decide
def polyRep36_42_0 : PolyHom 36 42 where
  M := !![0,(mono6 (1) 2),0,(mono6 (-1) 0);0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift36_42 (b : Fin 3) : PolyHom 36 42 :=
  ![polyRep36_42_0,PolyHom.zero 36 42,PolyHom.zero 36 42] b
theorem polyLiftFree36_42 : ∀ b : Fin 3, (polyLift36_42 b).freeBlock=basisInt (homKind 36 42) b := by decide
def polyLift36_43 (b : Fin 3) : PolyHom 36 43 :=
  ![PolyHom.zero 36 43,PolyHom.zero 36 43,PolyHom.zero 36 43] b
theorem polyLiftFree36_43 : ∀ b : Fin 3, (polyLift36_43 b).freeBlock=basisInt (homKind 36 43) b := by decide
def polyRep36_44_0 : PolyHom 36 44 where
  M := !![(mono6 (1) 1),(mono6 (1) 2),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift36_44 (b : Fin 3) : PolyHom 36 44 :=
  ![polyRep36_44_0,PolyHom.zero 36 44,PolyHom.zero 36 44] b
theorem polyLiftFree36_44 : ∀ b : Fin 3, (polyLift36_44 b).freeBlock=basisInt (homKind 36 44) b := by decide
def polyRep36_45_0 : PolyHom 36 45 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift36_45 (b : Fin 3) : PolyHom 36 45 :=
  ![polyRep36_45_0,PolyHom.zero 36 45,PolyHom.zero 36 45] b
theorem polyLiftFree36_45 : ∀ b : Fin 3, (polyLift36_45 b).freeBlock=basisInt (homKind 36 45) b := by decide
def polyLift36_46 (b : Fin 3) : PolyHom 36 46 :=
  ![PolyHom.zero 36 46,PolyHom.zero 36 46,PolyHom.zero 36 46] b
theorem polyLiftFree36_46 : ∀ b : Fin 3, (polyLift36_46 b).freeBlock=basisInt (homKind 36 46) b := by decide
def polyLiftRow36 (j : Fin 47) (b : Fin 3) : PolyHom 36 j :=
  match j with
  | ⟨0,_⟩ => polyLift36_0 b
  | ⟨1,_⟩ => polyLift36_1 b
  | ⟨2,_⟩ => polyLift36_2 b
  | ⟨3,_⟩ => polyLift36_3 b
  | ⟨4,_⟩ => polyLift36_4 b
  | ⟨5,_⟩ => polyLift36_5 b
  | ⟨6,_⟩ => polyLift36_6 b
  | ⟨7,_⟩ => polyLift36_7 b
  | ⟨8,_⟩ => polyLift36_8 b
  | ⟨9,_⟩ => polyLift36_9 b
  | ⟨10,_⟩ => polyLift36_10 b
  | ⟨11,_⟩ => polyLift36_11 b
  | ⟨12,_⟩ => polyLift36_12 b
  | ⟨13,_⟩ => polyLift36_13 b
  | ⟨14,_⟩ => polyLift36_14 b
  | ⟨15,_⟩ => polyLift36_15 b
  | ⟨16,_⟩ => polyLift36_16 b
  | ⟨17,_⟩ => polyLift36_17 b
  | ⟨18,_⟩ => polyLift36_18 b
  | ⟨19,_⟩ => polyLift36_19 b
  | ⟨20,_⟩ => polyLift36_20 b
  | ⟨21,_⟩ => polyLift36_21 b
  | ⟨22,_⟩ => polyLift36_22 b
  | ⟨23,_⟩ => polyLift36_23 b
  | ⟨24,_⟩ => polyLift36_24 b
  | ⟨25,_⟩ => polyLift36_25 b
  | ⟨26,_⟩ => polyLift36_26 b
  | ⟨27,_⟩ => polyLift36_27 b
  | ⟨28,_⟩ => polyLift36_28 b
  | ⟨29,_⟩ => polyLift36_29 b
  | ⟨30,_⟩ => polyLift36_30 b
  | ⟨31,_⟩ => polyLift36_31 b
  | ⟨32,_⟩ => polyLift36_32 b
  | ⟨33,_⟩ => polyLift36_33 b
  | ⟨34,_⟩ => polyLift36_34 b
  | ⟨35,_⟩ => polyLift36_35 b
  | ⟨36,_⟩ => polyLift36_36 b
  | ⟨37,_⟩ => polyLift36_37 b
  | ⟨38,_⟩ => polyLift36_38 b
  | ⟨39,_⟩ => polyLift36_39 b
  | ⟨40,_⟩ => polyLift36_40 b
  | ⟨41,_⟩ => polyLift36_41 b
  | ⟨42,_⟩ => polyLift36_42 b
  | ⟨43,_⟩ => polyLift36_43 b
  | ⟨44,_⟩ => polyLift36_44 b
  | ⟨45,_⟩ => polyLift36_45 b
  | ⟨46,_⟩ => polyLift36_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree36 (j : Fin 47) (b : Fin 3) : (polyLiftRow36 j b).freeBlock=basisInt (homKind 36 j) b := by
  fin_cases j
  · exact polyLiftFree36_0 b
  · exact polyLiftFree36_1 b
  · exact polyLiftFree36_2 b
  · exact polyLiftFree36_3 b
  · exact polyLiftFree36_4 b
  · exact polyLiftFree36_5 b
  · exact polyLiftFree36_6 b
  · exact polyLiftFree36_7 b
  · exact polyLiftFree36_8 b
  · exact polyLiftFree36_9 b
  · exact polyLiftFree36_10 b
  · exact polyLiftFree36_11 b
  · exact polyLiftFree36_12 b
  · exact polyLiftFree36_13 b
  · exact polyLiftFree36_14 b
  · exact polyLiftFree36_15 b
  · exact polyLiftFree36_16 b
  · exact polyLiftFree36_17 b
  · exact polyLiftFree36_18 b
  · exact polyLiftFree36_19 b
  · exact polyLiftFree36_20 b
  · exact polyLiftFree36_21 b
  · exact polyLiftFree36_22 b
  · exact polyLiftFree36_23 b
  · exact polyLiftFree36_24 b
  · exact polyLiftFree36_25 b
  · exact polyLiftFree36_26 b
  · exact polyLiftFree36_27 b
  · exact polyLiftFree36_28 b
  · exact polyLiftFree36_29 b
  · exact polyLiftFree36_30 b
  · exact polyLiftFree36_31 b
  · exact polyLiftFree36_32 b
  · exact polyLiftFree36_33 b
  · exact polyLiftFree36_34 b
  · exact polyLiftFree36_35 b
  · exact polyLiftFree36_36 b
  · exact polyLiftFree36_37 b
  · exact polyLiftFree36_38 b
  · exact polyLiftFree36_39 b
  · exact polyLiftFree36_40 b
  · exact polyLiftFree36_41 b
  · exact polyLiftFree36_42 b
  · exact polyLiftFree36_43 b
  · exact polyLiftFree36_44 b
  · exact polyLiftFree36_45 b
  · exact polyLiftFree36_46 b
end UniserialComputations.N6
