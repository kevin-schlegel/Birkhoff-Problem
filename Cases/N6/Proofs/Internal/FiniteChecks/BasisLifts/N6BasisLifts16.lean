import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift16_0 (b : Fin 3) : PolyHom 16 0 :=
  ![PolyHom.zero 16 0,PolyHom.zero 16 0,PolyHom.zero 16 0] b
theorem polyLiftFree16_0 : ∀ b : Fin 3, (polyLift16_0 b).freeBlock=basisInt (homKind 16 0) b := by decide
def polyLift16_1 (b : Fin 3) : PolyHom 16 1 :=
  ![PolyHom.zero 16 1,PolyHom.zero 16 1,PolyHom.zero 16 1] b
theorem polyLiftFree16_1 : ∀ b : Fin 3, (polyLift16_1 b).freeBlock=basisInt (homKind 16 1) b := by decide
def polyLift16_2 (b : Fin 3) : PolyHom 16 2 :=
  ![PolyHom.zero 16 2,PolyHom.zero 16 2,PolyHom.zero 16 2] b
theorem polyLiftFree16_2 : ∀ b : Fin 3, (polyLift16_2 b).freeBlock=basisInt (homKind 16 2) b := by decide
def polyLift16_3 (b : Fin 3) : PolyHom 16 3 :=
  ![PolyHom.zero 16 3,PolyHom.zero 16 3,PolyHom.zero 16 3] b
theorem polyLiftFree16_3 : ∀ b : Fin 3, (polyLift16_3 b).freeBlock=basisInt (homKind 16 3) b := by decide
def polyLift16_4 (b : Fin 3) : PolyHom 16 4 :=
  ![PolyHom.zero 16 4,PolyHom.zero 16 4,PolyHom.zero 16 4] b
theorem polyLiftFree16_4 : ∀ b : Fin 3, (polyLift16_4 b).freeBlock=basisInt (homKind 16 4) b := by decide
def polyLift16_5 (b : Fin 3) : PolyHom 16 5 :=
  ![PolyHom.zero 16 5,PolyHom.zero 16 5,PolyHom.zero 16 5] b
theorem polyLiftFree16_5 : ∀ b : Fin 3, (polyLift16_5 b).freeBlock=basisInt (homKind 16 5) b := by decide
def polyRep16_6_0 : PolyHom 16 6 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_6 (b : Fin 3) : PolyHom 16 6 :=
  ![polyRep16_6_0,PolyHom.zero 16 6,PolyHom.zero 16 6] b
theorem polyLiftFree16_6 : ∀ b : Fin 3, (polyLift16_6 b).freeBlock=basisInt (homKind 16 6) b := by decide
def polyRep16_7_0 : PolyHom 16 7 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_7 (b : Fin 3) : PolyHom 16 7 :=
  ![polyRep16_7_0,PolyHom.zero 16 7,PolyHom.zero 16 7] b
theorem polyLiftFree16_7 : ∀ b : Fin 3, (polyLift16_7 b).freeBlock=basisInt (homKind 16 7) b := by decide
def polyLift16_8 (b : Fin 3) : PolyHom 16 8 :=
  ![PolyHom.zero 16 8,PolyHom.zero 16 8,PolyHom.zero 16 8] b
theorem polyLiftFree16_8 : ∀ b : Fin 3, (polyLift16_8 b).freeBlock=basisInt (homKind 16 8) b := by decide
def polyLift16_9 (b : Fin 3) : PolyHom 16 9 :=
  ![PolyHom.zero 16 9,PolyHom.zero 16 9,PolyHom.zero 16 9] b
theorem polyLiftFree16_9 : ∀ b : Fin 3, (polyLift16_9 b).freeBlock=basisInt (homKind 16 9) b := by decide
def polyRep16_10_0 : PolyHom 16 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_10 (b : Fin 3) : PolyHom 16 10 :=
  ![polyRep16_10_0,PolyHom.zero 16 10,PolyHom.zero 16 10] b
theorem polyLiftFree16_10 : ∀ b : Fin 3, (polyLift16_10 b).freeBlock=basisInt (homKind 16 10) b := by decide
def polyRep16_11_0 : PolyHom 16 11 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_11 (b : Fin 3) : PolyHom 16 11 :=
  ![polyRep16_11_0,PolyHom.zero 16 11,PolyHom.zero 16 11] b
theorem polyLiftFree16_11 : ∀ b : Fin 3, (polyLift16_11 b).freeBlock=basisInt (homKind 16 11) b := by decide
def polyRep16_12_0 : PolyHom 16 12 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_12 (b : Fin 3) : PolyHom 16 12 :=
  ![polyRep16_12_0,PolyHom.zero 16 12,PolyHom.zero 16 12] b
theorem polyLiftFree16_12 : ∀ b : Fin 3, (polyLift16_12 b).freeBlock=basisInt (homKind 16 12) b := by decide
def polyLift16_13 (b : Fin 3) : PolyHom 16 13 :=
  ![PolyHom.zero 16 13,PolyHom.zero 16 13,PolyHom.zero 16 13] b
theorem polyLiftFree16_13 : ∀ b : Fin 3, (polyLift16_13 b).freeBlock=basisInt (homKind 16 13) b := by decide
def polyLift16_14 (b : Fin 3) : PolyHom 16 14 :=
  ![PolyHom.zero 16 14,PolyHom.zero 16 14,PolyHom.zero 16 14] b
theorem polyLiftFree16_14 : ∀ b : Fin 3, (polyLift16_14 b).freeBlock=basisInt (homKind 16 14) b := by decide
def polyLift16_15 (b : Fin 3) : PolyHom 16 15 :=
  ![PolyHom.zero 16 15,PolyHom.zero 16 15,PolyHom.zero 16 15] b
theorem polyLiftFree16_15 : ∀ b : Fin 3, (polyLift16_15 b).freeBlock=basisInt (homKind 16 15) b := by decide
def polyRep16_16_0 : PolyHom 16 16 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_16 (b : Fin 3) : PolyHom 16 16 :=
  ![polyRep16_16_0,PolyHom.zero 16 16,PolyHom.zero 16 16] b
theorem polyLiftFree16_16 : ∀ b : Fin 3, (polyLift16_16 b).freeBlock=basisInt (homKind 16 16) b := by decide
def polyLift16_17 (b : Fin 3) : PolyHom 16 17 :=
  ![PolyHom.zero 16 17,PolyHom.zero 16 17,PolyHom.zero 16 17] b
theorem polyLiftFree16_17 : ∀ b : Fin 3, (polyLift16_17 b).freeBlock=basisInt (homKind 16 17) b := by decide
def polyLift16_18 (b : Fin 3) : PolyHom 16 18 :=
  ![PolyHom.zero 16 18,PolyHom.zero 16 18,PolyHom.zero 16 18] b
theorem polyLiftFree16_18 : ∀ b : Fin 3, (polyLift16_18 b).freeBlock=basisInt (homKind 16 18) b := by decide
def polyLift16_19 (b : Fin 3) : PolyHom 16 19 :=
  ![PolyHom.zero 16 19,PolyHom.zero 16 19,PolyHom.zero 16 19] b
theorem polyLiftFree16_19 : ∀ b : Fin 3, (polyLift16_19 b).freeBlock=basisInt (homKind 16 19) b := by decide
def polyLift16_20 (b : Fin 3) : PolyHom 16 20 :=
  ![PolyHom.zero 16 20,PolyHom.zero 16 20,PolyHom.zero 16 20] b
theorem polyLiftFree16_20 : ∀ b : Fin 3, (polyLift16_20 b).freeBlock=basisInt (homKind 16 20) b := by decide
def polyRep16_21_0 : PolyHom 16 21 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_21 (b : Fin 3) : PolyHom 16 21 :=
  ![polyRep16_21_0,PolyHom.zero 16 21,PolyHom.zero 16 21] b
theorem polyLiftFree16_21 : ∀ b : Fin 3, (polyLift16_21 b).freeBlock=basisInt (homKind 16 21) b := by decide
def polyRep16_22_0 : PolyHom 16 22 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_22 (b : Fin 3) : PolyHom 16 22 :=
  ![polyRep16_22_0,PolyHom.zero 16 22,PolyHom.zero 16 22] b
theorem polyLiftFree16_22 : ∀ b : Fin 3, (polyLift16_22 b).freeBlock=basisInt (homKind 16 22) b := by decide
def polyLift16_23 (b : Fin 3) : PolyHom 16 23 :=
  ![PolyHom.zero 16 23,PolyHom.zero 16 23,PolyHom.zero 16 23] b
theorem polyLiftFree16_23 : ∀ b : Fin 3, (polyLift16_23 b).freeBlock=basisInt (homKind 16 23) b := by decide
def polyRep16_24_0 : PolyHom 16 24 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_24 (b : Fin 3) : PolyHom 16 24 :=
  ![polyRep16_24_0,PolyHom.zero 16 24,PolyHom.zero 16 24] b
theorem polyLiftFree16_24 : ∀ b : Fin 3, (polyLift16_24 b).freeBlock=basisInt (homKind 16 24) b := by decide
def polyRep16_25_0 : PolyHom 16 25 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_25 (b : Fin 3) : PolyHom 16 25 :=
  ![polyRep16_25_0,PolyHom.zero 16 25,PolyHom.zero 16 25] b
theorem polyLiftFree16_25 : ∀ b : Fin 3, (polyLift16_25 b).freeBlock=basisInt (homKind 16 25) b := by decide
def polyLift16_26 (b : Fin 3) : PolyHom 16 26 :=
  ![PolyHom.zero 16 26,PolyHom.zero 16 26,PolyHom.zero 16 26] b
theorem polyLiftFree16_26 : ∀ b : Fin 3, (polyLift16_26 b).freeBlock=basisInt (homKind 16 26) b := by decide
def polyRep16_27_0 : PolyHom 16 27 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_27 (b : Fin 3) : PolyHom 16 27 :=
  ![polyRep16_27_0,PolyHom.zero 16 27,PolyHom.zero 16 27] b
theorem polyLiftFree16_27 : ∀ b : Fin 3, (polyLift16_27 b).freeBlock=basisInt (homKind 16 27) b := by decide
def polyLift16_28 (b : Fin 3) : PolyHom 16 28 :=
  ![PolyHom.zero 16 28,PolyHom.zero 16 28,PolyHom.zero 16 28] b
theorem polyLiftFree16_28 : ∀ b : Fin 3, (polyLift16_28 b).freeBlock=basisInt (homKind 16 28) b := by decide
def polyLift16_29 (b : Fin 3) : PolyHom 16 29 :=
  ![PolyHom.zero 16 29,PolyHom.zero 16 29,PolyHom.zero 16 29] b
theorem polyLiftFree16_29 : ∀ b : Fin 3, (polyLift16_29 b).freeBlock=basisInt (homKind 16 29) b := by decide
def polyRep16_30_0 : PolyHom 16 30 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_30 (b : Fin 3) : PolyHom 16 30 :=
  ![polyRep16_30_0,PolyHom.zero 16 30,PolyHom.zero 16 30] b
theorem polyLiftFree16_30 : ∀ b : Fin 3, (polyLift16_30 b).freeBlock=basisInt (homKind 16 30) b := by decide
def polyRep16_31_0 : PolyHom 16 31 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_31 (b : Fin 3) : PolyHom 16 31 :=
  ![polyRep16_31_0,PolyHom.zero 16 31,PolyHom.zero 16 31] b
theorem polyLiftFree16_31 : ∀ b : Fin 3, (polyLift16_31 b).freeBlock=basisInt (homKind 16 31) b := by decide
def polyRep16_32_0 : PolyHom 16 32 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_32 (b : Fin 3) : PolyHom 16 32 :=
  ![polyRep16_32_0,PolyHom.zero 16 32,PolyHom.zero 16 32] b
theorem polyLiftFree16_32 : ∀ b : Fin 3, (polyLift16_32 b).freeBlock=basisInt (homKind 16 32) b := by decide
def polyRep16_33_0 : PolyHom 16 33 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_33 (b : Fin 3) : PolyHom 16 33 :=
  ![polyRep16_33_0,PolyHom.zero 16 33,PolyHom.zero 16 33] b
theorem polyLiftFree16_33 : ∀ b : Fin 3, (polyLift16_33 b).freeBlock=basisInt (homKind 16 33) b := by decide
def polyRep16_34_0 : PolyHom 16 34 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_34 (b : Fin 3) : PolyHom 16 34 :=
  ![polyRep16_34_0,PolyHom.zero 16 34,PolyHom.zero 16 34] b
theorem polyLiftFree16_34 : ∀ b : Fin 3, (polyLift16_34 b).freeBlock=basisInt (homKind 16 34) b := by decide
def polyLift16_35 (b : Fin 3) : PolyHom 16 35 :=
  ![PolyHom.zero 16 35,PolyHom.zero 16 35,PolyHom.zero 16 35] b
theorem polyLiftFree16_35 : ∀ b : Fin 3, (polyLift16_35 b).freeBlock=basisInt (homKind 16 35) b := by decide
def polyRep16_36_0 : PolyHom 16 36 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_36 (b : Fin 3) : PolyHom 16 36 :=
  ![polyRep16_36_0,PolyHom.zero 16 36,PolyHom.zero 16 36] b
theorem polyLiftFree16_36 : ∀ b : Fin 3, (polyLift16_36 b).freeBlock=basisInt (homKind 16 36) b := by decide
def polyRep16_37_0 : PolyHom 16 37 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_37 (b : Fin 3) : PolyHom 16 37 :=
  ![polyRep16_37_0,PolyHom.zero 16 37,PolyHom.zero 16 37] b
theorem polyLiftFree16_37 : ∀ b : Fin 3, (polyLift16_37 b).freeBlock=basisInt (homKind 16 37) b := by decide
def polyRep16_38_0 : PolyHom 16 38 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_38 (b : Fin 3) : PolyHom 16 38 :=
  ![polyRep16_38_0,PolyHom.zero 16 38,PolyHom.zero 16 38] b
theorem polyLiftFree16_38 : ∀ b : Fin 3, (polyLift16_38 b).freeBlock=basisInt (homKind 16 38) b := by decide
def polyRep16_39_0 : PolyHom 16 39 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_39 (b : Fin 3) : PolyHom 16 39 :=
  ![polyRep16_39_0,PolyHom.zero 16 39,PolyHom.zero 16 39] b
theorem polyLiftFree16_39 : ∀ b : Fin 3, (polyLift16_39 b).freeBlock=basisInt (homKind 16 39) b := by decide
def polyRep16_40_0 : PolyHom 16 40 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_40 (b : Fin 3) : PolyHom 16 40 :=
  ![polyRep16_40_0,PolyHom.zero 16 40,PolyHom.zero 16 40] b
theorem polyLiftFree16_40 : ∀ b : Fin 3, (polyLift16_40 b).freeBlock=basisInt (homKind 16 40) b := by decide
def polyLift16_41 (b : Fin 3) : PolyHom 16 41 :=
  ![PolyHom.zero 16 41,PolyHom.zero 16 41,PolyHom.zero 16 41] b
theorem polyLiftFree16_41 : ∀ b : Fin 3, (polyLift16_41 b).freeBlock=basisInt (homKind 16 41) b := by decide
def polyRep16_42_0 : PolyHom 16 42 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_42 (b : Fin 3) : PolyHom 16 42 :=
  ![polyRep16_42_0,PolyHom.zero 16 42,PolyHom.zero 16 42] b
theorem polyLiftFree16_42 : ∀ b : Fin 3, (polyLift16_42 b).freeBlock=basisInt (homKind 16 42) b := by decide
def polyLift16_43 (b : Fin 3) : PolyHom 16 43 :=
  ![PolyHom.zero 16 43,PolyHom.zero 16 43,PolyHom.zero 16 43] b
theorem polyLiftFree16_43 : ∀ b : Fin 3, (polyLift16_43 b).freeBlock=basisInt (homKind 16 43) b := by decide
def polyRep16_44_0 : PolyHom 16 44 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_44 (b : Fin 3) : PolyHom 16 44 :=
  ![polyRep16_44_0,PolyHom.zero 16 44,PolyHom.zero 16 44] b
theorem polyLiftFree16_44 : ∀ b : Fin 3, (polyLift16_44 b).freeBlock=basisInt (homKind 16 44) b := by decide
def polyRep16_45_0 : PolyHom 16 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift16_45 (b : Fin 3) : PolyHom 16 45 :=
  ![polyRep16_45_0,PolyHom.zero 16 45,PolyHom.zero 16 45] b
theorem polyLiftFree16_45 : ∀ b : Fin 3, (polyLift16_45 b).freeBlock=basisInt (homKind 16 45) b := by decide
def polyLift16_46 (b : Fin 3) : PolyHom 16 46 :=
  ![PolyHom.zero 16 46,PolyHom.zero 16 46,PolyHom.zero 16 46] b
theorem polyLiftFree16_46 : ∀ b : Fin 3, (polyLift16_46 b).freeBlock=basisInt (homKind 16 46) b := by decide
def polyLiftRow16 (j : Fin 47) (b : Fin 3) : PolyHom 16 j :=
  match j with
  | ⟨0,_⟩ => polyLift16_0 b
  | ⟨1,_⟩ => polyLift16_1 b
  | ⟨2,_⟩ => polyLift16_2 b
  | ⟨3,_⟩ => polyLift16_3 b
  | ⟨4,_⟩ => polyLift16_4 b
  | ⟨5,_⟩ => polyLift16_5 b
  | ⟨6,_⟩ => polyLift16_6 b
  | ⟨7,_⟩ => polyLift16_7 b
  | ⟨8,_⟩ => polyLift16_8 b
  | ⟨9,_⟩ => polyLift16_9 b
  | ⟨10,_⟩ => polyLift16_10 b
  | ⟨11,_⟩ => polyLift16_11 b
  | ⟨12,_⟩ => polyLift16_12 b
  | ⟨13,_⟩ => polyLift16_13 b
  | ⟨14,_⟩ => polyLift16_14 b
  | ⟨15,_⟩ => polyLift16_15 b
  | ⟨16,_⟩ => polyLift16_16 b
  | ⟨17,_⟩ => polyLift16_17 b
  | ⟨18,_⟩ => polyLift16_18 b
  | ⟨19,_⟩ => polyLift16_19 b
  | ⟨20,_⟩ => polyLift16_20 b
  | ⟨21,_⟩ => polyLift16_21 b
  | ⟨22,_⟩ => polyLift16_22 b
  | ⟨23,_⟩ => polyLift16_23 b
  | ⟨24,_⟩ => polyLift16_24 b
  | ⟨25,_⟩ => polyLift16_25 b
  | ⟨26,_⟩ => polyLift16_26 b
  | ⟨27,_⟩ => polyLift16_27 b
  | ⟨28,_⟩ => polyLift16_28 b
  | ⟨29,_⟩ => polyLift16_29 b
  | ⟨30,_⟩ => polyLift16_30 b
  | ⟨31,_⟩ => polyLift16_31 b
  | ⟨32,_⟩ => polyLift16_32 b
  | ⟨33,_⟩ => polyLift16_33 b
  | ⟨34,_⟩ => polyLift16_34 b
  | ⟨35,_⟩ => polyLift16_35 b
  | ⟨36,_⟩ => polyLift16_36 b
  | ⟨37,_⟩ => polyLift16_37 b
  | ⟨38,_⟩ => polyLift16_38 b
  | ⟨39,_⟩ => polyLift16_39 b
  | ⟨40,_⟩ => polyLift16_40 b
  | ⟨41,_⟩ => polyLift16_41 b
  | ⟨42,_⟩ => polyLift16_42 b
  | ⟨43,_⟩ => polyLift16_43 b
  | ⟨44,_⟩ => polyLift16_44 b
  | ⟨45,_⟩ => polyLift16_45 b
  | ⟨46,_⟩ => polyLift16_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree16 (j : Fin 47) (b : Fin 3) : (polyLiftRow16 j b).freeBlock=basisInt (homKind 16 j) b := by
  fin_cases j
  · exact polyLiftFree16_0 b
  · exact polyLiftFree16_1 b
  · exact polyLiftFree16_2 b
  · exact polyLiftFree16_3 b
  · exact polyLiftFree16_4 b
  · exact polyLiftFree16_5 b
  · exact polyLiftFree16_6 b
  · exact polyLiftFree16_7 b
  · exact polyLiftFree16_8 b
  · exact polyLiftFree16_9 b
  · exact polyLiftFree16_10 b
  · exact polyLiftFree16_11 b
  · exact polyLiftFree16_12 b
  · exact polyLiftFree16_13 b
  · exact polyLiftFree16_14 b
  · exact polyLiftFree16_15 b
  · exact polyLiftFree16_16 b
  · exact polyLiftFree16_17 b
  · exact polyLiftFree16_18 b
  · exact polyLiftFree16_19 b
  · exact polyLiftFree16_20 b
  · exact polyLiftFree16_21 b
  · exact polyLiftFree16_22 b
  · exact polyLiftFree16_23 b
  · exact polyLiftFree16_24 b
  · exact polyLiftFree16_25 b
  · exact polyLiftFree16_26 b
  · exact polyLiftFree16_27 b
  · exact polyLiftFree16_28 b
  · exact polyLiftFree16_29 b
  · exact polyLiftFree16_30 b
  · exact polyLiftFree16_31 b
  · exact polyLiftFree16_32 b
  · exact polyLiftFree16_33 b
  · exact polyLiftFree16_34 b
  · exact polyLiftFree16_35 b
  · exact polyLiftFree16_36 b
  · exact polyLiftFree16_37 b
  · exact polyLiftFree16_38 b
  · exact polyLiftFree16_39 b
  · exact polyLiftFree16_40 b
  · exact polyLiftFree16_41 b
  · exact polyLiftFree16_42 b
  · exact polyLiftFree16_43 b
  · exact polyLiftFree16_44 b
  · exact polyLiftFree16_45 b
  · exact polyLiftFree16_46 b
end UniserialComputations.N6
