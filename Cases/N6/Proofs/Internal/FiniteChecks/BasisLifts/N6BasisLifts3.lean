import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift3_0 (b : Fin 3) : PolyHom 3 0 :=
  ![PolyHom.zero 3 0,PolyHom.zero 3 0,PolyHom.zero 3 0] b
theorem polyLiftFree3_0 : ∀ b : Fin 3, (polyLift3_0 b).freeBlock=basisInt (homKind 3 0) b := by decide
def polyLift3_1 (b : Fin 3) : PolyHom 3 1 :=
  ![PolyHom.zero 3 1,PolyHom.zero 3 1,PolyHom.zero 3 1] b
theorem polyLiftFree3_1 : ∀ b : Fin 3, (polyLift3_1 b).freeBlock=basisInt (homKind 3 1) b := by decide
def polyLift3_2 (b : Fin 3) : PolyHom 3 2 :=
  ![PolyHom.zero 3 2,PolyHom.zero 3 2,PolyHom.zero 3 2] b
theorem polyLiftFree3_2 : ∀ b : Fin 3, (polyLift3_2 b).freeBlock=basisInt (homKind 3 2) b := by decide
def polyRep3_3_0 : PolyHom 3 3 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_3 (b : Fin 3) : PolyHom 3 3 :=
  ![polyRep3_3_0,PolyHom.zero 3 3,PolyHom.zero 3 3] b
theorem polyLiftFree3_3 : ∀ b : Fin 3, (polyLift3_3 b).freeBlock=basisInt (homKind 3 3) b := by decide
def polyLift3_4 (b : Fin 3) : PolyHom 3 4 :=
  ![PolyHom.zero 3 4,PolyHom.zero 3 4,PolyHom.zero 3 4] b
theorem polyLiftFree3_4 : ∀ b : Fin 3, (polyLift3_4 b).freeBlock=basisInt (homKind 3 4) b := by decide
def polyLift3_5 (b : Fin 3) : PolyHom 3 5 :=
  ![PolyHom.zero 3 5,PolyHom.zero 3 5,PolyHom.zero 3 5] b
theorem polyLiftFree3_5 : ∀ b : Fin 3, (polyLift3_5 b).freeBlock=basisInt (homKind 3 5) b := by decide
def polyRep3_6_0 : PolyHom 3 6 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_6 (b : Fin 3) : PolyHom 3 6 :=
  ![polyRep3_6_0,PolyHom.zero 3 6,PolyHom.zero 3 6] b
theorem polyLiftFree3_6 : ∀ b : Fin 3, (polyLift3_6 b).freeBlock=basisInt (homKind 3 6) b := by decide
def polyRep3_7_0 : PolyHom 3 7 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_7 (b : Fin 3) : PolyHom 3 7 :=
  ![polyRep3_7_0,PolyHom.zero 3 7,PolyHom.zero 3 7] b
theorem polyLiftFree3_7 : ∀ b : Fin 3, (polyLift3_7 b).freeBlock=basisInt (homKind 3 7) b := by decide
def polyLift3_8 (b : Fin 3) : PolyHom 3 8 :=
  ![PolyHom.zero 3 8,PolyHom.zero 3 8,PolyHom.zero 3 8] b
theorem polyLiftFree3_8 : ∀ b : Fin 3, (polyLift3_8 b).freeBlock=basisInt (homKind 3 8) b := by decide
def polyLift3_9 (b : Fin 3) : PolyHom 3 9 :=
  ![PolyHom.zero 3 9,PolyHom.zero 3 9,PolyHom.zero 3 9] b
theorem polyLiftFree3_9 : ∀ b : Fin 3, (polyLift3_9 b).freeBlock=basisInt (homKind 3 9) b := by decide
def polyRep3_10_0 : PolyHom 3 10 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_10 (b : Fin 3) : PolyHom 3 10 :=
  ![polyRep3_10_0,PolyHom.zero 3 10,PolyHom.zero 3 10] b
theorem polyLiftFree3_10 : ∀ b : Fin 3, (polyLift3_10 b).freeBlock=basisInt (homKind 3 10) b := by decide
def polyRep3_11_0 : PolyHom 3 11 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_11 (b : Fin 3) : PolyHom 3 11 :=
  ![polyRep3_11_0,PolyHom.zero 3 11,PolyHom.zero 3 11] b
theorem polyLiftFree3_11 : ∀ b : Fin 3, (polyLift3_11 b).freeBlock=basisInt (homKind 3 11) b := by decide
def polyRep3_12_0 : PolyHom 3 12 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_12 (b : Fin 3) : PolyHom 3 12 :=
  ![polyRep3_12_0,PolyHom.zero 3 12,PolyHom.zero 3 12] b
theorem polyLiftFree3_12 : ∀ b : Fin 3, (polyLift3_12 b).freeBlock=basisInt (homKind 3 12) b := by decide
def polyLift3_13 (b : Fin 3) : PolyHom 3 13 :=
  ![PolyHom.zero 3 13,PolyHom.zero 3 13,PolyHom.zero 3 13] b
theorem polyLiftFree3_13 : ∀ b : Fin 3, (polyLift3_13 b).freeBlock=basisInt (homKind 3 13) b := by decide
def polyLift3_14 (b : Fin 3) : PolyHom 3 14 :=
  ![PolyHom.zero 3 14,PolyHom.zero 3 14,PolyHom.zero 3 14] b
theorem polyLiftFree3_14 : ∀ b : Fin 3, (polyLift3_14 b).freeBlock=basisInt (homKind 3 14) b := by decide
def polyLift3_15 (b : Fin 3) : PolyHom 3 15 :=
  ![PolyHom.zero 3 15,PolyHom.zero 3 15,PolyHom.zero 3 15] b
theorem polyLiftFree3_15 : ∀ b : Fin 3, (polyLift3_15 b).freeBlock=basisInt (homKind 3 15) b := by decide
def polyRep3_16_0 : PolyHom 3 16 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_16 (b : Fin 3) : PolyHom 3 16 :=
  ![polyRep3_16_0,PolyHom.zero 3 16,PolyHom.zero 3 16] b
theorem polyLiftFree3_16 : ∀ b : Fin 3, (polyLift3_16 b).freeBlock=basisInt (homKind 3 16) b := by decide
def polyLift3_17 (b : Fin 3) : PolyHom 3 17 :=
  ![PolyHom.zero 3 17,PolyHom.zero 3 17,PolyHom.zero 3 17] b
theorem polyLiftFree3_17 : ∀ b : Fin 3, (polyLift3_17 b).freeBlock=basisInt (homKind 3 17) b := by decide
def polyRep3_18_0 : PolyHom 3 18 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_18 (b : Fin 3) : PolyHom 3 18 :=
  ![polyRep3_18_0,PolyHom.zero 3 18,PolyHom.zero 3 18] b
theorem polyLiftFree3_18 : ∀ b : Fin 3, (polyLift3_18 b).freeBlock=basisInt (homKind 3 18) b := by decide
def polyRep3_19_0 : PolyHom 3 19 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_19 (b : Fin 3) : PolyHom 3 19 :=
  ![polyRep3_19_0,PolyHom.zero 3 19,PolyHom.zero 3 19] b
theorem polyLiftFree3_19 : ∀ b : Fin 3, (polyLift3_19 b).freeBlock=basisInt (homKind 3 19) b := by decide
def polyLift3_20 (b : Fin 3) : PolyHom 3 20 :=
  ![PolyHom.zero 3 20,PolyHom.zero 3 20,PolyHom.zero 3 20] b
theorem polyLiftFree3_20 : ∀ b : Fin 3, (polyLift3_20 b).freeBlock=basisInt (homKind 3 20) b := by decide
def polyRep3_21_0 : PolyHom 3 21 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_21 (b : Fin 3) : PolyHom 3 21 :=
  ![polyRep3_21_0,PolyHom.zero 3 21,PolyHom.zero 3 21] b
theorem polyLiftFree3_21 : ∀ b : Fin 3, (polyLift3_21 b).freeBlock=basisInt (homKind 3 21) b := by decide
def polyRep3_22_0 : PolyHom 3 22 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_22 (b : Fin 3) : PolyHom 3 22 :=
  ![polyRep3_22_0,PolyHom.zero 3 22,PolyHom.zero 3 22] b
theorem polyLiftFree3_22 : ∀ b : Fin 3, (polyLift3_22 b).freeBlock=basisInt (homKind 3 22) b := by decide
def polyLift3_23 (b : Fin 3) : PolyHom 3 23 :=
  ![PolyHom.zero 3 23,PolyHom.zero 3 23,PolyHom.zero 3 23] b
theorem polyLiftFree3_23 : ∀ b : Fin 3, (polyLift3_23 b).freeBlock=basisInt (homKind 3 23) b := by decide
def polyRep3_24_0 : PolyHom 3 24 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_24 (b : Fin 3) : PolyHom 3 24 :=
  ![polyRep3_24_0,PolyHom.zero 3 24,PolyHom.zero 3 24] b
theorem polyLiftFree3_24 : ∀ b : Fin 3, (polyLift3_24 b).freeBlock=basisInt (homKind 3 24) b := by decide
def polyRep3_25_0 : PolyHom 3 25 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_25 (b : Fin 3) : PolyHom 3 25 :=
  ![polyRep3_25_0,PolyHom.zero 3 25,PolyHom.zero 3 25] b
theorem polyLiftFree3_25 : ∀ b : Fin 3, (polyLift3_25 b).freeBlock=basisInt (homKind 3 25) b := by decide
def polyRep3_26_0 : PolyHom 3 26 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_26 (b : Fin 3) : PolyHom 3 26 :=
  ![polyRep3_26_0,PolyHom.zero 3 26,PolyHom.zero 3 26] b
theorem polyLiftFree3_26 : ∀ b : Fin 3, (polyLift3_26 b).freeBlock=basisInt (homKind 3 26) b := by decide
def polyRep3_27_0 : PolyHom 3 27 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_27 (b : Fin 3) : PolyHom 3 27 :=
  ![polyRep3_27_0,PolyHom.zero 3 27,PolyHom.zero 3 27] b
theorem polyLiftFree3_27 : ∀ b : Fin 3, (polyLift3_27 b).freeBlock=basisInt (homKind 3 27) b := by decide
def polyRep3_28_0 : PolyHom 3 28 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_28 (b : Fin 3) : PolyHom 3 28 :=
  ![polyRep3_28_0,PolyHom.zero 3 28,PolyHom.zero 3 28] b
theorem polyLiftFree3_28 : ∀ b : Fin 3, (polyLift3_28 b).freeBlock=basisInt (homKind 3 28) b := by decide
def polyLift3_29 (b : Fin 3) : PolyHom 3 29 :=
  ![PolyHom.zero 3 29,PolyHom.zero 3 29,PolyHom.zero 3 29] b
theorem polyLiftFree3_29 : ∀ b : Fin 3, (polyLift3_29 b).freeBlock=basisInt (homKind 3 29) b := by decide
def polyRep3_30_0 : PolyHom 3 30 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_30 (b : Fin 3) : PolyHom 3 30 :=
  ![polyRep3_30_0,PolyHom.zero 3 30,PolyHom.zero 3 30] b
theorem polyLiftFree3_30 : ∀ b : Fin 3, (polyLift3_30 b).freeBlock=basisInt (homKind 3 30) b := by decide
def polyRep3_31_0 : PolyHom 3 31 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_31 (b : Fin 3) : PolyHom 3 31 :=
  ![polyRep3_31_0,PolyHom.zero 3 31,PolyHom.zero 3 31] b
theorem polyLiftFree3_31 : ∀ b : Fin 3, (polyLift3_31 b).freeBlock=basisInt (homKind 3 31) b := by decide
def polyRep3_32_0 : PolyHom 3 32 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_32 (b : Fin 3) : PolyHom 3 32 :=
  ![polyRep3_32_0,PolyHom.zero 3 32,PolyHom.zero 3 32] b
theorem polyLiftFree3_32 : ∀ b : Fin 3, (polyLift3_32 b).freeBlock=basisInt (homKind 3 32) b := by decide
def polyRep3_33_0 : PolyHom 3 33 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_33 (b : Fin 3) : PolyHom 3 33 :=
  ![polyRep3_33_0,PolyHom.zero 3 33,PolyHom.zero 3 33] b
theorem polyLiftFree3_33 : ∀ b : Fin 3, (polyLift3_33 b).freeBlock=basisInt (homKind 3 33) b := by decide
def polyRep3_34_0 : PolyHom 3 34 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_34 (b : Fin 3) : PolyHom 3 34 :=
  ![polyRep3_34_0,PolyHom.zero 3 34,PolyHom.zero 3 34] b
theorem polyLiftFree3_34 : ∀ b : Fin 3, (polyLift3_34 b).freeBlock=basisInt (homKind 3 34) b := by decide
def polyLift3_35 (b : Fin 3) : PolyHom 3 35 :=
  ![PolyHom.zero 3 35,PolyHom.zero 3 35,PolyHom.zero 3 35] b
theorem polyLiftFree3_35 : ∀ b : Fin 3, (polyLift3_35 b).freeBlock=basisInt (homKind 3 35) b := by decide
def polyRep3_36_0 : PolyHom 3 36 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_36 (b : Fin 3) : PolyHom 3 36 :=
  ![polyRep3_36_0,PolyHom.zero 3 36,PolyHom.zero 3 36] b
theorem polyLiftFree3_36 : ∀ b : Fin 3, (polyLift3_36 b).freeBlock=basisInt (homKind 3 36) b := by decide
def polyRep3_37_0 : PolyHom 3 37 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_37 (b : Fin 3) : PolyHom 3 37 :=
  ![polyRep3_37_0,PolyHom.zero 3 37,PolyHom.zero 3 37] b
theorem polyLiftFree3_37 : ∀ b : Fin 3, (polyLift3_37 b).freeBlock=basisInt (homKind 3 37) b := by decide
def polyRep3_38_0 : PolyHom 3 38 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_38 (b : Fin 3) : PolyHom 3 38 :=
  ![polyRep3_38_0,PolyHom.zero 3 38,PolyHom.zero 3 38] b
theorem polyLiftFree3_38 : ∀ b : Fin 3, (polyLift3_38 b).freeBlock=basisInt (homKind 3 38) b := by decide
def polyRep3_39_0 : PolyHom 3 39 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_39 (b : Fin 3) : PolyHom 3 39 :=
  ![polyRep3_39_0,PolyHom.zero 3 39,PolyHom.zero 3 39] b
theorem polyLiftFree3_39 : ∀ b : Fin 3, (polyLift3_39 b).freeBlock=basisInt (homKind 3 39) b := by decide
def polyRep3_40_0 : PolyHom 3 40 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_40 (b : Fin 3) : PolyHom 3 40 :=
  ![polyRep3_40_0,PolyHom.zero 3 40,PolyHom.zero 3 40] b
theorem polyLiftFree3_40 : ∀ b : Fin 3, (polyLift3_40 b).freeBlock=basisInt (homKind 3 40) b := by decide
def polyRep3_41_0 : PolyHom 3 41 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_41 (b : Fin 3) : PolyHom 3 41 :=
  ![polyRep3_41_0,PolyHom.zero 3 41,PolyHom.zero 3 41] b
theorem polyLiftFree3_41 : ∀ b : Fin 3, (polyLift3_41 b).freeBlock=basisInt (homKind 3 41) b := by decide
def polyRep3_42_0 : PolyHom 3 42 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_42 (b : Fin 3) : PolyHom 3 42 :=
  ![polyRep3_42_0,PolyHom.zero 3 42,PolyHom.zero 3 42] b
theorem polyLiftFree3_42 : ∀ b : Fin 3, (polyLift3_42 b).freeBlock=basisInt (homKind 3 42) b := by decide
def polyRep3_43_0 : PolyHom 3 43 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_43 (b : Fin 3) : PolyHom 3 43 :=
  ![polyRep3_43_0,PolyHom.zero 3 43,PolyHom.zero 3 43] b
theorem polyLiftFree3_43 : ∀ b : Fin 3, (polyLift3_43 b).freeBlock=basisInt (homKind 3 43) b := by decide
def polyRep3_44_0 : PolyHom 3 44 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_44 (b : Fin 3) : PolyHom 3 44 :=
  ![polyRep3_44_0,PolyHom.zero 3 44,PolyHom.zero 3 44] b
theorem polyLiftFree3_44 : ∀ b : Fin 3, (polyLift3_44 b).freeBlock=basisInt (homKind 3 44) b := by decide
def polyRep3_45_0 : PolyHom 3 45 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift3_45 (b : Fin 3) : PolyHom 3 45 :=
  ![polyRep3_45_0,PolyHom.zero 3 45,PolyHom.zero 3 45] b
theorem polyLiftFree3_45 : ∀ b : Fin 3, (polyLift3_45 b).freeBlock=basisInt (homKind 3 45) b := by decide
def polyLift3_46 (b : Fin 3) : PolyHom 3 46 :=
  ![PolyHom.zero 3 46,PolyHom.zero 3 46,PolyHom.zero 3 46] b
theorem polyLiftFree3_46 : ∀ b : Fin 3, (polyLift3_46 b).freeBlock=basisInt (homKind 3 46) b := by decide
def polyLiftRow3 (j : Fin 47) (b : Fin 3) : PolyHom 3 j :=
  match j with
  | ⟨0,_⟩ => polyLift3_0 b
  | ⟨1,_⟩ => polyLift3_1 b
  | ⟨2,_⟩ => polyLift3_2 b
  | ⟨3,_⟩ => polyLift3_3 b
  | ⟨4,_⟩ => polyLift3_4 b
  | ⟨5,_⟩ => polyLift3_5 b
  | ⟨6,_⟩ => polyLift3_6 b
  | ⟨7,_⟩ => polyLift3_7 b
  | ⟨8,_⟩ => polyLift3_8 b
  | ⟨9,_⟩ => polyLift3_9 b
  | ⟨10,_⟩ => polyLift3_10 b
  | ⟨11,_⟩ => polyLift3_11 b
  | ⟨12,_⟩ => polyLift3_12 b
  | ⟨13,_⟩ => polyLift3_13 b
  | ⟨14,_⟩ => polyLift3_14 b
  | ⟨15,_⟩ => polyLift3_15 b
  | ⟨16,_⟩ => polyLift3_16 b
  | ⟨17,_⟩ => polyLift3_17 b
  | ⟨18,_⟩ => polyLift3_18 b
  | ⟨19,_⟩ => polyLift3_19 b
  | ⟨20,_⟩ => polyLift3_20 b
  | ⟨21,_⟩ => polyLift3_21 b
  | ⟨22,_⟩ => polyLift3_22 b
  | ⟨23,_⟩ => polyLift3_23 b
  | ⟨24,_⟩ => polyLift3_24 b
  | ⟨25,_⟩ => polyLift3_25 b
  | ⟨26,_⟩ => polyLift3_26 b
  | ⟨27,_⟩ => polyLift3_27 b
  | ⟨28,_⟩ => polyLift3_28 b
  | ⟨29,_⟩ => polyLift3_29 b
  | ⟨30,_⟩ => polyLift3_30 b
  | ⟨31,_⟩ => polyLift3_31 b
  | ⟨32,_⟩ => polyLift3_32 b
  | ⟨33,_⟩ => polyLift3_33 b
  | ⟨34,_⟩ => polyLift3_34 b
  | ⟨35,_⟩ => polyLift3_35 b
  | ⟨36,_⟩ => polyLift3_36 b
  | ⟨37,_⟩ => polyLift3_37 b
  | ⟨38,_⟩ => polyLift3_38 b
  | ⟨39,_⟩ => polyLift3_39 b
  | ⟨40,_⟩ => polyLift3_40 b
  | ⟨41,_⟩ => polyLift3_41 b
  | ⟨42,_⟩ => polyLift3_42 b
  | ⟨43,_⟩ => polyLift3_43 b
  | ⟨44,_⟩ => polyLift3_44 b
  | ⟨45,_⟩ => polyLift3_45 b
  | ⟨46,_⟩ => polyLift3_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree3 (j : Fin 47) (b : Fin 3) : (polyLiftRow3 j b).freeBlock=basisInt (homKind 3 j) b := by
  fin_cases j
  · exact polyLiftFree3_0 b
  · exact polyLiftFree3_1 b
  · exact polyLiftFree3_2 b
  · exact polyLiftFree3_3 b
  · exact polyLiftFree3_4 b
  · exact polyLiftFree3_5 b
  · exact polyLiftFree3_6 b
  · exact polyLiftFree3_7 b
  · exact polyLiftFree3_8 b
  · exact polyLiftFree3_9 b
  · exact polyLiftFree3_10 b
  · exact polyLiftFree3_11 b
  · exact polyLiftFree3_12 b
  · exact polyLiftFree3_13 b
  · exact polyLiftFree3_14 b
  · exact polyLiftFree3_15 b
  · exact polyLiftFree3_16 b
  · exact polyLiftFree3_17 b
  · exact polyLiftFree3_18 b
  · exact polyLiftFree3_19 b
  · exact polyLiftFree3_20 b
  · exact polyLiftFree3_21 b
  · exact polyLiftFree3_22 b
  · exact polyLiftFree3_23 b
  · exact polyLiftFree3_24 b
  · exact polyLiftFree3_25 b
  · exact polyLiftFree3_26 b
  · exact polyLiftFree3_27 b
  · exact polyLiftFree3_28 b
  · exact polyLiftFree3_29 b
  · exact polyLiftFree3_30 b
  · exact polyLiftFree3_31 b
  · exact polyLiftFree3_32 b
  · exact polyLiftFree3_33 b
  · exact polyLiftFree3_34 b
  · exact polyLiftFree3_35 b
  · exact polyLiftFree3_36 b
  · exact polyLiftFree3_37 b
  · exact polyLiftFree3_38 b
  · exact polyLiftFree3_39 b
  · exact polyLiftFree3_40 b
  · exact polyLiftFree3_41 b
  · exact polyLiftFree3_42 b
  · exact polyLiftFree3_43 b
  · exact polyLiftFree3_44 b
  · exact polyLiftFree3_45 b
  · exact polyLiftFree3_46 b
end UniserialComputations.N6
