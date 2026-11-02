import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift44_0 (b : Fin 3) : PolyHom 44 0 :=
  ![PolyHom.zero 44 0,PolyHom.zero 44 0,PolyHom.zero 44 0] b
theorem polyLiftFree44_0 : ∀ b : Fin 3, (polyLift44_0 b).freeBlock=basisInt (homKind 44 0) b := by decide
def polyLift44_1 (b : Fin 3) : PolyHom 44 1 :=
  ![PolyHom.zero 44 1,PolyHom.zero 44 1,PolyHom.zero 44 1] b
theorem polyLiftFree44_1 : ∀ b : Fin 3, (polyLift44_1 b).freeBlock=basisInt (homKind 44 1) b := by decide
def polyLift44_2 (b : Fin 3) : PolyHom 44 2 :=
  ![PolyHom.zero 44 2,PolyHom.zero 44 2,PolyHom.zero 44 2] b
theorem polyLiftFree44_2 : ∀ b : Fin 3, (polyLift44_2 b).freeBlock=basisInt (homKind 44 2) b := by decide
def polyLift44_3 (b : Fin 3) : PolyHom 44 3 :=
  ![PolyHom.zero 44 3,PolyHom.zero 44 3,PolyHom.zero 44 3] b
theorem polyLiftFree44_3 : ∀ b : Fin 3, (polyLift44_3 b).freeBlock=basisInt (homKind 44 3) b := by decide
def polyLift44_4 (b : Fin 3) : PolyHom 44 4 :=
  ![PolyHom.zero 44 4,PolyHom.zero 44 4,PolyHom.zero 44 4] b
theorem polyLiftFree44_4 : ∀ b : Fin 3, (polyLift44_4 b).freeBlock=basisInt (homKind 44 4) b := by decide
def polyLift44_5 (b : Fin 3) : PolyHom 44 5 :=
  ![PolyHom.zero 44 5,PolyHom.zero 44 5,PolyHom.zero 44 5] b
theorem polyLiftFree44_5 : ∀ b : Fin 3, (polyLift44_5 b).freeBlock=basisInt (homKind 44 5) b := by decide
def polyLift44_6 (b : Fin 3) : PolyHom 44 6 :=
  ![PolyHom.zero 44 6,PolyHom.zero 44 6,PolyHom.zero 44 6] b
theorem polyLiftFree44_6 : ∀ b : Fin 3, (polyLift44_6 b).freeBlock=basisInt (homKind 44 6) b := by decide
def polyLift44_7 (b : Fin 3) : PolyHom 44 7 :=
  ![PolyHom.zero 44 7,PolyHom.zero 44 7,PolyHom.zero 44 7] b
theorem polyLiftFree44_7 : ∀ b : Fin 3, (polyLift44_7 b).freeBlock=basisInt (homKind 44 7) b := by decide
def polyLift44_8 (b : Fin 3) : PolyHom 44 8 :=
  ![PolyHom.zero 44 8,PolyHom.zero 44 8,PolyHom.zero 44 8] b
theorem polyLiftFree44_8 : ∀ b : Fin 3, (polyLift44_8 b).freeBlock=basisInt (homKind 44 8) b := by decide
def polyLift44_9 (b : Fin 3) : PolyHom 44 9 :=
  ![PolyHom.zero 44 9,PolyHom.zero 44 9,PolyHom.zero 44 9] b
theorem polyLiftFree44_9 : ∀ b : Fin 3, (polyLift44_9 b).freeBlock=basisInt (homKind 44 9) b := by decide
def polyRep44_10_0 : PolyHom 44 10 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep44_10_1 : PolyHom 44 10 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_10 (b : Fin 3) : PolyHom 44 10 :=
  ![polyRep44_10_0,polyRep44_10_1,PolyHom.zero 44 10] b
theorem polyLiftFree44_10 : ∀ b : Fin 3, (polyLift44_10 b).freeBlock=basisInt (homKind 44 10) b := by decide
def polyRep44_11_0 : PolyHom 44 11 where
  M := !![0,0,0,0;(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep44_11_1 : PolyHom 44 11 where
  M := !![(mono6 (1) 3),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_11 (b : Fin 3) : PolyHom 44 11 :=
  ![polyRep44_11_0,polyRep44_11_1,PolyHom.zero 44 11] b
theorem polyLiftFree44_11 : ∀ b : Fin 3, (polyLift44_11 b).freeBlock=basisInt (homKind 44 11) b := by decide
def polyRep44_12_0 : PolyHom 44 12 where
  M := !![(mono6 (1) 2),0,0,0;(mono6 (-1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_12 (b : Fin 3) : PolyHom 44 12 :=
  ![polyRep44_12_0,PolyHom.zero 44 12,PolyHom.zero 44 12] b
theorem polyLiftFree44_12 : ∀ b : Fin 3, (polyLift44_12 b).freeBlock=basisInt (homKind 44 12) b := by decide
def polyRep44_13_0 : PolyHom 44 13 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_13 (b : Fin 3) : PolyHom 44 13 :=
  ![polyRep44_13_0,PolyHom.zero 44 13,PolyHom.zero 44 13] b
theorem polyLiftFree44_13 : ∀ b : Fin 3, (polyLift44_13 b).freeBlock=basisInt (homKind 44 13) b := by decide
def polyLift44_14 (b : Fin 3) : PolyHom 44 14 :=
  ![PolyHom.zero 44 14,PolyHom.zero 44 14,PolyHom.zero 44 14] b
theorem polyLiftFree44_14 : ∀ b : Fin 3, (polyLift44_14 b).freeBlock=basisInt (homKind 44 14) b := by decide
def polyLift44_15 (b : Fin 3) : PolyHom 44 15 :=
  ![PolyHom.zero 44 15,PolyHom.zero 44 15,PolyHom.zero 44 15] b
theorem polyLiftFree44_15 : ∀ b : Fin 3, (polyLift44_15 b).freeBlock=basisInt (homKind 44 15) b := by decide
def polyLift44_16 (b : Fin 3) : PolyHom 44 16 :=
  ![PolyHom.zero 44 16,PolyHom.zero 44 16,PolyHom.zero 44 16] b
theorem polyLiftFree44_16 : ∀ b : Fin 3, (polyLift44_16 b).freeBlock=basisInt (homKind 44 16) b := by decide
def polyLift44_17 (b : Fin 3) : PolyHom 44 17 :=
  ![PolyHom.zero 44 17,PolyHom.zero 44 17,PolyHom.zero 44 17] b
theorem polyLiftFree44_17 : ∀ b : Fin 3, (polyLift44_17 b).freeBlock=basisInt (homKind 44 17) b := by decide
def polyLift44_18 (b : Fin 3) : PolyHom 44 18 :=
  ![PolyHom.zero 44 18,PolyHom.zero 44 18,PolyHom.zero 44 18] b
theorem polyLiftFree44_18 : ∀ b : Fin 3, (polyLift44_18 b).freeBlock=basisInt (homKind 44 18) b := by decide
def polyLift44_19 (b : Fin 3) : PolyHom 44 19 :=
  ![PolyHom.zero 44 19,PolyHom.zero 44 19,PolyHom.zero 44 19] b
theorem polyLiftFree44_19 : ∀ b : Fin 3, (polyLift44_19 b).freeBlock=basisInt (homKind 44 19) b := by decide
def polyLift44_20 (b : Fin 3) : PolyHom 44 20 :=
  ![PolyHom.zero 44 20,PolyHom.zero 44 20,PolyHom.zero 44 20] b
theorem polyLiftFree44_20 : ∀ b : Fin 3, (polyLift44_20 b).freeBlock=basisInt (homKind 44 20) b := by decide
def polyRep44_21_0 : PolyHom 44 21 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep44_21_1 : PolyHom 44 21 where
  M := !![(mono6 (1) 2),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_21 (b : Fin 3) : PolyHom 44 21 :=
  ![polyRep44_21_0,polyRep44_21_1,PolyHom.zero 44 21] b
theorem polyLiftFree44_21 : ∀ b : Fin 3, (polyLift44_21 b).freeBlock=basisInt (homKind 44 21) b := by decide
def polyRep44_22_0 : PolyHom 44 22 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_22 (b : Fin 3) : PolyHom 44 22 :=
  ![polyRep44_22_0,PolyHom.zero 44 22,PolyHom.zero 44 22] b
theorem polyLiftFree44_22 : ∀ b : Fin 3, (polyLift44_22 b).freeBlock=basisInt (homKind 44 22) b := by decide
def polyLift44_23 (b : Fin 3) : PolyHom 44 23 :=
  ![PolyHom.zero 44 23,PolyHom.zero 44 23,PolyHom.zero 44 23] b
theorem polyLiftFree44_23 : ∀ b : Fin 3, (polyLift44_23 b).freeBlock=basisInt (homKind 44 23) b := by decide
def polyRep44_24_0 : PolyHom 44 24 where
  M := !![0,0,(mono6 (1) 0),0;(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (-1) 1),0]
  U := !![(mono6 (1) 0),0;0,(mono6 (-1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep44_24_1 : PolyHom 44 24 where
  M := !![(mono6 (1) 2),0,(mono6 (1) 1),0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_24 (b : Fin 3) : PolyHom 44 24 :=
  ![polyRep44_24_0,polyRep44_24_1,PolyHom.zero 44 24] b
theorem polyLiftFree44_24 : ∀ b : Fin 3, (polyLift44_24 b).freeBlock=basisInt (homKind 44 24) b := by decide
def polyRep44_25_0 : PolyHom 44 25 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_25 (b : Fin 3) : PolyHom 44 25 :=
  ![polyRep44_25_0,PolyHom.zero 44 25,PolyHom.zero 44 25] b
theorem polyLiftFree44_25 : ∀ b : Fin 3, (polyLift44_25 b).freeBlock=basisInt (homKind 44 25) b := by decide
def polyRep44_26_0 : PolyHom 44 26 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,(mono6 (1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_26 (b : Fin 3) : PolyHom 44 26 :=
  ![polyRep44_26_0,PolyHom.zero 44 26,PolyHom.zero 44 26] b
theorem polyLiftFree44_26 : ∀ b : Fin 3, (polyLift44_26 b).freeBlock=basisInt (homKind 44 26) b := by decide
def polyRep44_27_0 : PolyHom 44 27 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_27 (b : Fin 3) : PolyHom 44 27 :=
  ![polyRep44_27_0,PolyHom.zero 44 27,PolyHom.zero 44 27] b
theorem polyLiftFree44_27 : ∀ b : Fin 3, (polyLift44_27 b).freeBlock=basisInt (homKind 44 27) b := by decide
def polyRep44_28_0 : PolyHom 44 28 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 1),0,0;0,(mono6 (1) 0),0,0]
  U := !![(mono6 (1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_28 (b : Fin 3) : PolyHom 44 28 :=
  ![polyRep44_28_0,PolyHom.zero 44 28,PolyHom.zero 44 28] b
theorem polyLiftFree44_28 : ∀ b : Fin 3, (polyLift44_28 b).freeBlock=basisInt (homKind 44 28) b := by decide
def polyLift44_29 (b : Fin 3) : PolyHom 44 29 :=
  ![PolyHom.zero 44 29,PolyHom.zero 44 29,PolyHom.zero 44 29] b
theorem polyLiftFree44_29 : ∀ b : Fin 3, (polyLift44_29 b).freeBlock=basisInt (homKind 44 29) b := by decide
def polyRep44_30_0 : PolyHom 44 30 where
  M := !![(mono6 (1) 2),0,0,0;(mono6 (-1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0]
  U := !![0,0;(mono6 (1) 2),(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_30 (b : Fin 3) : PolyHom 44 30 :=
  ![polyRep44_30_0,PolyHom.zero 44 30,PolyHom.zero 44 30] b
theorem polyLiftFree44_30 : ∀ b : Fin 3, (polyLift44_30 b).freeBlock=basisInt (homKind 44 30) b := by decide
def polyRep44_31_0 : PolyHom 44 31 where
  M := !![(mono6 (1) 1),0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_31 (b : Fin 3) : PolyHom 44 31 :=
  ![polyRep44_31_0,PolyHom.zero 44 31,PolyHom.zero 44 31] b
theorem polyLiftFree44_31 : ∀ b : Fin 3, (polyLift44_31 b).freeBlock=basisInt (homKind 44 31) b := by decide
def polyRep44_32_0 : PolyHom 44 32 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,(mono6 (1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_32 (b : Fin 3) : PolyHom 44 32 :=
  ![polyRep44_32_0,PolyHom.zero 44 32,PolyHom.zero 44 32] b
theorem polyLiftFree44_32 : ∀ b : Fin 3, (polyLift44_32 b).freeBlock=basisInt (homKind 44 32) b := by decide
def polyRep44_33_0 : PolyHom 44 33 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_33 (b : Fin 3) : PolyHom 44 33 :=
  ![polyRep44_33_0,PolyHom.zero 44 33,PolyHom.zero 44 33] b
theorem polyLiftFree44_33 : ∀ b : Fin 3, (polyLift44_33 b).freeBlock=basisInt (homKind 44 33) b := by decide
def polyRep44_34_0 : PolyHom 44 34 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_34 (b : Fin 3) : PolyHom 44 34 :=
  ![polyRep44_34_0,PolyHom.zero 44 34,PolyHom.zero 44 34] b
theorem polyLiftFree44_34 : ∀ b : Fin 3, (polyLift44_34 b).freeBlock=basisInt (homKind 44 34) b := by decide
def polyRep44_35_0 : PolyHom 44 35 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_35 (b : Fin 3) : PolyHom 44 35 :=
  ![polyRep44_35_0,PolyHom.zero 44 35,PolyHom.zero 44 35] b
theorem polyLiftFree44_35 : ∀ b : Fin 3, (polyLift44_35 b).freeBlock=basisInt (homKind 44 35) b := by decide
def polyRep44_36_0 : PolyHom 44 36 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_36 (b : Fin 3) : PolyHom 44 36 :=
  ![polyRep44_36_0,PolyHom.zero 44 36,PolyHom.zero 44 36] b
theorem polyLiftFree44_36 : ∀ b : Fin 3, (polyLift44_36 b).freeBlock=basisInt (homKind 44 36) b := by decide
def polyRep44_37_0 : PolyHom 44 37 where
  M := !![(mono6 (1) 1),0,0,0;(mono6 (-1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0]
  U := !![0,0;(mono6 (1) 2),(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_37 (b : Fin 3) : PolyHom 44 37 :=
  ![polyRep44_37_0,PolyHom.zero 44 37,PolyHom.zero 44 37] b
theorem polyLiftFree44_37 : ∀ b : Fin 3, (polyLift44_37 b).freeBlock=basisInt (homKind 44 37) b := by decide
def polyRep44_38_0 : PolyHom 44 38 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,(mono6 (1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_38 (b : Fin 3) : PolyHom 44 38 :=
  ![polyRep44_38_0,PolyHom.zero 44 38,PolyHom.zero 44 38] b
theorem polyLiftFree44_38 : ∀ b : Fin 3, (polyLift44_38 b).freeBlock=basisInt (homKind 44 38) b := by decide
def polyRep44_39_0 : PolyHom 44 39 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,(mono6 (1) 0),0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_39 (b : Fin 3) : PolyHom 44 39 :=
  ![polyRep44_39_0,PolyHom.zero 44 39,PolyHom.zero 44 39] b
theorem polyLiftFree44_39 : ∀ b : Fin 3, (polyLift44_39 b).freeBlock=basisInt (homKind 44 39) b := by decide
def polyRep44_40_0 : PolyHom 44 40 where
  M := !![(mono6 (1) 1),0,0,(mono6 (1) 0);0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_40 (b : Fin 3) : PolyHom 44 40 :=
  ![polyRep44_40_0,PolyHom.zero 44 40,PolyHom.zero 44 40] b
theorem polyLiftFree44_40 : ∀ b : Fin 3, (polyLift44_40 b).freeBlock=basisInt (homKind 44 40) b := by decide
def polyRep44_41_0 : PolyHom 44 41 where
  M := !![(mono6 (1) 0),0,0,(mono6 (1) 0);0,0,0,0;0,0,(mono6 (1) 1),0;0,0,(mono6 (1) 0),0]
  U := !![(mono6 (1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_41 (b : Fin 3) : PolyHom 44 41 :=
  ![polyRep44_41_0,PolyHom.zero 44 41,PolyHom.zero 44 41] b
theorem polyLiftFree44_41 : ∀ b : Fin 3, (polyLift44_41 b).freeBlock=basisInt (homKind 44 41) b := by decide
def polyRep44_42_0 : PolyHom 44 42 where
  M := !![0,(mono6 (1) 2),0,0;0,(mono6 (-1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),(mono6 (-1) 1)]
  U := !![0,0;(mono6 (1) 2),(mono6 (-1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_42 (b : Fin 3) : PolyHom 44 42 :=
  ![polyRep44_42_0,PolyHom.zero 44 42,PolyHom.zero 44 42] b
theorem polyLiftFree44_42 : ∀ b : Fin 3, (polyLift44_42 b).freeBlock=basisInt (homKind 44 42) b := by decide
def polyRep44_43_0 : PolyHom 44 43 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 1),0;0,0,(mono6 (1) 0),(mono6 (1) 0)]
  U := !![(mono6 (1) 0),0;(mono6 (1) 1),(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_43 (b : Fin 3) : PolyHom 44 43 :=
  ![polyRep44_43_0,PolyHom.zero 44 43,PolyHom.zero 44 43] b
theorem polyLiftFree44_43 : ∀ b : Fin 3, (polyLift44_43 b).freeBlock=basisInt (homKind 44 43) b := by decide
def polyRep44_44_0 : PolyHom 44 44 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,(mono6 (1) 0)]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep44_44_1 : PolyHom 44 44 where
  M := !![(mono6 (1) 1),(mono6 (1) 2),0,0;0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_44 (b : Fin 3) : PolyHom 44 44 :=
  ![polyRep44_44_0,polyRep44_44_1,PolyHom.zero 44 44] b
theorem polyLiftFree44_44 : ∀ b : Fin 3, (polyLift44_44 b).freeBlock=basisInt (homKind 44 44) b := by decide
def polyRep44_45_0 : PolyHom 44 45 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep44_45_1 : PolyHom 44 45 where
  M := !![0,0,0,0;0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift44_45 (b : Fin 3) : PolyHom 44 45 :=
  ![polyRep44_45_0,polyRep44_45_1,PolyHom.zero 44 45] b
theorem polyLiftFree44_45 : ∀ b : Fin 3, (polyLift44_45 b).freeBlock=basisInt (homKind 44 45) b := by decide
def polyLift44_46 (b : Fin 3) : PolyHom 44 46 :=
  ![PolyHom.zero 44 46,PolyHom.zero 44 46,PolyHom.zero 44 46] b
theorem polyLiftFree44_46 : ∀ b : Fin 3, (polyLift44_46 b).freeBlock=basisInt (homKind 44 46) b := by decide
def polyLiftRow44 (j : Fin 47) (b : Fin 3) : PolyHom 44 j :=
  match j with
  | ⟨0,_⟩ => polyLift44_0 b
  | ⟨1,_⟩ => polyLift44_1 b
  | ⟨2,_⟩ => polyLift44_2 b
  | ⟨3,_⟩ => polyLift44_3 b
  | ⟨4,_⟩ => polyLift44_4 b
  | ⟨5,_⟩ => polyLift44_5 b
  | ⟨6,_⟩ => polyLift44_6 b
  | ⟨7,_⟩ => polyLift44_7 b
  | ⟨8,_⟩ => polyLift44_8 b
  | ⟨9,_⟩ => polyLift44_9 b
  | ⟨10,_⟩ => polyLift44_10 b
  | ⟨11,_⟩ => polyLift44_11 b
  | ⟨12,_⟩ => polyLift44_12 b
  | ⟨13,_⟩ => polyLift44_13 b
  | ⟨14,_⟩ => polyLift44_14 b
  | ⟨15,_⟩ => polyLift44_15 b
  | ⟨16,_⟩ => polyLift44_16 b
  | ⟨17,_⟩ => polyLift44_17 b
  | ⟨18,_⟩ => polyLift44_18 b
  | ⟨19,_⟩ => polyLift44_19 b
  | ⟨20,_⟩ => polyLift44_20 b
  | ⟨21,_⟩ => polyLift44_21 b
  | ⟨22,_⟩ => polyLift44_22 b
  | ⟨23,_⟩ => polyLift44_23 b
  | ⟨24,_⟩ => polyLift44_24 b
  | ⟨25,_⟩ => polyLift44_25 b
  | ⟨26,_⟩ => polyLift44_26 b
  | ⟨27,_⟩ => polyLift44_27 b
  | ⟨28,_⟩ => polyLift44_28 b
  | ⟨29,_⟩ => polyLift44_29 b
  | ⟨30,_⟩ => polyLift44_30 b
  | ⟨31,_⟩ => polyLift44_31 b
  | ⟨32,_⟩ => polyLift44_32 b
  | ⟨33,_⟩ => polyLift44_33 b
  | ⟨34,_⟩ => polyLift44_34 b
  | ⟨35,_⟩ => polyLift44_35 b
  | ⟨36,_⟩ => polyLift44_36 b
  | ⟨37,_⟩ => polyLift44_37 b
  | ⟨38,_⟩ => polyLift44_38 b
  | ⟨39,_⟩ => polyLift44_39 b
  | ⟨40,_⟩ => polyLift44_40 b
  | ⟨41,_⟩ => polyLift44_41 b
  | ⟨42,_⟩ => polyLift44_42 b
  | ⟨43,_⟩ => polyLift44_43 b
  | ⟨44,_⟩ => polyLift44_44 b
  | ⟨45,_⟩ => polyLift44_45 b
  | ⟨46,_⟩ => polyLift44_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree44 (j : Fin 47) (b : Fin 3) : (polyLiftRow44 j b).freeBlock=basisInt (homKind 44 j) b := by
  fin_cases j
  · exact polyLiftFree44_0 b
  · exact polyLiftFree44_1 b
  · exact polyLiftFree44_2 b
  · exact polyLiftFree44_3 b
  · exact polyLiftFree44_4 b
  · exact polyLiftFree44_5 b
  · exact polyLiftFree44_6 b
  · exact polyLiftFree44_7 b
  · exact polyLiftFree44_8 b
  · exact polyLiftFree44_9 b
  · exact polyLiftFree44_10 b
  · exact polyLiftFree44_11 b
  · exact polyLiftFree44_12 b
  · exact polyLiftFree44_13 b
  · exact polyLiftFree44_14 b
  · exact polyLiftFree44_15 b
  · exact polyLiftFree44_16 b
  · exact polyLiftFree44_17 b
  · exact polyLiftFree44_18 b
  · exact polyLiftFree44_19 b
  · exact polyLiftFree44_20 b
  · exact polyLiftFree44_21 b
  · exact polyLiftFree44_22 b
  · exact polyLiftFree44_23 b
  · exact polyLiftFree44_24 b
  · exact polyLiftFree44_25 b
  · exact polyLiftFree44_26 b
  · exact polyLiftFree44_27 b
  · exact polyLiftFree44_28 b
  · exact polyLiftFree44_29 b
  · exact polyLiftFree44_30 b
  · exact polyLiftFree44_31 b
  · exact polyLiftFree44_32 b
  · exact polyLiftFree44_33 b
  · exact polyLiftFree44_34 b
  · exact polyLiftFree44_35 b
  · exact polyLiftFree44_36 b
  · exact polyLiftFree44_37 b
  · exact polyLiftFree44_38 b
  · exact polyLiftFree44_39 b
  · exact polyLiftFree44_40 b
  · exact polyLiftFree44_41 b
  · exact polyLiftFree44_42 b
  · exact polyLiftFree44_43 b
  · exact polyLiftFree44_44 b
  · exact polyLiftFree44_45 b
  · exact polyLiftFree44_46 b
end UniserialComputations.N6
