import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift13_0 (b : Fin 3) : PolyHom 13 0 :=
  ![PolyHom.zero 13 0,PolyHom.zero 13 0,PolyHom.zero 13 0] b
theorem polyLiftFree13_0 : ∀ b : Fin 3, (polyLift13_0 b).freeBlock=basisInt (homKind 13 0) b := by decide
def polyLift13_1 (b : Fin 3) : PolyHom 13 1 :=
  ![PolyHom.zero 13 1,PolyHom.zero 13 1,PolyHom.zero 13 1] b
theorem polyLiftFree13_1 : ∀ b : Fin 3, (polyLift13_1 b).freeBlock=basisInt (homKind 13 1) b := by decide
def polyLift13_2 (b : Fin 3) : PolyHom 13 2 :=
  ![PolyHom.zero 13 2,PolyHom.zero 13 2,PolyHom.zero 13 2] b
theorem polyLiftFree13_2 : ∀ b : Fin 3, (polyLift13_2 b).freeBlock=basisInt (homKind 13 2) b := by decide
def polyLift13_3 (b : Fin 3) : PolyHom 13 3 :=
  ![PolyHom.zero 13 3,PolyHom.zero 13 3,PolyHom.zero 13 3] b
theorem polyLiftFree13_3 : ∀ b : Fin 3, (polyLift13_3 b).freeBlock=basisInt (homKind 13 3) b := by decide
def polyLift13_4 (b : Fin 3) : PolyHom 13 4 :=
  ![PolyHom.zero 13 4,PolyHom.zero 13 4,PolyHom.zero 13 4] b
theorem polyLiftFree13_4 : ∀ b : Fin 3, (polyLift13_4 b).freeBlock=basisInt (homKind 13 4) b := by decide
def polyLift13_5 (b : Fin 3) : PolyHom 13 5 :=
  ![PolyHom.zero 13 5,PolyHom.zero 13 5,PolyHom.zero 13 5] b
theorem polyLiftFree13_5 : ∀ b : Fin 3, (polyLift13_5 b).freeBlock=basisInt (homKind 13 5) b := by decide
def polyLift13_6 (b : Fin 3) : PolyHom 13 6 :=
  ![PolyHom.zero 13 6,PolyHom.zero 13 6,PolyHom.zero 13 6] b
theorem polyLiftFree13_6 : ∀ b : Fin 3, (polyLift13_6 b).freeBlock=basisInt (homKind 13 6) b := by decide
def polyLift13_7 (b : Fin 3) : PolyHom 13 7 :=
  ![PolyHom.zero 13 7,PolyHom.zero 13 7,PolyHom.zero 13 7] b
theorem polyLiftFree13_7 : ∀ b : Fin 3, (polyLift13_7 b).freeBlock=basisInt (homKind 13 7) b := by decide
def polyLift13_8 (b : Fin 3) : PolyHom 13 8 :=
  ![PolyHom.zero 13 8,PolyHom.zero 13 8,PolyHom.zero 13 8] b
theorem polyLiftFree13_8 : ∀ b : Fin 3, (polyLift13_8 b).freeBlock=basisInt (homKind 13 8) b := by decide
def polyLift13_9 (b : Fin 3) : PolyHom 13 9 :=
  ![PolyHom.zero 13 9,PolyHom.zero 13 9,PolyHom.zero 13 9] b
theorem polyLiftFree13_9 : ∀ b : Fin 3, (polyLift13_9 b).freeBlock=basisInt (homKind 13 9) b := by decide
def polyRep13_10_0 : PolyHom 13 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 3),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift13_10 (b : Fin 3) : PolyHom 13 10 :=
  ![polyRep13_10_0,PolyHom.zero 13 10,PolyHom.zero 13 10] b
theorem polyLiftFree13_10 : ∀ b : Fin 3, (polyLift13_10 b).freeBlock=basisInt (homKind 13 10) b := by decide
def polyRep13_11_0 : PolyHom 13 11 where
  M := !![(mono6 (1) 2),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift13_11 (b : Fin 3) : PolyHom 13 11 :=
  ![polyRep13_11_0,PolyHom.zero 13 11,PolyHom.zero 13 11] b
theorem polyLiftFree13_11 : ∀ b : Fin 3, (polyLift13_11 b).freeBlock=basisInt (homKind 13 11) b := by decide
def polyRep13_12_0 : PolyHom 13 12 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift13_12 (b : Fin 3) : PolyHom 13 12 :=
  ![polyRep13_12_0,PolyHom.zero 13 12,PolyHom.zero 13 12] b
theorem polyLiftFree13_12 : ∀ b : Fin 3, (polyLift13_12 b).freeBlock=basisInt (homKind 13 12) b := by decide
def polyRep13_13_0 : PolyHom 13 13 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift13_13 (b : Fin 3) : PolyHom 13 13 :=
  ![polyRep13_13_0,PolyHom.zero 13 13,PolyHom.zero 13 13] b
theorem polyLiftFree13_13 : ∀ b : Fin 3, (polyLift13_13 b).freeBlock=basisInt (homKind 13 13) b := by decide
def polyLift13_14 (b : Fin 3) : PolyHom 13 14 :=
  ![PolyHom.zero 13 14,PolyHom.zero 13 14,PolyHom.zero 13 14] b
theorem polyLiftFree13_14 : ∀ b : Fin 3, (polyLift13_14 b).freeBlock=basisInt (homKind 13 14) b := by decide
def polyLift13_15 (b : Fin 3) : PolyHom 13 15 :=
  ![PolyHom.zero 13 15,PolyHom.zero 13 15,PolyHom.zero 13 15] b
theorem polyLiftFree13_15 : ∀ b : Fin 3, (polyLift13_15 b).freeBlock=basisInt (homKind 13 15) b := by decide
def polyLift13_16 (b : Fin 3) : PolyHom 13 16 :=
  ![PolyHom.zero 13 16,PolyHom.zero 13 16,PolyHom.zero 13 16] b
theorem polyLiftFree13_16 : ∀ b : Fin 3, (polyLift13_16 b).freeBlock=basisInt (homKind 13 16) b := by decide
def polyLift13_17 (b : Fin 3) : PolyHom 13 17 :=
  ![PolyHom.zero 13 17,PolyHom.zero 13 17,PolyHom.zero 13 17] b
theorem polyLiftFree13_17 : ∀ b : Fin 3, (polyLift13_17 b).freeBlock=basisInt (homKind 13 17) b := by decide
def polyLift13_18 (b : Fin 3) : PolyHom 13 18 :=
  ![PolyHom.zero 13 18,PolyHom.zero 13 18,PolyHom.zero 13 18] b
theorem polyLiftFree13_18 : ∀ b : Fin 3, (polyLift13_18 b).freeBlock=basisInt (homKind 13 18) b := by decide
def polyLift13_19 (b : Fin 3) : PolyHom 13 19 :=
  ![PolyHom.zero 13 19,PolyHom.zero 13 19,PolyHom.zero 13 19] b
theorem polyLiftFree13_19 : ∀ b : Fin 3, (polyLift13_19 b).freeBlock=basisInt (homKind 13 19) b := by decide
def polyLift13_20 (b : Fin 3) : PolyHom 13 20 :=
  ![PolyHom.zero 13 20,PolyHom.zero 13 20,PolyHom.zero 13 20] b
theorem polyLiftFree13_20 : ∀ b : Fin 3, (polyLift13_20 b).freeBlock=basisInt (homKind 13 20) b := by decide
def polyRep13_21_0 : PolyHom 13 21 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift13_21 (b : Fin 3) : PolyHom 13 21 :=
  ![polyRep13_21_0,PolyHom.zero 13 21,PolyHom.zero 13 21] b
theorem polyLiftFree13_21 : ∀ b : Fin 3, (polyLift13_21 b).freeBlock=basisInt (homKind 13 21) b := by decide
def polyRep13_22_0 : PolyHom 13 22 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift13_22 (b : Fin 3) : PolyHom 13 22 :=
  ![polyRep13_22_0,PolyHom.zero 13 22,PolyHom.zero 13 22] b
theorem polyLiftFree13_22 : ∀ b : Fin 3, (polyLift13_22 b).freeBlock=basisInt (homKind 13 22) b := by decide
def polyLift13_23 (b : Fin 3) : PolyHom 13 23 :=
  ![PolyHom.zero 13 23,PolyHom.zero 13 23,PolyHom.zero 13 23] b
theorem polyLiftFree13_23 : ∀ b : Fin 3, (polyLift13_23 b).freeBlock=basisInt (homKind 13 23) b := by decide
def polyRep13_24_0 : PolyHom 13 24 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),(mono6 (1) 2),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift13_24 (b : Fin 3) : PolyHom 13 24 :=
  ![polyRep13_24_0,PolyHom.zero 13 24,PolyHom.zero 13 24] b
theorem polyLiftFree13_24 : ∀ b : Fin 3, (polyLift13_24 b).freeBlock=basisInt (homKind 13 24) b := by decide
def polyRep13_25_0 : PolyHom 13 25 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift13_25 (b : Fin 3) : PolyHom 13 25 :=
  ![polyRep13_25_0,PolyHom.zero 13 25,PolyHom.zero 13 25] b
theorem polyLiftFree13_25 : ∀ b : Fin 3, (polyLift13_25 b).freeBlock=basisInt (homKind 13 25) b := by decide
def polyRep13_26_0 : PolyHom 13 26 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift13_26 (b : Fin 3) : PolyHom 13 26 :=
  ![polyRep13_26_0,PolyHom.zero 13 26,PolyHom.zero 13 26] b
theorem polyLiftFree13_26 : ∀ b : Fin 3, (polyLift13_26 b).freeBlock=basisInt (homKind 13 26) b := by decide
def polyRep13_27_0 : PolyHom 13 27 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift13_27 (b : Fin 3) : PolyHom 13 27 :=
  ![polyRep13_27_0,PolyHom.zero 13 27,PolyHom.zero 13 27] b
theorem polyLiftFree13_27 : ∀ b : Fin 3, (polyLift13_27 b).freeBlock=basisInt (homKind 13 27) b := by decide
def polyLift13_28 (b : Fin 3) : PolyHom 13 28 :=
  ![PolyHom.zero 13 28,PolyHom.zero 13 28,PolyHom.zero 13 28] b
theorem polyLiftFree13_28 : ∀ b : Fin 3, (polyLift13_28 b).freeBlock=basisInt (homKind 13 28) b := by decide
def polyLift13_29 (b : Fin 3) : PolyHom 13 29 :=
  ![PolyHom.zero 13 29,PolyHom.zero 13 29,PolyHom.zero 13 29] b
theorem polyLiftFree13_29 : ∀ b : Fin 3, (polyLift13_29 b).freeBlock=basisInt (homKind 13 29) b := by decide
def polyRep13_30_0 : PolyHom 13 30 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift13_30 (b : Fin 3) : PolyHom 13 30 :=
  ![polyRep13_30_0,PolyHom.zero 13 30,PolyHom.zero 13 30] b
theorem polyLiftFree13_30 : ∀ b : Fin 3, (polyLift13_30 b).freeBlock=basisInt (homKind 13 30) b := by decide
def polyRep13_31_0 : PolyHom 13 31 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift13_31 (b : Fin 3) : PolyHom 13 31 :=
  ![polyRep13_31_0,PolyHom.zero 13 31,PolyHom.zero 13 31] b
theorem polyLiftFree13_31 : ∀ b : Fin 3, (polyLift13_31 b).freeBlock=basisInt (homKind 13 31) b := by decide
def polyRep13_32_0 : PolyHom 13 32 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift13_32 (b : Fin 3) : PolyHom 13 32 :=
  ![polyRep13_32_0,PolyHom.zero 13 32,PolyHom.zero 13 32] b
theorem polyLiftFree13_32 : ∀ b : Fin 3, (polyLift13_32 b).freeBlock=basisInt (homKind 13 32) b := by decide
def polyLift13_33 (b : Fin 3) : PolyHom 13 33 :=
  ![PolyHom.zero 13 33,PolyHom.zero 13 33,PolyHom.zero 13 33] b
theorem polyLiftFree13_33 : ∀ b : Fin 3, (polyLift13_33 b).freeBlock=basisInt (homKind 13 33) b := by decide
def polyLift13_34 (b : Fin 3) : PolyHom 13 34 :=
  ![PolyHom.zero 13 34,PolyHom.zero 13 34,PolyHom.zero 13 34] b
theorem polyLiftFree13_34 : ∀ b : Fin 3, (polyLift13_34 b).freeBlock=basisInt (homKind 13 34) b := by decide
def polyLift13_35 (b : Fin 3) : PolyHom 13 35 :=
  ![PolyHom.zero 13 35,PolyHom.zero 13 35,PolyHom.zero 13 35] b
theorem polyLiftFree13_35 : ∀ b : Fin 3, (polyLift13_35 b).freeBlock=basisInt (homKind 13 35) b := by decide
def polyLift13_36 (b : Fin 3) : PolyHom 13 36 :=
  ![PolyHom.zero 13 36,PolyHom.zero 13 36,PolyHom.zero 13 36] b
theorem polyLiftFree13_36 : ∀ b : Fin 3, (polyLift13_36 b).freeBlock=basisInt (homKind 13 36) b := by decide
def polyRep13_37_0 : PolyHom 13 37 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift13_37 (b : Fin 3) : PolyHom 13 37 :=
  ![polyRep13_37_0,PolyHom.zero 13 37,PolyHom.zero 13 37] b
theorem polyLiftFree13_37 : ∀ b : Fin 3, (polyLift13_37 b).freeBlock=basisInt (homKind 13 37) b := by decide
def polyRep13_38_0 : PolyHom 13 38 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift13_38 (b : Fin 3) : PolyHom 13 38 :=
  ![polyRep13_38_0,PolyHom.zero 13 38,PolyHom.zero 13 38] b
theorem polyLiftFree13_38 : ∀ b : Fin 3, (polyLift13_38 b).freeBlock=basisInt (homKind 13 38) b := by decide
def polyRep13_39_0 : PolyHom 13 39 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift13_39 (b : Fin 3) : PolyHom 13 39 :=
  ![polyRep13_39_0,PolyHom.zero 13 39,PolyHom.zero 13 39] b
theorem polyLiftFree13_39 : ∀ b : Fin 3, (polyLift13_39 b).freeBlock=basisInt (homKind 13 39) b := by decide
def polyRep13_40_0 : PolyHom 13 40 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),(mono6 (1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift13_40 (b : Fin 3) : PolyHom 13 40 :=
  ![polyRep13_40_0,PolyHom.zero 13 40,PolyHom.zero 13 40] b
theorem polyLiftFree13_40 : ∀ b : Fin 3, (polyLift13_40 b).freeBlock=basisInt (homKind 13 40) b := by decide
def polyLift13_41 (b : Fin 3) : PolyHom 13 41 :=
  ![PolyHom.zero 13 41,PolyHom.zero 13 41,PolyHom.zero 13 41] b
theorem polyLiftFree13_41 : ∀ b : Fin 3, (polyLift13_41 b).freeBlock=basisInt (homKind 13 41) b := by decide
def polyRep13_42_0 : PolyHom 13 42 where
  M := !![0,(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),(mono6 (-1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (-1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift13_42 (b : Fin 3) : PolyHom 13 42 :=
  ![polyRep13_42_0,PolyHom.zero 13 42,PolyHom.zero 13 42] b
theorem polyLiftFree13_42 : ∀ b : Fin 3, (polyLift13_42 b).freeBlock=basisInt (homKind 13 42) b := by decide
def polyLift13_43 (b : Fin 3) : PolyHom 13 43 :=
  ![PolyHom.zero 13 43,PolyHom.zero 13 43,PolyHom.zero 13 43] b
theorem polyLiftFree13_43 : ∀ b : Fin 3, (polyLift13_43 b).freeBlock=basisInt (homKind 13 43) b := by decide
def polyRep13_44_0 : PolyHom 13 44 where
  M := !![0,(mono6 (1) 1),0,0;0,0,(mono6 (1) 0),(mono6 (-1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),(mono6 (-1) 1);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift13_44 (b : Fin 3) : PolyHom 13 44 :=
  ![polyRep13_44_0,PolyHom.zero 13 44,PolyHom.zero 13 44] b
theorem polyLiftFree13_44 : ∀ b : Fin 3, (polyLift13_44 b).freeBlock=basisInt (homKind 13 44) b := by decide
def polyRep13_45_0 : PolyHom 13 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift13_45 (b : Fin 3) : PolyHom 13 45 :=
  ![polyRep13_45_0,PolyHom.zero 13 45,PolyHom.zero 13 45] b
theorem polyLiftFree13_45 : ∀ b : Fin 3, (polyLift13_45 b).freeBlock=basisInt (homKind 13 45) b := by decide
def polyLift13_46 (b : Fin 3) : PolyHom 13 46 :=
  ![PolyHom.zero 13 46,PolyHom.zero 13 46,PolyHom.zero 13 46] b
theorem polyLiftFree13_46 : ∀ b : Fin 3, (polyLift13_46 b).freeBlock=basisInt (homKind 13 46) b := by decide
def polyLiftRow13 (j : Fin 47) (b : Fin 3) : PolyHom 13 j :=
  match j with
  | ⟨0,_⟩ => polyLift13_0 b
  | ⟨1,_⟩ => polyLift13_1 b
  | ⟨2,_⟩ => polyLift13_2 b
  | ⟨3,_⟩ => polyLift13_3 b
  | ⟨4,_⟩ => polyLift13_4 b
  | ⟨5,_⟩ => polyLift13_5 b
  | ⟨6,_⟩ => polyLift13_6 b
  | ⟨7,_⟩ => polyLift13_7 b
  | ⟨8,_⟩ => polyLift13_8 b
  | ⟨9,_⟩ => polyLift13_9 b
  | ⟨10,_⟩ => polyLift13_10 b
  | ⟨11,_⟩ => polyLift13_11 b
  | ⟨12,_⟩ => polyLift13_12 b
  | ⟨13,_⟩ => polyLift13_13 b
  | ⟨14,_⟩ => polyLift13_14 b
  | ⟨15,_⟩ => polyLift13_15 b
  | ⟨16,_⟩ => polyLift13_16 b
  | ⟨17,_⟩ => polyLift13_17 b
  | ⟨18,_⟩ => polyLift13_18 b
  | ⟨19,_⟩ => polyLift13_19 b
  | ⟨20,_⟩ => polyLift13_20 b
  | ⟨21,_⟩ => polyLift13_21 b
  | ⟨22,_⟩ => polyLift13_22 b
  | ⟨23,_⟩ => polyLift13_23 b
  | ⟨24,_⟩ => polyLift13_24 b
  | ⟨25,_⟩ => polyLift13_25 b
  | ⟨26,_⟩ => polyLift13_26 b
  | ⟨27,_⟩ => polyLift13_27 b
  | ⟨28,_⟩ => polyLift13_28 b
  | ⟨29,_⟩ => polyLift13_29 b
  | ⟨30,_⟩ => polyLift13_30 b
  | ⟨31,_⟩ => polyLift13_31 b
  | ⟨32,_⟩ => polyLift13_32 b
  | ⟨33,_⟩ => polyLift13_33 b
  | ⟨34,_⟩ => polyLift13_34 b
  | ⟨35,_⟩ => polyLift13_35 b
  | ⟨36,_⟩ => polyLift13_36 b
  | ⟨37,_⟩ => polyLift13_37 b
  | ⟨38,_⟩ => polyLift13_38 b
  | ⟨39,_⟩ => polyLift13_39 b
  | ⟨40,_⟩ => polyLift13_40 b
  | ⟨41,_⟩ => polyLift13_41 b
  | ⟨42,_⟩ => polyLift13_42 b
  | ⟨43,_⟩ => polyLift13_43 b
  | ⟨44,_⟩ => polyLift13_44 b
  | ⟨45,_⟩ => polyLift13_45 b
  | ⟨46,_⟩ => polyLift13_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree13 (j : Fin 47) (b : Fin 3) : (polyLiftRow13 j b).freeBlock=basisInt (homKind 13 j) b := by
  fin_cases j
  · exact polyLiftFree13_0 b
  · exact polyLiftFree13_1 b
  · exact polyLiftFree13_2 b
  · exact polyLiftFree13_3 b
  · exact polyLiftFree13_4 b
  · exact polyLiftFree13_5 b
  · exact polyLiftFree13_6 b
  · exact polyLiftFree13_7 b
  · exact polyLiftFree13_8 b
  · exact polyLiftFree13_9 b
  · exact polyLiftFree13_10 b
  · exact polyLiftFree13_11 b
  · exact polyLiftFree13_12 b
  · exact polyLiftFree13_13 b
  · exact polyLiftFree13_14 b
  · exact polyLiftFree13_15 b
  · exact polyLiftFree13_16 b
  · exact polyLiftFree13_17 b
  · exact polyLiftFree13_18 b
  · exact polyLiftFree13_19 b
  · exact polyLiftFree13_20 b
  · exact polyLiftFree13_21 b
  · exact polyLiftFree13_22 b
  · exact polyLiftFree13_23 b
  · exact polyLiftFree13_24 b
  · exact polyLiftFree13_25 b
  · exact polyLiftFree13_26 b
  · exact polyLiftFree13_27 b
  · exact polyLiftFree13_28 b
  · exact polyLiftFree13_29 b
  · exact polyLiftFree13_30 b
  · exact polyLiftFree13_31 b
  · exact polyLiftFree13_32 b
  · exact polyLiftFree13_33 b
  · exact polyLiftFree13_34 b
  · exact polyLiftFree13_35 b
  · exact polyLiftFree13_36 b
  · exact polyLiftFree13_37 b
  · exact polyLiftFree13_38 b
  · exact polyLiftFree13_39 b
  · exact polyLiftFree13_40 b
  · exact polyLiftFree13_41 b
  · exact polyLiftFree13_42 b
  · exact polyLiftFree13_43 b
  · exact polyLiftFree13_44 b
  · exact polyLiftFree13_45 b
  · exact polyLiftFree13_46 b
end UniserialComputations.N6
