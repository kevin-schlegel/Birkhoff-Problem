import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift7_0 (b : Fin 3) : PolyHom 7 0 :=
  ![PolyHom.zero 7 0,PolyHom.zero 7 0,PolyHom.zero 7 0] b
theorem polyLiftFree7_0 : ∀ b : Fin 3, (polyLift7_0 b).freeBlock=basisInt (homKind 7 0) b := by decide
def polyLift7_1 (b : Fin 3) : PolyHom 7 1 :=
  ![PolyHom.zero 7 1,PolyHom.zero 7 1,PolyHom.zero 7 1] b
theorem polyLiftFree7_1 : ∀ b : Fin 3, (polyLift7_1 b).freeBlock=basisInt (homKind 7 1) b := by decide
def polyLift7_2 (b : Fin 3) : PolyHom 7 2 :=
  ![PolyHom.zero 7 2,PolyHom.zero 7 2,PolyHom.zero 7 2] b
theorem polyLiftFree7_2 : ∀ b : Fin 3, (polyLift7_2 b).freeBlock=basisInt (homKind 7 2) b := by decide
def polyLift7_3 (b : Fin 3) : PolyHom 7 3 :=
  ![PolyHom.zero 7 3,PolyHom.zero 7 3,PolyHom.zero 7 3] b
theorem polyLiftFree7_3 : ∀ b : Fin 3, (polyLift7_3 b).freeBlock=basisInt (homKind 7 3) b := by decide
def polyLift7_4 (b : Fin 3) : PolyHom 7 4 :=
  ![PolyHom.zero 7 4,PolyHom.zero 7 4,PolyHom.zero 7 4] b
theorem polyLiftFree7_4 : ∀ b : Fin 3, (polyLift7_4 b).freeBlock=basisInt (homKind 7 4) b := by decide
def polyLift7_5 (b : Fin 3) : PolyHom 7 5 :=
  ![PolyHom.zero 7 5,PolyHom.zero 7 5,PolyHom.zero 7 5] b
theorem polyLiftFree7_5 : ∀ b : Fin 3, (polyLift7_5 b).freeBlock=basisInt (homKind 7 5) b := by decide
def polyRep7_6_0 : PolyHom 7 6 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift7_6 (b : Fin 3) : PolyHom 7 6 :=
  ![polyRep7_6_0,PolyHom.zero 7 6,PolyHom.zero 7 6] b
theorem polyLiftFree7_6 : ∀ b : Fin 3, (polyLift7_6 b).freeBlock=basisInt (homKind 7 6) b := by decide
def polyRep7_7_0 : PolyHom 7 7 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift7_7 (b : Fin 3) : PolyHom 7 7 :=
  ![polyRep7_7_0,PolyHom.zero 7 7,PolyHom.zero 7 7] b
theorem polyLiftFree7_7 : ∀ b : Fin 3, (polyLift7_7 b).freeBlock=basisInt (homKind 7 7) b := by decide
def polyLift7_8 (b : Fin 3) : PolyHom 7 8 :=
  ![PolyHom.zero 7 8,PolyHom.zero 7 8,PolyHom.zero 7 8] b
theorem polyLiftFree7_8 : ∀ b : Fin 3, (polyLift7_8 b).freeBlock=basisInt (homKind 7 8) b := by decide
def polyLift7_9 (b : Fin 3) : PolyHom 7 9 :=
  ![PolyHom.zero 7 9,PolyHom.zero 7 9,PolyHom.zero 7 9] b
theorem polyLiftFree7_9 : ∀ b : Fin 3, (polyLift7_9 b).freeBlock=basisInt (homKind 7 9) b := by decide
def polyRep7_10_0 : PolyHom 7 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift7_10 (b : Fin 3) : PolyHom 7 10 :=
  ![polyRep7_10_0,PolyHom.zero 7 10,PolyHom.zero 7 10] b
theorem polyLiftFree7_10 : ∀ b : Fin 3, (polyLift7_10 b).freeBlock=basisInt (homKind 7 10) b := by decide
def polyRep7_11_0 : PolyHom 7 11 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift7_11 (b : Fin 3) : PolyHom 7 11 :=
  ![polyRep7_11_0,PolyHom.zero 7 11,PolyHom.zero 7 11] b
theorem polyLiftFree7_11 : ∀ b : Fin 3, (polyLift7_11 b).freeBlock=basisInt (homKind 7 11) b := by decide
def polyRep7_12_0 : PolyHom 7 12 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift7_12 (b : Fin 3) : PolyHom 7 12 :=
  ![polyRep7_12_0,PolyHom.zero 7 12,PolyHom.zero 7 12] b
theorem polyLiftFree7_12 : ∀ b : Fin 3, (polyLift7_12 b).freeBlock=basisInt (homKind 7 12) b := by decide
def polyLift7_13 (b : Fin 3) : PolyHom 7 13 :=
  ![PolyHom.zero 7 13,PolyHom.zero 7 13,PolyHom.zero 7 13] b
theorem polyLiftFree7_13 : ∀ b : Fin 3, (polyLift7_13 b).freeBlock=basisInt (homKind 7 13) b := by decide
def polyLift7_14 (b : Fin 3) : PolyHom 7 14 :=
  ![PolyHom.zero 7 14,PolyHom.zero 7 14,PolyHom.zero 7 14] b
theorem polyLiftFree7_14 : ∀ b : Fin 3, (polyLift7_14 b).freeBlock=basisInt (homKind 7 14) b := by decide
def polyLift7_15 (b : Fin 3) : PolyHom 7 15 :=
  ![PolyHom.zero 7 15,PolyHom.zero 7 15,PolyHom.zero 7 15] b
theorem polyLiftFree7_15 : ∀ b : Fin 3, (polyLift7_15 b).freeBlock=basisInt (homKind 7 15) b := by decide
def polyLift7_16 (b : Fin 3) : PolyHom 7 16 :=
  ![PolyHom.zero 7 16,PolyHom.zero 7 16,PolyHom.zero 7 16] b
theorem polyLiftFree7_16 : ∀ b : Fin 3, (polyLift7_16 b).freeBlock=basisInt (homKind 7 16) b := by decide
def polyLift7_17 (b : Fin 3) : PolyHom 7 17 :=
  ![PolyHom.zero 7 17,PolyHom.zero 7 17,PolyHom.zero 7 17] b
theorem polyLiftFree7_17 : ∀ b : Fin 3, (polyLift7_17 b).freeBlock=basisInt (homKind 7 17) b := by decide
def polyLift7_18 (b : Fin 3) : PolyHom 7 18 :=
  ![PolyHom.zero 7 18,PolyHom.zero 7 18,PolyHom.zero 7 18] b
theorem polyLiftFree7_18 : ∀ b : Fin 3, (polyLift7_18 b).freeBlock=basisInt (homKind 7 18) b := by decide
def polyLift7_19 (b : Fin 3) : PolyHom 7 19 :=
  ![PolyHom.zero 7 19,PolyHom.zero 7 19,PolyHom.zero 7 19] b
theorem polyLiftFree7_19 : ∀ b : Fin 3, (polyLift7_19 b).freeBlock=basisInt (homKind 7 19) b := by decide
def polyLift7_20 (b : Fin 3) : PolyHom 7 20 :=
  ![PolyHom.zero 7 20,PolyHom.zero 7 20,PolyHom.zero 7 20] b
theorem polyLiftFree7_20 : ∀ b : Fin 3, (polyLift7_20 b).freeBlock=basisInt (homKind 7 20) b := by decide
def polyRep7_21_0 : PolyHom 7 21 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift7_21 (b : Fin 3) : PolyHom 7 21 :=
  ![polyRep7_21_0,PolyHom.zero 7 21,PolyHom.zero 7 21] b
theorem polyLiftFree7_21 : ∀ b : Fin 3, (polyLift7_21 b).freeBlock=basisInt (homKind 7 21) b := by decide
def polyLift7_22 (b : Fin 3) : PolyHom 7 22 :=
  ![PolyHom.zero 7 22,PolyHom.zero 7 22,PolyHom.zero 7 22] b
theorem polyLiftFree7_22 : ∀ b : Fin 3, (polyLift7_22 b).freeBlock=basisInt (homKind 7 22) b := by decide
def polyLift7_23 (b : Fin 3) : PolyHom 7 23 :=
  ![PolyHom.zero 7 23,PolyHom.zero 7 23,PolyHom.zero 7 23] b
theorem polyLiftFree7_23 : ∀ b : Fin 3, (polyLift7_23 b).freeBlock=basisInt (homKind 7 23) b := by decide
def polyRep7_24_0 : PolyHom 7 24 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift7_24 (b : Fin 3) : PolyHom 7 24 :=
  ![polyRep7_24_0,PolyHom.zero 7 24,PolyHom.zero 7 24] b
theorem polyLiftFree7_24 : ∀ b : Fin 3, (polyLift7_24 b).freeBlock=basisInt (homKind 7 24) b := by decide
def polyRep7_25_0 : PolyHom 7 25 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift7_25 (b : Fin 3) : PolyHom 7 25 :=
  ![polyRep7_25_0,PolyHom.zero 7 25,PolyHom.zero 7 25] b
theorem polyLiftFree7_25 : ∀ b : Fin 3, (polyLift7_25 b).freeBlock=basisInt (homKind 7 25) b := by decide
def polyLift7_26 (b : Fin 3) : PolyHom 7 26 :=
  ![PolyHom.zero 7 26,PolyHom.zero 7 26,PolyHom.zero 7 26] b
theorem polyLiftFree7_26 : ∀ b : Fin 3, (polyLift7_26 b).freeBlock=basisInt (homKind 7 26) b := by decide
def polyRep7_27_0 : PolyHom 7 27 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift7_27 (b : Fin 3) : PolyHom 7 27 :=
  ![polyRep7_27_0,PolyHom.zero 7 27,PolyHom.zero 7 27] b
theorem polyLiftFree7_27 : ∀ b : Fin 3, (polyLift7_27 b).freeBlock=basisInt (homKind 7 27) b := by decide
def polyLift7_28 (b : Fin 3) : PolyHom 7 28 :=
  ![PolyHom.zero 7 28,PolyHom.zero 7 28,PolyHom.zero 7 28] b
theorem polyLiftFree7_28 : ∀ b : Fin 3, (polyLift7_28 b).freeBlock=basisInt (homKind 7 28) b := by decide
def polyLift7_29 (b : Fin 3) : PolyHom 7 29 :=
  ![PolyHom.zero 7 29,PolyHom.zero 7 29,PolyHom.zero 7 29] b
theorem polyLiftFree7_29 : ∀ b : Fin 3, (polyLift7_29 b).freeBlock=basisInt (homKind 7 29) b := by decide
def polyRep7_30_0 : PolyHom 7 30 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift7_30 (b : Fin 3) : PolyHom 7 30 :=
  ![polyRep7_30_0,PolyHom.zero 7 30,PolyHom.zero 7 30] b
theorem polyLiftFree7_30 : ∀ b : Fin 3, (polyLift7_30 b).freeBlock=basisInt (homKind 7 30) b := by decide
def polyRep7_31_0 : PolyHom 7 31 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift7_31 (b : Fin 3) : PolyHom 7 31 :=
  ![polyRep7_31_0,PolyHom.zero 7 31,PolyHom.zero 7 31] b
theorem polyLiftFree7_31 : ∀ b : Fin 3, (polyLift7_31 b).freeBlock=basisInt (homKind 7 31) b := by decide
def polyRep7_32_0 : PolyHom 7 32 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift7_32 (b : Fin 3) : PolyHom 7 32 :=
  ![polyRep7_32_0,PolyHom.zero 7 32,PolyHom.zero 7 32] b
theorem polyLiftFree7_32 : ∀ b : Fin 3, (polyLift7_32 b).freeBlock=basisInt (homKind 7 32) b := by decide
def polyRep7_33_0 : PolyHom 7 33 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift7_33 (b : Fin 3) : PolyHom 7 33 :=
  ![polyRep7_33_0,PolyHom.zero 7 33,PolyHom.zero 7 33] b
theorem polyLiftFree7_33 : ∀ b : Fin 3, (polyLift7_33 b).freeBlock=basisInt (homKind 7 33) b := by decide
def polyRep7_34_0 : PolyHom 7 34 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift7_34 (b : Fin 3) : PolyHom 7 34 :=
  ![polyRep7_34_0,PolyHom.zero 7 34,PolyHom.zero 7 34] b
theorem polyLiftFree7_34 : ∀ b : Fin 3, (polyLift7_34 b).freeBlock=basisInt (homKind 7 34) b := by decide
def polyLift7_35 (b : Fin 3) : PolyHom 7 35 :=
  ![PolyHom.zero 7 35,PolyHom.zero 7 35,PolyHom.zero 7 35] b
theorem polyLiftFree7_35 : ∀ b : Fin 3, (polyLift7_35 b).freeBlock=basisInt (homKind 7 35) b := by decide
def polyLift7_36 (b : Fin 3) : PolyHom 7 36 :=
  ![PolyHom.zero 7 36,PolyHom.zero 7 36,PolyHom.zero 7 36] b
theorem polyLiftFree7_36 : ∀ b : Fin 3, (polyLift7_36 b).freeBlock=basisInt (homKind 7 36) b := by decide
def polyRep7_37_0 : PolyHom 7 37 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift7_37 (b : Fin 3) : PolyHom 7 37 :=
  ![polyRep7_37_0,PolyHom.zero 7 37,PolyHom.zero 7 37] b
theorem polyLiftFree7_37 : ∀ b : Fin 3, (polyLift7_37 b).freeBlock=basisInt (homKind 7 37) b := by decide
def polyRep7_38_0 : PolyHom 7 38 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift7_38 (b : Fin 3) : PolyHom 7 38 :=
  ![polyRep7_38_0,PolyHom.zero 7 38,PolyHom.zero 7 38] b
theorem polyLiftFree7_38 : ∀ b : Fin 3, (polyLift7_38 b).freeBlock=basisInt (homKind 7 38) b := by decide
def polyLift7_39 (b : Fin 3) : PolyHom 7 39 :=
  ![PolyHom.zero 7 39,PolyHom.zero 7 39,PolyHom.zero 7 39] b
theorem polyLiftFree7_39 : ∀ b : Fin 3, (polyLift7_39 b).freeBlock=basisInt (homKind 7 39) b := by decide
def polyRep7_40_0 : PolyHom 7 40 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift7_40 (b : Fin 3) : PolyHom 7 40 :=
  ![polyRep7_40_0,PolyHom.zero 7 40,PolyHom.zero 7 40] b
theorem polyLiftFree7_40 : ∀ b : Fin 3, (polyLift7_40 b).freeBlock=basisInt (homKind 7 40) b := by decide
def polyLift7_41 (b : Fin 3) : PolyHom 7 41 :=
  ![PolyHom.zero 7 41,PolyHom.zero 7 41,PolyHom.zero 7 41] b
theorem polyLiftFree7_41 : ∀ b : Fin 3, (polyLift7_41 b).freeBlock=basisInt (homKind 7 41) b := by decide
def polyRep7_42_0 : PolyHom 7 42 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift7_42 (b : Fin 3) : PolyHom 7 42 :=
  ![polyRep7_42_0,PolyHom.zero 7 42,PolyHom.zero 7 42] b
theorem polyLiftFree7_42 : ∀ b : Fin 3, (polyLift7_42 b).freeBlock=basisInt (homKind 7 42) b := by decide
def polyLift7_43 (b : Fin 3) : PolyHom 7 43 :=
  ![PolyHom.zero 7 43,PolyHom.zero 7 43,PolyHom.zero 7 43] b
theorem polyLiftFree7_43 : ∀ b : Fin 3, (polyLift7_43 b).freeBlock=basisInt (homKind 7 43) b := by decide
def polyRep7_44_0 : PolyHom 7 44 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift7_44 (b : Fin 3) : PolyHom 7 44 :=
  ![polyRep7_44_0,PolyHom.zero 7 44,PolyHom.zero 7 44] b
theorem polyLiftFree7_44 : ∀ b : Fin 3, (polyLift7_44 b).freeBlock=basisInt (homKind 7 44) b := by decide
def polyRep7_45_0 : PolyHom 7 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift7_45 (b : Fin 3) : PolyHom 7 45 :=
  ![polyRep7_45_0,PolyHom.zero 7 45,PolyHom.zero 7 45] b
theorem polyLiftFree7_45 : ∀ b : Fin 3, (polyLift7_45 b).freeBlock=basisInt (homKind 7 45) b := by decide
def polyLift7_46 (b : Fin 3) : PolyHom 7 46 :=
  ![PolyHom.zero 7 46,PolyHom.zero 7 46,PolyHom.zero 7 46] b
theorem polyLiftFree7_46 : ∀ b : Fin 3, (polyLift7_46 b).freeBlock=basisInt (homKind 7 46) b := by decide
def polyLiftRow7 (j : Fin 47) (b : Fin 3) : PolyHom 7 j :=
  match j with
  | ⟨0,_⟩ => polyLift7_0 b
  | ⟨1,_⟩ => polyLift7_1 b
  | ⟨2,_⟩ => polyLift7_2 b
  | ⟨3,_⟩ => polyLift7_3 b
  | ⟨4,_⟩ => polyLift7_4 b
  | ⟨5,_⟩ => polyLift7_5 b
  | ⟨6,_⟩ => polyLift7_6 b
  | ⟨7,_⟩ => polyLift7_7 b
  | ⟨8,_⟩ => polyLift7_8 b
  | ⟨9,_⟩ => polyLift7_9 b
  | ⟨10,_⟩ => polyLift7_10 b
  | ⟨11,_⟩ => polyLift7_11 b
  | ⟨12,_⟩ => polyLift7_12 b
  | ⟨13,_⟩ => polyLift7_13 b
  | ⟨14,_⟩ => polyLift7_14 b
  | ⟨15,_⟩ => polyLift7_15 b
  | ⟨16,_⟩ => polyLift7_16 b
  | ⟨17,_⟩ => polyLift7_17 b
  | ⟨18,_⟩ => polyLift7_18 b
  | ⟨19,_⟩ => polyLift7_19 b
  | ⟨20,_⟩ => polyLift7_20 b
  | ⟨21,_⟩ => polyLift7_21 b
  | ⟨22,_⟩ => polyLift7_22 b
  | ⟨23,_⟩ => polyLift7_23 b
  | ⟨24,_⟩ => polyLift7_24 b
  | ⟨25,_⟩ => polyLift7_25 b
  | ⟨26,_⟩ => polyLift7_26 b
  | ⟨27,_⟩ => polyLift7_27 b
  | ⟨28,_⟩ => polyLift7_28 b
  | ⟨29,_⟩ => polyLift7_29 b
  | ⟨30,_⟩ => polyLift7_30 b
  | ⟨31,_⟩ => polyLift7_31 b
  | ⟨32,_⟩ => polyLift7_32 b
  | ⟨33,_⟩ => polyLift7_33 b
  | ⟨34,_⟩ => polyLift7_34 b
  | ⟨35,_⟩ => polyLift7_35 b
  | ⟨36,_⟩ => polyLift7_36 b
  | ⟨37,_⟩ => polyLift7_37 b
  | ⟨38,_⟩ => polyLift7_38 b
  | ⟨39,_⟩ => polyLift7_39 b
  | ⟨40,_⟩ => polyLift7_40 b
  | ⟨41,_⟩ => polyLift7_41 b
  | ⟨42,_⟩ => polyLift7_42 b
  | ⟨43,_⟩ => polyLift7_43 b
  | ⟨44,_⟩ => polyLift7_44 b
  | ⟨45,_⟩ => polyLift7_45 b
  | ⟨46,_⟩ => polyLift7_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree7 (j : Fin 47) (b : Fin 3) : (polyLiftRow7 j b).freeBlock=basisInt (homKind 7 j) b := by
  fin_cases j
  · exact polyLiftFree7_0 b
  · exact polyLiftFree7_1 b
  · exact polyLiftFree7_2 b
  · exact polyLiftFree7_3 b
  · exact polyLiftFree7_4 b
  · exact polyLiftFree7_5 b
  · exact polyLiftFree7_6 b
  · exact polyLiftFree7_7 b
  · exact polyLiftFree7_8 b
  · exact polyLiftFree7_9 b
  · exact polyLiftFree7_10 b
  · exact polyLiftFree7_11 b
  · exact polyLiftFree7_12 b
  · exact polyLiftFree7_13 b
  · exact polyLiftFree7_14 b
  · exact polyLiftFree7_15 b
  · exact polyLiftFree7_16 b
  · exact polyLiftFree7_17 b
  · exact polyLiftFree7_18 b
  · exact polyLiftFree7_19 b
  · exact polyLiftFree7_20 b
  · exact polyLiftFree7_21 b
  · exact polyLiftFree7_22 b
  · exact polyLiftFree7_23 b
  · exact polyLiftFree7_24 b
  · exact polyLiftFree7_25 b
  · exact polyLiftFree7_26 b
  · exact polyLiftFree7_27 b
  · exact polyLiftFree7_28 b
  · exact polyLiftFree7_29 b
  · exact polyLiftFree7_30 b
  · exact polyLiftFree7_31 b
  · exact polyLiftFree7_32 b
  · exact polyLiftFree7_33 b
  · exact polyLiftFree7_34 b
  · exact polyLiftFree7_35 b
  · exact polyLiftFree7_36 b
  · exact polyLiftFree7_37 b
  · exact polyLiftFree7_38 b
  · exact polyLiftFree7_39 b
  · exact polyLiftFree7_40 b
  · exact polyLiftFree7_41 b
  · exact polyLiftFree7_42 b
  · exact polyLiftFree7_43 b
  · exact polyLiftFree7_44 b
  · exact polyLiftFree7_45 b
  · exact polyLiftFree7_46 b
end UniserialComputations.N6
