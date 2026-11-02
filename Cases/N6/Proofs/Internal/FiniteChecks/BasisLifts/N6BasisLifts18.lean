import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift18_0 (b : Fin 3) : PolyHom 18 0 :=
  ![PolyHom.zero 18 0,PolyHom.zero 18 0,PolyHom.zero 18 0] b
theorem polyLiftFree18_0 : ∀ b : Fin 3, (polyLift18_0 b).freeBlock=basisInt (homKind 18 0) b := by decide
def polyRep18_1_0 : PolyHom 18 1 where
  M := !![0,0,0,0;(mono6 (-1) 1),0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![(mono6 (-1) 0),0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_1 (b : Fin 3) : PolyHom 18 1 :=
  ![polyRep18_1_0,PolyHom.zero 18 1,PolyHom.zero 18 1] b
theorem polyLiftFree18_1 : ∀ b : Fin 3, (polyLift18_1 b).freeBlock=basisInt (homKind 18 1) b := by decide
def polyLift18_2 (b : Fin 3) : PolyHom 18 2 :=
  ![PolyHom.zero 18 2,PolyHom.zero 18 2,PolyHom.zero 18 2] b
theorem polyLiftFree18_2 : ∀ b : Fin 3, (polyLift18_2 b).freeBlock=basisInt (homKind 18 2) b := by decide
def polyRep18_3_0 : PolyHom 18 3 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_3 (b : Fin 3) : PolyHom 18 3 :=
  ![polyRep18_3_0,PolyHom.zero 18 3,PolyHom.zero 18 3] b
theorem polyLiftFree18_3 : ∀ b : Fin 3, (polyLift18_3 b).freeBlock=basisInt (homKind 18 3) b := by decide
def polyRep18_4_0 : PolyHom 18 4 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_4 (b : Fin 3) : PolyHom 18 4 :=
  ![polyRep18_4_0,PolyHom.zero 18 4,PolyHom.zero 18 4] b
theorem polyLiftFree18_4 : ∀ b : Fin 3, (polyLift18_4 b).freeBlock=basisInt (homKind 18 4) b := by decide
def polyRep18_5_0 : PolyHom 18 5 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_5 (b : Fin 3) : PolyHom 18 5 :=
  ![polyRep18_5_0,PolyHom.zero 18 5,PolyHom.zero 18 5] b
theorem polyLiftFree18_5 : ∀ b : Fin 3, (polyLift18_5 b).freeBlock=basisInt (homKind 18 5) b := by decide
def polyRep18_6_0 : PolyHom 18 6 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_6_1 : PolyHom 18 6 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_6 (b : Fin 3) : PolyHom 18 6 :=
  ![polyRep18_6_0,polyRep18_6_1,PolyHom.zero 18 6] b
theorem polyLiftFree18_6 : ∀ b : Fin 3, (polyLift18_6 b).freeBlock=basisInt (homKind 18 6) b := by decide
def polyRep18_7_0 : PolyHom 18 7 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_7_1 : PolyHom 18 7 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_7 (b : Fin 3) : PolyHom 18 7 :=
  ![polyRep18_7_0,polyRep18_7_1,PolyHom.zero 18 7] b
theorem polyLiftFree18_7 : ∀ b : Fin 3, (polyLift18_7 b).freeBlock=basisInt (homKind 18 7) b := by decide
def polyRep18_8_0 : PolyHom 18 8 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_8 (b : Fin 3) : PolyHom 18 8 :=
  ![polyRep18_8_0,PolyHom.zero 18 8,PolyHom.zero 18 8] b
theorem polyLiftFree18_8 : ∀ b : Fin 3, (polyLift18_8 b).freeBlock=basisInt (homKind 18 8) b := by decide
def polyRep18_9_0 : PolyHom 18 9 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_9 (b : Fin 3) : PolyHom 18 9 :=
  ![polyRep18_9_0,PolyHom.zero 18 9,PolyHom.zero 18 9] b
theorem polyLiftFree18_9 : ∀ b : Fin 3, (polyLift18_9 b).freeBlock=basisInt (homKind 18 9) b := by decide
def polyRep18_10_0 : PolyHom 18 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_10_1 : PolyHom 18 10 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 4),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_10 (b : Fin 3) : PolyHom 18 10 :=
  ![polyRep18_10_0,polyRep18_10_1,PolyHom.zero 18 10] b
theorem polyLiftFree18_10 : ∀ b : Fin 3, (polyLift18_10 b).freeBlock=basisInt (homKind 18 10) b := by decide
def polyRep18_11_0 : PolyHom 18 11 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_11_1 : PolyHom 18 11 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_11 (b : Fin 3) : PolyHom 18 11 :=
  ![polyRep18_11_0,polyRep18_11_1,PolyHom.zero 18 11] b
theorem polyLiftFree18_11 : ∀ b : Fin 3, (polyLift18_11 b).freeBlock=basisInt (homKind 18 11) b := by decide
def polyRep18_12_0 : PolyHom 18 12 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_12_1 : PolyHom 18 12 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_12 (b : Fin 3) : PolyHom 18 12 :=
  ![polyRep18_12_0,polyRep18_12_1,PolyHom.zero 18 12] b
theorem polyLiftFree18_12 : ∀ b : Fin 3, (polyLift18_12 b).freeBlock=basisInt (homKind 18 12) b := by decide
def polyRep18_13_0 : PolyHom 18 13 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_13 (b : Fin 3) : PolyHom 18 13 :=
  ![polyRep18_13_0,PolyHom.zero 18 13,PolyHom.zero 18 13] b
theorem polyLiftFree18_13 : ∀ b : Fin 3, (polyLift18_13 b).freeBlock=basisInt (homKind 18 13) b := by decide
def polyRep18_14_0 : PolyHom 18 14 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 0),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_14 (b : Fin 3) : PolyHom 18 14 :=
  ![polyRep18_14_0,PolyHom.zero 18 14,PolyHom.zero 18 14] b
theorem polyLiftFree18_14 : ∀ b : Fin 3, (polyLift18_14 b).freeBlock=basisInt (homKind 18 14) b := by decide
def polyRep18_15_0 : PolyHom 18 15 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_15 (b : Fin 3) : PolyHom 18 15 :=
  ![polyRep18_15_0,PolyHom.zero 18 15,PolyHom.zero 18 15] b
theorem polyLiftFree18_15 : ∀ b : Fin 3, (polyLift18_15 b).freeBlock=basisInt (homKind 18 15) b := by decide
def polyRep18_16_0 : PolyHom 18 16 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_16_1 : PolyHom 18 16 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_16 (b : Fin 3) : PolyHom 18 16 :=
  ![polyRep18_16_0,polyRep18_16_1,PolyHom.zero 18 16] b
theorem polyLiftFree18_16 : ∀ b : Fin 3, (polyLift18_16 b).freeBlock=basisInt (homKind 18 16) b := by decide
def polyRep18_17_0 : PolyHom 18 17 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_17 (b : Fin 3) : PolyHom 18 17 :=
  ![polyRep18_17_0,PolyHom.zero 18 17,PolyHom.zero 18 17] b
theorem polyLiftFree18_17 : ∀ b : Fin 3, (polyLift18_17 b).freeBlock=basisInt (homKind 18 17) b := by decide
def polyRep18_18_0 : PolyHom 18 18 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_18_1 : PolyHom 18 18 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_18 (b : Fin 3) : PolyHom 18 18 :=
  ![polyRep18_18_0,polyRep18_18_1,PolyHom.zero 18 18] b
theorem polyLiftFree18_18 : ∀ b : Fin 3, (polyLift18_18 b).freeBlock=basisInt (homKind 18 18) b := by decide
def polyRep18_19_0 : PolyHom 18 19 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_19 (b : Fin 3) : PolyHom 18 19 :=
  ![polyRep18_19_0,PolyHom.zero 18 19,PolyHom.zero 18 19] b
theorem polyLiftFree18_19 : ∀ b : Fin 3, (polyLift18_19 b).freeBlock=basisInt (homKind 18 19) b := by decide
def polyRep18_20_0 : PolyHom 18 20 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_20 (b : Fin 3) : PolyHom 18 20 :=
  ![polyRep18_20_0,PolyHom.zero 18 20,PolyHom.zero 18 20] b
theorem polyLiftFree18_20 : ∀ b : Fin 3, (polyLift18_20 b).freeBlock=basisInt (homKind 18 20) b := by decide
def polyRep18_21_0 : PolyHom 18 21 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_21_1 : PolyHom 18 21 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_21 (b : Fin 3) : PolyHom 18 21 :=
  ![polyRep18_21_0,polyRep18_21_1,PolyHom.zero 18 21] b
theorem polyLiftFree18_21 : ∀ b : Fin 3, (polyLift18_21 b).freeBlock=basisInt (homKind 18 21) b := by decide
def polyRep18_22_0 : PolyHom 18 22 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_22_1 : PolyHom 18 22 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_22 (b : Fin 3) : PolyHom 18 22 :=
  ![polyRep18_22_0,polyRep18_22_1,PolyHom.zero 18 22] b
theorem polyLiftFree18_22 : ∀ b : Fin 3, (polyLift18_22 b).freeBlock=basisInt (homKind 18 22) b := by decide
def polyRep18_23_0 : PolyHom 18 23 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_23 (b : Fin 3) : PolyHom 18 23 :=
  ![polyRep18_23_0,PolyHom.zero 18 23,PolyHom.zero 18 23] b
theorem polyLiftFree18_23 : ∀ b : Fin 3, (polyLift18_23 b).freeBlock=basisInt (homKind 18 23) b := by decide
def polyRep18_24_0 : PolyHom 18 24 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_24_1 : PolyHom 18 24 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_24 (b : Fin 3) : PolyHom 18 24 :=
  ![polyRep18_24_0,polyRep18_24_1,PolyHom.zero 18 24] b
theorem polyLiftFree18_24 : ∀ b : Fin 3, (polyLift18_24 b).freeBlock=basisInt (homKind 18 24) b := by decide
def polyRep18_25_0 : PolyHom 18 25 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_25_1 : PolyHom 18 25 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_25 (b : Fin 3) : PolyHom 18 25 :=
  ![polyRep18_25_0,polyRep18_25_1,PolyHom.zero 18 25] b
theorem polyLiftFree18_25 : ∀ b : Fin 3, (polyLift18_25 b).freeBlock=basisInt (homKind 18 25) b := by decide
def polyRep18_26_0 : PolyHom 18 26 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_26_1 : PolyHom 18 26 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_26 (b : Fin 3) : PolyHom 18 26 :=
  ![polyRep18_26_0,polyRep18_26_1,PolyHom.zero 18 26] b
theorem polyLiftFree18_26 : ∀ b : Fin 3, (polyLift18_26 b).freeBlock=basisInt (homKind 18 26) b := by decide
def polyRep18_27_0 : PolyHom 18 27 where
  M := !![(mono6 (1) 0),0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_27_1 : PolyHom 18 27 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_27 (b : Fin 3) : PolyHom 18 27 :=
  ![polyRep18_27_0,polyRep18_27_1,PolyHom.zero 18 27] b
theorem polyLiftFree18_27 : ∀ b : Fin 3, (polyLift18_27 b).freeBlock=basisInt (homKind 18 27) b := by decide
def polyRep18_28_0 : PolyHom 18 28 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_28 (b : Fin 3) : PolyHom 18 28 :=
  ![polyRep18_28_0,PolyHom.zero 18 28,PolyHom.zero 18 28] b
theorem polyLiftFree18_28 : ∀ b : Fin 3, (polyLift18_28 b).freeBlock=basisInt (homKind 18 28) b := by decide
def polyRep18_29_0 : PolyHom 18 29 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_29 (b : Fin 3) : PolyHom 18 29 :=
  ![polyRep18_29_0,PolyHom.zero 18 29,PolyHom.zero 18 29] b
theorem polyLiftFree18_29 : ∀ b : Fin 3, (polyLift18_29 b).freeBlock=basisInt (homKind 18 29) b := by decide
def polyRep18_30_0 : PolyHom 18 30 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_30_1 : PolyHom 18 30 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_30_2 : PolyHom 18 30 where
  M := !![(mono6 (1) 1),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_30 (b : Fin 3) : PolyHom 18 30 :=
  ![polyRep18_30_0,polyRep18_30_1,polyRep18_30_2] b
theorem polyLiftFree18_30 : ∀ b : Fin 3, (polyLift18_30 b).freeBlock=basisInt (homKind 18 30) b := by decide
def polyRep18_31_0 : PolyHom 18 31 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_31_1 : PolyHom 18 31 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_31_2 : PolyHom 18 31 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_31 (b : Fin 3) : PolyHom 18 31 :=
  ![polyRep18_31_0,polyRep18_31_1,polyRep18_31_2] b
theorem polyLiftFree18_31 : ∀ b : Fin 3, (polyLift18_31 b).freeBlock=basisInt (homKind 18 31) b := by decide
def polyRep18_32_0 : PolyHom 18 32 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_32_1 : PolyHom 18 32 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_32_2 : PolyHom 18 32 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_32 (b : Fin 3) : PolyHom 18 32 :=
  ![polyRep18_32_0,polyRep18_32_1,polyRep18_32_2] b
theorem polyLiftFree18_32 : ∀ b : Fin 3, (polyLift18_32 b).freeBlock=basisInt (homKind 18 32) b := by decide
def polyRep18_33_0 : PolyHom 18 33 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_33_1 : PolyHom 18 33 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_33 (b : Fin 3) : PolyHom 18 33 :=
  ![polyRep18_33_0,polyRep18_33_1,PolyHom.zero 18 33] b
theorem polyLiftFree18_33 : ∀ b : Fin 3, (polyLift18_33 b).freeBlock=basisInt (homKind 18 33) b := by decide
def polyRep18_34_0 : PolyHom 18 34 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_34_1 : PolyHom 18 34 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_34 (b : Fin 3) : PolyHom 18 34 :=
  ![polyRep18_34_0,polyRep18_34_1,PolyHom.zero 18 34] b
theorem polyLiftFree18_34 : ∀ b : Fin 3, (polyLift18_34 b).freeBlock=basisInt (homKind 18 34) b := by decide
def polyRep18_35_0 : PolyHom 18 35 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 1),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_35 (b : Fin 3) : PolyHom 18 35 :=
  ![polyRep18_35_0,PolyHom.zero 18 35,PolyHom.zero 18 35] b
theorem polyLiftFree18_35 : ∀ b : Fin 3, (polyLift18_35 b).freeBlock=basisInt (homKind 18 35) b := by decide
def polyRep18_36_0 : PolyHom 18 36 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_36_1 : PolyHom 18 36 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_36 (b : Fin 3) : PolyHom 18 36 :=
  ![polyRep18_36_0,polyRep18_36_1,PolyHom.zero 18 36] b
theorem polyLiftFree18_36 : ∀ b : Fin 3, (polyLift18_36 b).freeBlock=basisInt (homKind 18 36) b := by decide
def polyRep18_37_0 : PolyHom 18 37 where
  M := !![0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_37_1 : PolyHom 18 37 where
  M := !![0,0,0,0;0,0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_37_2 : PolyHom 18 37 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_37 (b : Fin 3) : PolyHom 18 37 :=
  ![polyRep18_37_0,polyRep18_37_1,polyRep18_37_2] b
theorem polyLiftFree18_37 : ∀ b : Fin 3, (polyLift18_37 b).freeBlock=basisInt (homKind 18 37) b := by decide
def polyRep18_38_0 : PolyHom 18 38 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_38_1 : PolyHom 18 38 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_38_2 : PolyHom 18 38 where
  M := !![(mono6 (1) 0),(mono6 (1) 1),0,0;0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_38 (b : Fin 3) : PolyHom 18 38 :=
  ![polyRep18_38_0,polyRep18_38_1,polyRep18_38_2] b
theorem polyLiftFree18_38 : ∀ b : Fin 3, (polyLift18_38 b).freeBlock=basisInt (homKind 18 38) b := by decide
def polyRep18_39_0 : PolyHom 18 39 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_39_1 : PolyHom 18 39 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_39_2 : PolyHom 18 39 where
  M := !![(mono6 (1) 0),(mono6 (1) 0),0,0;0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_39 (b : Fin 3) : PolyHom 18 39 :=
  ![polyRep18_39_0,polyRep18_39_1,polyRep18_39_2] b
theorem polyLiftFree18_39 : ∀ b : Fin 3, (polyLift18_39 b).freeBlock=basisInt (homKind 18 39) b := by decide
def polyRep18_40_0 : PolyHom 18 40 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_40_1 : PolyHom 18 40 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_40_2 : PolyHom 18 40 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_40 (b : Fin 3) : PolyHom 18 40 :=
  ![polyRep18_40_0,polyRep18_40_1,polyRep18_40_2] b
theorem polyLiftFree18_40 : ∀ b : Fin 3, (polyLift18_40 b).freeBlock=basisInt (homKind 18 40) b := by decide
def polyRep18_41_0 : PolyHom 18 41 where
  M := !![0,(mono6 (-1) 0),0,0;0,0,(mono6 (1) 0),0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![(mono6 (1) 0),0;0,(mono6 (1) 0)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_41_1 : PolyHom 18 41 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_41 (b : Fin 3) : PolyHom 18 41 :=
  ![polyRep18_41_0,polyRep18_41_1,PolyHom.zero 18 41] b
theorem polyLiftFree18_41 : ∀ b : Fin 3, (polyLift18_41 b).freeBlock=basisInt (homKind 18 41) b := by decide
def polyRep18_42_0 : PolyHom 18 42 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_42_1 : PolyHom 18 42 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_42_2 : PolyHom 18 42 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_42 (b : Fin 3) : PolyHom 18 42 :=
  ![polyRep18_42_0,polyRep18_42_1,polyRep18_42_2] b
theorem polyLiftFree18_42 : ∀ b : Fin 3, (polyLift18_42 b).freeBlock=basisInt (homKind 18 42) b := by decide
def polyRep18_43_0 : PolyHom 18 43 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 2),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_43_1 : PolyHom 18 43 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_43 (b : Fin 3) : PolyHom 18 43 :=
  ![polyRep18_43_0,polyRep18_43_1,PolyHom.zero 18 43] b
theorem polyLiftFree18_43 : ∀ b : Fin 3, (polyLift18_43 b).freeBlock=basisInt (homKind 18 43) b := by decide
def polyRep18_44_0 : PolyHom 18 44 where
  M := !![0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_44_1 : PolyHom 18 44 where
  M := !![0,0,0,0;0,0,0,0;0,0,(mono6 (1) 0),0;0,0,0,0]
  U := !![0,0;(mono6 (1) 3),0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_44_2 : PolyHom 18 44 where
  M := !![0,(mono6 (-1) 1),0,0;0,0,0,0;0,0,0,(mono6 (1) 0);0,0,0,0]
  U := !![0,0;0,(mono6 (1) 1)]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_44 (b : Fin 3) : PolyHom 18 44 :=
  ![polyRep18_44_0,polyRep18_44_1,polyRep18_44_2] b
theorem polyLiftFree18_44 : ∀ b : Fin 3, (polyLift18_44 b).freeBlock=basisInt (homKind 18 44) b := by decide
def polyRep18_45_0 : PolyHom 18 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyRep18_45_1 : PolyHom 18 45 where
  M := !![0,0,0,0;0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift18_45 (b : Fin 3) : PolyHom 18 45 :=
  ![polyRep18_45_0,polyRep18_45_1,PolyHom.zero 18 45] b
theorem polyLiftFree18_45 : ∀ b : Fin 3, (polyLift18_45 b).freeBlock=basisInt (homKind 18 45) b := by decide
def polyLift18_46 (b : Fin 3) : PolyHom 18 46 :=
  ![PolyHom.zero 18 46,PolyHom.zero 18 46,PolyHom.zero 18 46] b
theorem polyLiftFree18_46 : ∀ b : Fin 3, (polyLift18_46 b).freeBlock=basisInt (homKind 18 46) b := by decide
def polyLiftRow18 (j : Fin 47) (b : Fin 3) : PolyHom 18 j :=
  match j with
  | ⟨0,_⟩ => polyLift18_0 b
  | ⟨1,_⟩ => polyLift18_1 b
  | ⟨2,_⟩ => polyLift18_2 b
  | ⟨3,_⟩ => polyLift18_3 b
  | ⟨4,_⟩ => polyLift18_4 b
  | ⟨5,_⟩ => polyLift18_5 b
  | ⟨6,_⟩ => polyLift18_6 b
  | ⟨7,_⟩ => polyLift18_7 b
  | ⟨8,_⟩ => polyLift18_8 b
  | ⟨9,_⟩ => polyLift18_9 b
  | ⟨10,_⟩ => polyLift18_10 b
  | ⟨11,_⟩ => polyLift18_11 b
  | ⟨12,_⟩ => polyLift18_12 b
  | ⟨13,_⟩ => polyLift18_13 b
  | ⟨14,_⟩ => polyLift18_14 b
  | ⟨15,_⟩ => polyLift18_15 b
  | ⟨16,_⟩ => polyLift18_16 b
  | ⟨17,_⟩ => polyLift18_17 b
  | ⟨18,_⟩ => polyLift18_18 b
  | ⟨19,_⟩ => polyLift18_19 b
  | ⟨20,_⟩ => polyLift18_20 b
  | ⟨21,_⟩ => polyLift18_21 b
  | ⟨22,_⟩ => polyLift18_22 b
  | ⟨23,_⟩ => polyLift18_23 b
  | ⟨24,_⟩ => polyLift18_24 b
  | ⟨25,_⟩ => polyLift18_25 b
  | ⟨26,_⟩ => polyLift18_26 b
  | ⟨27,_⟩ => polyLift18_27 b
  | ⟨28,_⟩ => polyLift18_28 b
  | ⟨29,_⟩ => polyLift18_29 b
  | ⟨30,_⟩ => polyLift18_30 b
  | ⟨31,_⟩ => polyLift18_31 b
  | ⟨32,_⟩ => polyLift18_32 b
  | ⟨33,_⟩ => polyLift18_33 b
  | ⟨34,_⟩ => polyLift18_34 b
  | ⟨35,_⟩ => polyLift18_35 b
  | ⟨36,_⟩ => polyLift18_36 b
  | ⟨37,_⟩ => polyLift18_37 b
  | ⟨38,_⟩ => polyLift18_38 b
  | ⟨39,_⟩ => polyLift18_39 b
  | ⟨40,_⟩ => polyLift18_40 b
  | ⟨41,_⟩ => polyLift18_41 b
  | ⟨42,_⟩ => polyLift18_42 b
  | ⟨43,_⟩ => polyLift18_43 b
  | ⟨44,_⟩ => polyLift18_44 b
  | ⟨45,_⟩ => polyLift18_45 b
  | ⟨46,_⟩ => polyLift18_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree18 (j : Fin 47) (b : Fin 3) : (polyLiftRow18 j b).freeBlock=basisInt (homKind 18 j) b := by
  fin_cases j
  · exact polyLiftFree18_0 b
  · exact polyLiftFree18_1 b
  · exact polyLiftFree18_2 b
  · exact polyLiftFree18_3 b
  · exact polyLiftFree18_4 b
  · exact polyLiftFree18_5 b
  · exact polyLiftFree18_6 b
  · exact polyLiftFree18_7 b
  · exact polyLiftFree18_8 b
  · exact polyLiftFree18_9 b
  · exact polyLiftFree18_10 b
  · exact polyLiftFree18_11 b
  · exact polyLiftFree18_12 b
  · exact polyLiftFree18_13 b
  · exact polyLiftFree18_14 b
  · exact polyLiftFree18_15 b
  · exact polyLiftFree18_16 b
  · exact polyLiftFree18_17 b
  · exact polyLiftFree18_18 b
  · exact polyLiftFree18_19 b
  · exact polyLiftFree18_20 b
  · exact polyLiftFree18_21 b
  · exact polyLiftFree18_22 b
  · exact polyLiftFree18_23 b
  · exact polyLiftFree18_24 b
  · exact polyLiftFree18_25 b
  · exact polyLiftFree18_26 b
  · exact polyLiftFree18_27 b
  · exact polyLiftFree18_28 b
  · exact polyLiftFree18_29 b
  · exact polyLiftFree18_30 b
  · exact polyLiftFree18_31 b
  · exact polyLiftFree18_32 b
  · exact polyLiftFree18_33 b
  · exact polyLiftFree18_34 b
  · exact polyLiftFree18_35 b
  · exact polyLiftFree18_36 b
  · exact polyLiftFree18_37 b
  · exact polyLiftFree18_38 b
  · exact polyLiftFree18_39 b
  · exact polyLiftFree18_40 b
  · exact polyLiftFree18_41 b
  · exact polyLiftFree18_42 b
  · exact polyLiftFree18_43 b
  · exact polyLiftFree18_44 b
  · exact polyLiftFree18_45 b
  · exact polyLiftFree18_46 b
end UniserialComputations.N6
