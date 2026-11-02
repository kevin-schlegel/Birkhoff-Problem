import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift6_0 (b : Fin 3) : PolyHom 6 0 :=
  ![PolyHom.zero 6 0,PolyHom.zero 6 0,PolyHom.zero 6 0] b
theorem polyLiftFree6_0 : ∀ b : Fin 3, (polyLift6_0 b).freeBlock=basisInt (homKind 6 0) b := by decide
def polyLift6_1 (b : Fin 3) : PolyHom 6 1 :=
  ![PolyHom.zero 6 1,PolyHom.zero 6 1,PolyHom.zero 6 1] b
theorem polyLiftFree6_1 : ∀ b : Fin 3, (polyLift6_1 b).freeBlock=basisInt (homKind 6 1) b := by decide
def polyLift6_2 (b : Fin 3) : PolyHom 6 2 :=
  ![PolyHom.zero 6 2,PolyHom.zero 6 2,PolyHom.zero 6 2] b
theorem polyLiftFree6_2 : ∀ b : Fin 3, (polyLift6_2 b).freeBlock=basisInt (homKind 6 2) b := by decide
def polyLift6_3 (b : Fin 3) : PolyHom 6 3 :=
  ![PolyHom.zero 6 3,PolyHom.zero 6 3,PolyHom.zero 6 3] b
theorem polyLiftFree6_3 : ∀ b : Fin 3, (polyLift6_3 b).freeBlock=basisInt (homKind 6 3) b := by decide
def polyLift6_4 (b : Fin 3) : PolyHom 6 4 :=
  ![PolyHom.zero 6 4,PolyHom.zero 6 4,PolyHom.zero 6 4] b
theorem polyLiftFree6_4 : ∀ b : Fin 3, (polyLift6_4 b).freeBlock=basisInt (homKind 6 4) b := by decide
def polyLift6_5 (b : Fin 3) : PolyHom 6 5 :=
  ![PolyHom.zero 6 5,PolyHom.zero 6 5,PolyHom.zero 6 5] b
theorem polyLiftFree6_5 : ∀ b : Fin 3, (polyLift6_5 b).freeBlock=basisInt (homKind 6 5) b := by decide
def polyRep6_6_0 : PolyHom 6 6 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift6_6 (b : Fin 3) : PolyHom 6 6 :=
  ![polyRep6_6_0,PolyHom.zero 6 6,PolyHom.zero 6 6] b
theorem polyLiftFree6_6 : ∀ b : Fin 3, (polyLift6_6 b).freeBlock=basisInt (homKind 6 6) b := by decide
def polyLift6_7 (b : Fin 3) : PolyHom 6 7 :=
  ![PolyHom.zero 6 7,PolyHom.zero 6 7,PolyHom.zero 6 7] b
theorem polyLiftFree6_7 : ∀ b : Fin 3, (polyLift6_7 b).freeBlock=basisInt (homKind 6 7) b := by decide
def polyLift6_8 (b : Fin 3) : PolyHom 6 8 :=
  ![PolyHom.zero 6 8,PolyHom.zero 6 8,PolyHom.zero 6 8] b
theorem polyLiftFree6_8 : ∀ b : Fin 3, (polyLift6_8 b).freeBlock=basisInt (homKind 6 8) b := by decide
def polyLift6_9 (b : Fin 3) : PolyHom 6 9 :=
  ![PolyHom.zero 6 9,PolyHom.zero 6 9,PolyHom.zero 6 9] b
theorem polyLiftFree6_9 : ∀ b : Fin 3, (polyLift6_9 b).freeBlock=basisInt (homKind 6 9) b := by decide
def polyRep6_10_0 : PolyHom 6 10 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift6_10 (b : Fin 3) : PolyHom 6 10 :=
  ![polyRep6_10_0,PolyHom.zero 6 10,PolyHom.zero 6 10] b
theorem polyLiftFree6_10 : ∀ b : Fin 3, (polyLift6_10 b).freeBlock=basisInt (homKind 6 10) b := by decide
def polyRep6_11_0 : PolyHom 6 11 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift6_11 (b : Fin 3) : PolyHom 6 11 :=
  ![polyRep6_11_0,PolyHom.zero 6 11,PolyHom.zero 6 11] b
theorem polyLiftFree6_11 : ∀ b : Fin 3, (polyLift6_11 b).freeBlock=basisInt (homKind 6 11) b := by decide
def polyLift6_12 (b : Fin 3) : PolyHom 6 12 :=
  ![PolyHom.zero 6 12,PolyHom.zero 6 12,PolyHom.zero 6 12] b
theorem polyLiftFree6_12 : ∀ b : Fin 3, (polyLift6_12 b).freeBlock=basisInt (homKind 6 12) b := by decide
def polyLift6_13 (b : Fin 3) : PolyHom 6 13 :=
  ![PolyHom.zero 6 13,PolyHom.zero 6 13,PolyHom.zero 6 13] b
theorem polyLiftFree6_13 : ∀ b : Fin 3, (polyLift6_13 b).freeBlock=basisInt (homKind 6 13) b := by decide
def polyLift6_14 (b : Fin 3) : PolyHom 6 14 :=
  ![PolyHom.zero 6 14,PolyHom.zero 6 14,PolyHom.zero 6 14] b
theorem polyLiftFree6_14 : ∀ b : Fin 3, (polyLift6_14 b).freeBlock=basisInt (homKind 6 14) b := by decide
def polyLift6_15 (b : Fin 3) : PolyHom 6 15 :=
  ![PolyHom.zero 6 15,PolyHom.zero 6 15,PolyHom.zero 6 15] b
theorem polyLiftFree6_15 : ∀ b : Fin 3, (polyLift6_15 b).freeBlock=basisInt (homKind 6 15) b := by decide
def polyLift6_16 (b : Fin 3) : PolyHom 6 16 :=
  ![PolyHom.zero 6 16,PolyHom.zero 6 16,PolyHom.zero 6 16] b
theorem polyLiftFree6_16 : ∀ b : Fin 3, (polyLift6_16 b).freeBlock=basisInt (homKind 6 16) b := by decide
def polyLift6_17 (b : Fin 3) : PolyHom 6 17 :=
  ![PolyHom.zero 6 17,PolyHom.zero 6 17,PolyHom.zero 6 17] b
theorem polyLiftFree6_17 : ∀ b : Fin 3, (polyLift6_17 b).freeBlock=basisInt (homKind 6 17) b := by decide
def polyLift6_18 (b : Fin 3) : PolyHom 6 18 :=
  ![PolyHom.zero 6 18,PolyHom.zero 6 18,PolyHom.zero 6 18] b
theorem polyLiftFree6_18 : ∀ b : Fin 3, (polyLift6_18 b).freeBlock=basisInt (homKind 6 18) b := by decide
def polyLift6_19 (b : Fin 3) : PolyHom 6 19 :=
  ![PolyHom.zero 6 19,PolyHom.zero 6 19,PolyHom.zero 6 19] b
theorem polyLiftFree6_19 : ∀ b : Fin 3, (polyLift6_19 b).freeBlock=basisInt (homKind 6 19) b := by decide
def polyLift6_20 (b : Fin 3) : PolyHom 6 20 :=
  ![PolyHom.zero 6 20,PolyHom.zero 6 20,PolyHom.zero 6 20] b
theorem polyLiftFree6_20 : ∀ b : Fin 3, (polyLift6_20 b).freeBlock=basisInt (homKind 6 20) b := by decide
def polyRep6_21_0 : PolyHom 6 21 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift6_21 (b : Fin 3) : PolyHom 6 21 :=
  ![polyRep6_21_0,PolyHom.zero 6 21,PolyHom.zero 6 21] b
theorem polyLiftFree6_21 : ∀ b : Fin 3, (polyLift6_21 b).freeBlock=basisInt (homKind 6 21) b := by decide
def polyLift6_22 (b : Fin 3) : PolyHom 6 22 :=
  ![PolyHom.zero 6 22,PolyHom.zero 6 22,PolyHom.zero 6 22] b
theorem polyLiftFree6_22 : ∀ b : Fin 3, (polyLift6_22 b).freeBlock=basisInt (homKind 6 22) b := by decide
def polyLift6_23 (b : Fin 3) : PolyHom 6 23 :=
  ![PolyHom.zero 6 23,PolyHom.zero 6 23,PolyHom.zero 6 23] b
theorem polyLiftFree6_23 : ∀ b : Fin 3, (polyLift6_23 b).freeBlock=basisInt (homKind 6 23) b := by decide
def polyRep6_24_0 : PolyHom 6 24 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift6_24 (b : Fin 3) : PolyHom 6 24 :=
  ![polyRep6_24_0,PolyHom.zero 6 24,PolyHom.zero 6 24] b
theorem polyLiftFree6_24 : ∀ b : Fin 3, (polyLift6_24 b).freeBlock=basisInt (homKind 6 24) b := by decide
def polyRep6_25_0 : PolyHom 6 25 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift6_25 (b : Fin 3) : PolyHom 6 25 :=
  ![polyRep6_25_0,PolyHom.zero 6 25,PolyHom.zero 6 25] b
theorem polyLiftFree6_25 : ∀ b : Fin 3, (polyLift6_25 b).freeBlock=basisInt (homKind 6 25) b := by decide
def polyLift6_26 (b : Fin 3) : PolyHom 6 26 :=
  ![PolyHom.zero 6 26,PolyHom.zero 6 26,PolyHom.zero 6 26] b
theorem polyLiftFree6_26 : ∀ b : Fin 3, (polyLift6_26 b).freeBlock=basisInt (homKind 6 26) b := by decide
def polyLift6_27 (b : Fin 3) : PolyHom 6 27 :=
  ![PolyHom.zero 6 27,PolyHom.zero 6 27,PolyHom.zero 6 27] b
theorem polyLiftFree6_27 : ∀ b : Fin 3, (polyLift6_27 b).freeBlock=basisInt (homKind 6 27) b := by decide
def polyLift6_28 (b : Fin 3) : PolyHom 6 28 :=
  ![PolyHom.zero 6 28,PolyHom.zero 6 28,PolyHom.zero 6 28] b
theorem polyLiftFree6_28 : ∀ b : Fin 3, (polyLift6_28 b).freeBlock=basisInt (homKind 6 28) b := by decide
def polyLift6_29 (b : Fin 3) : PolyHom 6 29 :=
  ![PolyHom.zero 6 29,PolyHom.zero 6 29,PolyHom.zero 6 29] b
theorem polyLiftFree6_29 : ∀ b : Fin 3, (polyLift6_29 b).freeBlock=basisInt (homKind 6 29) b := by decide
def polyRep6_30_0 : PolyHom 6 30 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift6_30 (b : Fin 3) : PolyHom 6 30 :=
  ![polyRep6_30_0,PolyHom.zero 6 30,PolyHom.zero 6 30] b
theorem polyLiftFree6_30 : ∀ b : Fin 3, (polyLift6_30 b).freeBlock=basisInt (homKind 6 30) b := by decide
def polyRep6_31_0 : PolyHom 6 31 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift6_31 (b : Fin 3) : PolyHom 6 31 :=
  ![polyRep6_31_0,PolyHom.zero 6 31,PolyHom.zero 6 31] b
theorem polyLiftFree6_31 : ∀ b : Fin 3, (polyLift6_31 b).freeBlock=basisInt (homKind 6 31) b := by decide
def polyLift6_32 (b : Fin 3) : PolyHom 6 32 :=
  ![PolyHom.zero 6 32,PolyHom.zero 6 32,PolyHom.zero 6 32] b
theorem polyLiftFree6_32 : ∀ b : Fin 3, (polyLift6_32 b).freeBlock=basisInt (homKind 6 32) b := by decide
def polyRep6_33_0 : PolyHom 6 33 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift6_33 (b : Fin 3) : PolyHom 6 33 :=
  ![polyRep6_33_0,PolyHom.zero 6 33,PolyHom.zero 6 33] b
theorem polyLiftFree6_33 : ∀ b : Fin 3, (polyLift6_33 b).freeBlock=basisInt (homKind 6 33) b := by decide
def polyLift6_34 (b : Fin 3) : PolyHom 6 34 :=
  ![PolyHom.zero 6 34,PolyHom.zero 6 34,PolyHom.zero 6 34] b
theorem polyLiftFree6_34 : ∀ b : Fin 3, (polyLift6_34 b).freeBlock=basisInt (homKind 6 34) b := by decide
def polyLift6_35 (b : Fin 3) : PolyHom 6 35 :=
  ![PolyHom.zero 6 35,PolyHom.zero 6 35,PolyHom.zero 6 35] b
theorem polyLiftFree6_35 : ∀ b : Fin 3, (polyLift6_35 b).freeBlock=basisInt (homKind 6 35) b := by decide
def polyLift6_36 (b : Fin 3) : PolyHom 6 36 :=
  ![PolyHom.zero 6 36,PolyHom.zero 6 36,PolyHom.zero 6 36] b
theorem polyLiftFree6_36 : ∀ b : Fin 3, (polyLift6_36 b).freeBlock=basisInt (homKind 6 36) b := by decide
def polyRep6_37_0 : PolyHom 6 37 where
  M := !![0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift6_37 (b : Fin 3) : PolyHom 6 37 :=
  ![polyRep6_37_0,PolyHom.zero 6 37,PolyHom.zero 6 37] b
theorem polyLiftFree6_37 : ∀ b : Fin 3, (polyLift6_37 b).freeBlock=basisInt (homKind 6 37) b := by decide
def polyLift6_38 (b : Fin 3) : PolyHom 6 38 :=
  ![PolyHom.zero 6 38,PolyHom.zero 6 38,PolyHom.zero 6 38] b
theorem polyLiftFree6_38 : ∀ b : Fin 3, (polyLift6_38 b).freeBlock=basisInt (homKind 6 38) b := by decide
def polyLift6_39 (b : Fin 3) : PolyHom 6 39 :=
  ![PolyHom.zero 6 39,PolyHom.zero 6 39,PolyHom.zero 6 39] b
theorem polyLiftFree6_39 : ∀ b : Fin 3, (polyLift6_39 b).freeBlock=basisInt (homKind 6 39) b := by decide
def polyRep6_40_0 : PolyHom 6 40 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift6_40 (b : Fin 3) : PolyHom 6 40 :=
  ![polyRep6_40_0,PolyHom.zero 6 40,PolyHom.zero 6 40] b
theorem polyLiftFree6_40 : ∀ b : Fin 3, (polyLift6_40 b).freeBlock=basisInt (homKind 6 40) b := by decide
def polyLift6_41 (b : Fin 3) : PolyHom 6 41 :=
  ![PolyHom.zero 6 41,PolyHom.zero 6 41,PolyHom.zero 6 41] b
theorem polyLiftFree6_41 : ∀ b : Fin 3, (polyLift6_41 b).freeBlock=basisInt (homKind 6 41) b := by decide
def polyRep6_42_0 : PolyHom 6 42 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift6_42 (b : Fin 3) : PolyHom 6 42 :=
  ![polyRep6_42_0,PolyHom.zero 6 42,PolyHom.zero 6 42] b
theorem polyLiftFree6_42 : ∀ b : Fin 3, (polyLift6_42 b).freeBlock=basisInt (homKind 6 42) b := by decide
def polyLift6_43 (b : Fin 3) : PolyHom 6 43 :=
  ![PolyHom.zero 6 43,PolyHom.zero 6 43,PolyHom.zero 6 43] b
theorem polyLiftFree6_43 : ∀ b : Fin 3, (polyLift6_43 b).freeBlock=basisInt (homKind 6 43) b := by decide
def polyRep6_44_0 : PolyHom 6 44 where
  M := !![0,0,(mono6 (1) 0),0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift6_44 (b : Fin 3) : PolyHom 6 44 :=
  ![polyRep6_44_0,PolyHom.zero 6 44,PolyHom.zero 6 44] b
theorem polyLiftFree6_44 : ∀ b : Fin 3, (polyLift6_44 b).freeBlock=basisInt (homKind 6 44) b := by decide
def polyRep6_45_0 : PolyHom 6 45 where
  M := !![(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift6_45 (b : Fin 3) : PolyHom 6 45 :=
  ![polyRep6_45_0,PolyHom.zero 6 45,PolyHom.zero 6 45] b
theorem polyLiftFree6_45 : ∀ b : Fin 3, (polyLift6_45 b).freeBlock=basisInt (homKind 6 45) b := by decide
def polyLift6_46 (b : Fin 3) : PolyHom 6 46 :=
  ![PolyHom.zero 6 46,PolyHom.zero 6 46,PolyHom.zero 6 46] b
theorem polyLiftFree6_46 : ∀ b : Fin 3, (polyLift6_46 b).freeBlock=basisInt (homKind 6 46) b := by decide
def polyLiftRow6 (j : Fin 47) (b : Fin 3) : PolyHom 6 j :=
  match j with
  | ⟨0,_⟩ => polyLift6_0 b
  | ⟨1,_⟩ => polyLift6_1 b
  | ⟨2,_⟩ => polyLift6_2 b
  | ⟨3,_⟩ => polyLift6_3 b
  | ⟨4,_⟩ => polyLift6_4 b
  | ⟨5,_⟩ => polyLift6_5 b
  | ⟨6,_⟩ => polyLift6_6 b
  | ⟨7,_⟩ => polyLift6_7 b
  | ⟨8,_⟩ => polyLift6_8 b
  | ⟨9,_⟩ => polyLift6_9 b
  | ⟨10,_⟩ => polyLift6_10 b
  | ⟨11,_⟩ => polyLift6_11 b
  | ⟨12,_⟩ => polyLift6_12 b
  | ⟨13,_⟩ => polyLift6_13 b
  | ⟨14,_⟩ => polyLift6_14 b
  | ⟨15,_⟩ => polyLift6_15 b
  | ⟨16,_⟩ => polyLift6_16 b
  | ⟨17,_⟩ => polyLift6_17 b
  | ⟨18,_⟩ => polyLift6_18 b
  | ⟨19,_⟩ => polyLift6_19 b
  | ⟨20,_⟩ => polyLift6_20 b
  | ⟨21,_⟩ => polyLift6_21 b
  | ⟨22,_⟩ => polyLift6_22 b
  | ⟨23,_⟩ => polyLift6_23 b
  | ⟨24,_⟩ => polyLift6_24 b
  | ⟨25,_⟩ => polyLift6_25 b
  | ⟨26,_⟩ => polyLift6_26 b
  | ⟨27,_⟩ => polyLift6_27 b
  | ⟨28,_⟩ => polyLift6_28 b
  | ⟨29,_⟩ => polyLift6_29 b
  | ⟨30,_⟩ => polyLift6_30 b
  | ⟨31,_⟩ => polyLift6_31 b
  | ⟨32,_⟩ => polyLift6_32 b
  | ⟨33,_⟩ => polyLift6_33 b
  | ⟨34,_⟩ => polyLift6_34 b
  | ⟨35,_⟩ => polyLift6_35 b
  | ⟨36,_⟩ => polyLift6_36 b
  | ⟨37,_⟩ => polyLift6_37 b
  | ⟨38,_⟩ => polyLift6_38 b
  | ⟨39,_⟩ => polyLift6_39 b
  | ⟨40,_⟩ => polyLift6_40 b
  | ⟨41,_⟩ => polyLift6_41 b
  | ⟨42,_⟩ => polyLift6_42 b
  | ⟨43,_⟩ => polyLift6_43 b
  | ⟨44,_⟩ => polyLift6_44 b
  | ⟨45,_⟩ => polyLift6_45 b
  | ⟨46,_⟩ => polyLift6_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree6 (j : Fin 47) (b : Fin 3) : (polyLiftRow6 j b).freeBlock=basisInt (homKind 6 j) b := by
  fin_cases j
  · exact polyLiftFree6_0 b
  · exact polyLiftFree6_1 b
  · exact polyLiftFree6_2 b
  · exact polyLiftFree6_3 b
  · exact polyLiftFree6_4 b
  · exact polyLiftFree6_5 b
  · exact polyLiftFree6_6 b
  · exact polyLiftFree6_7 b
  · exact polyLiftFree6_8 b
  · exact polyLiftFree6_9 b
  · exact polyLiftFree6_10 b
  · exact polyLiftFree6_11 b
  · exact polyLiftFree6_12 b
  · exact polyLiftFree6_13 b
  · exact polyLiftFree6_14 b
  · exact polyLiftFree6_15 b
  · exact polyLiftFree6_16 b
  · exact polyLiftFree6_17 b
  · exact polyLiftFree6_18 b
  · exact polyLiftFree6_19 b
  · exact polyLiftFree6_20 b
  · exact polyLiftFree6_21 b
  · exact polyLiftFree6_22 b
  · exact polyLiftFree6_23 b
  · exact polyLiftFree6_24 b
  · exact polyLiftFree6_25 b
  · exact polyLiftFree6_26 b
  · exact polyLiftFree6_27 b
  · exact polyLiftFree6_28 b
  · exact polyLiftFree6_29 b
  · exact polyLiftFree6_30 b
  · exact polyLiftFree6_31 b
  · exact polyLiftFree6_32 b
  · exact polyLiftFree6_33 b
  · exact polyLiftFree6_34 b
  · exact polyLiftFree6_35 b
  · exact polyLiftFree6_36 b
  · exact polyLiftFree6_37 b
  · exact polyLiftFree6_38 b
  · exact polyLiftFree6_39 b
  · exact polyLiftFree6_40 b
  · exact polyLiftFree6_41 b
  · exact polyLiftFree6_42 b
  · exact polyLiftFree6_43 b
  · exact polyLiftFree6_44 b
  · exact polyLiftFree6_45 b
  · exact polyLiftFree6_46 b
end UniserialComputations.N6
