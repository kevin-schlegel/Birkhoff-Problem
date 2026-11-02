import N6PolyHom
import N6HomTypes
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def polyLift12_0 (b : Fin 3) : PolyHom 12 0 :=
  ![PolyHom.zero 12 0,PolyHom.zero 12 0,PolyHom.zero 12 0] b
theorem polyLiftFree12_0 : ∀ b : Fin 3, (polyLift12_0 b).freeBlock=basisInt (homKind 12 0) b := by decide
def polyLift12_1 (b : Fin 3) : PolyHom 12 1 :=
  ![PolyHom.zero 12 1,PolyHom.zero 12 1,PolyHom.zero 12 1] b
theorem polyLiftFree12_1 : ∀ b : Fin 3, (polyLift12_1 b).freeBlock=basisInt (homKind 12 1) b := by decide
def polyLift12_2 (b : Fin 3) : PolyHom 12 2 :=
  ![PolyHom.zero 12 2,PolyHom.zero 12 2,PolyHom.zero 12 2] b
theorem polyLiftFree12_2 : ∀ b : Fin 3, (polyLift12_2 b).freeBlock=basisInt (homKind 12 2) b := by decide
def polyLift12_3 (b : Fin 3) : PolyHom 12 3 :=
  ![PolyHom.zero 12 3,PolyHom.zero 12 3,PolyHom.zero 12 3] b
theorem polyLiftFree12_3 : ∀ b : Fin 3, (polyLift12_3 b).freeBlock=basisInt (homKind 12 3) b := by decide
def polyLift12_4 (b : Fin 3) : PolyHom 12 4 :=
  ![PolyHom.zero 12 4,PolyHom.zero 12 4,PolyHom.zero 12 4] b
theorem polyLiftFree12_4 : ∀ b : Fin 3, (polyLift12_4 b).freeBlock=basisInt (homKind 12 4) b := by decide
def polyLift12_5 (b : Fin 3) : PolyHom 12 5 :=
  ![PolyHom.zero 12 5,PolyHom.zero 12 5,PolyHom.zero 12 5] b
theorem polyLiftFree12_5 : ∀ b : Fin 3, (polyLift12_5 b).freeBlock=basisInt (homKind 12 5) b := by decide
def polyLift12_6 (b : Fin 3) : PolyHom 12 6 :=
  ![PolyHom.zero 12 6,PolyHom.zero 12 6,PolyHom.zero 12 6] b
theorem polyLiftFree12_6 : ∀ b : Fin 3, (polyLift12_6 b).freeBlock=basisInt (homKind 12 6) b := by decide
def polyLift12_7 (b : Fin 3) : PolyHom 12 7 :=
  ![PolyHom.zero 12 7,PolyHom.zero 12 7,PolyHom.zero 12 7] b
theorem polyLiftFree12_7 : ∀ b : Fin 3, (polyLift12_7 b).freeBlock=basisInt (homKind 12 7) b := by decide
def polyLift12_8 (b : Fin 3) : PolyHom 12 8 :=
  ![PolyHom.zero 12 8,PolyHom.zero 12 8,PolyHom.zero 12 8] b
theorem polyLiftFree12_8 : ∀ b : Fin 3, (polyLift12_8 b).freeBlock=basisInt (homKind 12 8) b := by decide
def polyLift12_9 (b : Fin 3) : PolyHom 12 9 :=
  ![PolyHom.zero 12 9,PolyHom.zero 12 9,PolyHom.zero 12 9] b
theorem polyLiftFree12_9 : ∀ b : Fin 3, (polyLift12_9 b).freeBlock=basisInt (homKind 12 9) b := by decide
def polyRep12_10_0 : PolyHom 12 10 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 2),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift12_10 (b : Fin 3) : PolyHom 12 10 :=
  ![polyRep12_10_0,PolyHom.zero 12 10,PolyHom.zero 12 10] b
theorem polyLiftFree12_10 : ∀ b : Fin 3, (polyLift12_10 b).freeBlock=basisInt (homKind 12 10) b := by decide
def polyRep12_11_0 : PolyHom 12 11 where
  M := !![(mono6 (1) 1),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift12_11 (b : Fin 3) : PolyHom 12 11 :=
  ![polyRep12_11_0,PolyHom.zero 12 11,PolyHom.zero 12 11] b
theorem polyLiftFree12_11 : ∀ b : Fin 3, (polyLift12_11 b).freeBlock=basisInt (homKind 12 11) b := by decide
def polyRep12_12_0 : PolyHom 12 12 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 0),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift12_12 (b : Fin 3) : PolyHom 12 12 :=
  ![polyRep12_12_0,PolyHom.zero 12 12,PolyHom.zero 12 12] b
theorem polyLiftFree12_12 : ∀ b : Fin 3, (polyLift12_12 b).freeBlock=basisInt (homKind 12 12) b := by decide
def polyLift12_13 (b : Fin 3) : PolyHom 12 13 :=
  ![PolyHom.zero 12 13,PolyHom.zero 12 13,PolyHom.zero 12 13] b
theorem polyLiftFree12_13 : ∀ b : Fin 3, (polyLift12_13 b).freeBlock=basisInt (homKind 12 13) b := by decide
def polyLift12_14 (b : Fin 3) : PolyHom 12 14 :=
  ![PolyHom.zero 12 14,PolyHom.zero 12 14,PolyHom.zero 12 14] b
theorem polyLiftFree12_14 : ∀ b : Fin 3, (polyLift12_14 b).freeBlock=basisInt (homKind 12 14) b := by decide
def polyLift12_15 (b : Fin 3) : PolyHom 12 15 :=
  ![PolyHom.zero 12 15,PolyHom.zero 12 15,PolyHom.zero 12 15] b
theorem polyLiftFree12_15 : ∀ b : Fin 3, (polyLift12_15 b).freeBlock=basisInt (homKind 12 15) b := by decide
def polyLift12_16 (b : Fin 3) : PolyHom 12 16 :=
  ![PolyHom.zero 12 16,PolyHom.zero 12 16,PolyHom.zero 12 16] b
theorem polyLiftFree12_16 : ∀ b : Fin 3, (polyLift12_16 b).freeBlock=basisInt (homKind 12 16) b := by decide
def polyLift12_17 (b : Fin 3) : PolyHom 12 17 :=
  ![PolyHom.zero 12 17,PolyHom.zero 12 17,PolyHom.zero 12 17] b
theorem polyLiftFree12_17 : ∀ b : Fin 3, (polyLift12_17 b).freeBlock=basisInt (homKind 12 17) b := by decide
def polyLift12_18 (b : Fin 3) : PolyHom 12 18 :=
  ![PolyHom.zero 12 18,PolyHom.zero 12 18,PolyHom.zero 12 18] b
theorem polyLiftFree12_18 : ∀ b : Fin 3, (polyLift12_18 b).freeBlock=basisInt (homKind 12 18) b := by decide
def polyLift12_19 (b : Fin 3) : PolyHom 12 19 :=
  ![PolyHom.zero 12 19,PolyHom.zero 12 19,PolyHom.zero 12 19] b
theorem polyLiftFree12_19 : ∀ b : Fin 3, (polyLift12_19 b).freeBlock=basisInt (homKind 12 19) b := by decide
def polyLift12_20 (b : Fin 3) : PolyHom 12 20 :=
  ![PolyHom.zero 12 20,PolyHom.zero 12 20,PolyHom.zero 12 20] b
theorem polyLiftFree12_20 : ∀ b : Fin 3, (polyLift12_20 b).freeBlock=basisInt (homKind 12 20) b := by decide
def polyRep12_21_0 : PolyHom 12 21 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),0,0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift12_21 (b : Fin 3) : PolyHom 12 21 :=
  ![polyRep12_21_0,PolyHom.zero 12 21,PolyHom.zero 12 21] b
theorem polyLiftFree12_21 : ∀ b : Fin 3, (polyLift12_21 b).freeBlock=basisInt (homKind 12 21) b := by decide
def polyLift12_22 (b : Fin 3) : PolyHom 12 22 :=
  ![PolyHom.zero 12 22,PolyHom.zero 12 22,PolyHom.zero 12 22] b
theorem polyLiftFree12_22 : ∀ b : Fin 3, (polyLift12_22 b).freeBlock=basisInt (homKind 12 22) b := by decide
def polyLift12_23 (b : Fin 3) : PolyHom 12 23 :=
  ![PolyHom.zero 12 23,PolyHom.zero 12 23,PolyHom.zero 12 23] b
theorem polyLiftFree12_23 : ∀ b : Fin 3, (polyLift12_23 b).freeBlock=basisInt (homKind 12 23) b := by decide
def polyRep12_24_0 : PolyHom 12 24 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),(mono6 (1) 2),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift12_24 (b : Fin 3) : PolyHom 12 24 :=
  ![polyRep12_24_0,PolyHom.zero 12 24,PolyHom.zero 12 24] b
theorem polyLiftFree12_24 : ∀ b : Fin 3, (polyLift12_24 b).freeBlock=basisInt (homKind 12 24) b := by decide
def polyLift12_25 (b : Fin 3) : PolyHom 12 25 :=
  ![PolyHom.zero 12 25,PolyHom.zero 12 25,PolyHom.zero 12 25] b
theorem polyLiftFree12_25 : ∀ b : Fin 3, (polyLift12_25 b).freeBlock=basisInt (homKind 12 25) b := by decide
def polyLift12_26 (b : Fin 3) : PolyHom 12 26 :=
  ![PolyHom.zero 12 26,PolyHom.zero 12 26,PolyHom.zero 12 26] b
theorem polyLiftFree12_26 : ∀ b : Fin 3, (polyLift12_26 b).freeBlock=basisInt (homKind 12 26) b := by decide
def polyLift12_27 (b : Fin 3) : PolyHom 12 27 :=
  ![PolyHom.zero 12 27,PolyHom.zero 12 27,PolyHom.zero 12 27] b
theorem polyLiftFree12_27 : ∀ b : Fin 3, (polyLift12_27 b).freeBlock=basisInt (homKind 12 27) b := by decide
def polyLift12_28 (b : Fin 3) : PolyHom 12 28 :=
  ![PolyHom.zero 12 28,PolyHom.zero 12 28,PolyHom.zero 12 28] b
theorem polyLiftFree12_28 : ∀ b : Fin 3, (polyLift12_28 b).freeBlock=basisInt (homKind 12 28) b := by decide
def polyLift12_29 (b : Fin 3) : PolyHom 12 29 :=
  ![PolyHom.zero 12 29,PolyHom.zero 12 29,PolyHom.zero 12 29] b
theorem polyLiftFree12_29 : ∀ b : Fin 3, (polyLift12_29 b).freeBlock=basisInt (homKind 12 29) b := by decide
def polyRep12_30_0 : PolyHom 12 30 where
  M := !![(mono6 (1) 0),0,0,0;0,(mono6 (1) 0),(mono6 (1) 1),0;0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift12_30 (b : Fin 3) : PolyHom 12 30 :=
  ![polyRep12_30_0,PolyHom.zero 12 30,PolyHom.zero 12 30] b
theorem polyLiftFree12_30 : ∀ b : Fin 3, (polyLift12_30 b).freeBlock=basisInt (homKind 12 30) b := by decide
def polyLift12_31 (b : Fin 3) : PolyHom 12 31 :=
  ![PolyHom.zero 12 31,PolyHom.zero 12 31,PolyHom.zero 12 31] b
theorem polyLiftFree12_31 : ∀ b : Fin 3, (polyLift12_31 b).freeBlock=basisInt (homKind 12 31) b := by decide
def polyLift12_32 (b : Fin 3) : PolyHom 12 32 :=
  ![PolyHom.zero 12 32,PolyHom.zero 12 32,PolyHom.zero 12 32] b
theorem polyLiftFree12_32 : ∀ b : Fin 3, (polyLift12_32 b).freeBlock=basisInt (homKind 12 32) b := by decide
def polyLift12_33 (b : Fin 3) : PolyHom 12 33 :=
  ![PolyHom.zero 12 33,PolyHom.zero 12 33,PolyHom.zero 12 33] b
theorem polyLiftFree12_33 : ∀ b : Fin 3, (polyLift12_33 b).freeBlock=basisInt (homKind 12 33) b := by decide
def polyLift12_34 (b : Fin 3) : PolyHom 12 34 :=
  ![PolyHom.zero 12 34,PolyHom.zero 12 34,PolyHom.zero 12 34] b
theorem polyLiftFree12_34 : ∀ b : Fin 3, (polyLift12_34 b).freeBlock=basisInt (homKind 12 34) b := by decide
def polyLift12_35 (b : Fin 3) : PolyHom 12 35 :=
  ![PolyHom.zero 12 35,PolyHom.zero 12 35,PolyHom.zero 12 35] b
theorem polyLiftFree12_35 : ∀ b : Fin 3, (polyLift12_35 b).freeBlock=basisInt (homKind 12 35) b := by decide
def polyLift12_36 (b : Fin 3) : PolyHom 12 36 :=
  ![PolyHom.zero 12 36,PolyHom.zero 12 36,PolyHom.zero 12 36] b
theorem polyLiftFree12_36 : ∀ b : Fin 3, (polyLift12_36 b).freeBlock=basisInt (homKind 12 36) b := by decide
def polyLift12_37 (b : Fin 3) : PolyHom 12 37 :=
  ![PolyHom.zero 12 37,PolyHom.zero 12 37,PolyHom.zero 12 37] b
theorem polyLiftFree12_37 : ∀ b : Fin 3, (polyLift12_37 b).freeBlock=basisInt (homKind 12 37) b := by decide
def polyLift12_38 (b : Fin 3) : PolyHom 12 38 :=
  ![PolyHom.zero 12 38,PolyHom.zero 12 38,PolyHom.zero 12 38] b
theorem polyLiftFree12_38 : ∀ b : Fin 3, (polyLift12_38 b).freeBlock=basisInt (homKind 12 38) b := by decide
def polyLift12_39 (b : Fin 3) : PolyHom 12 39 :=
  ![PolyHom.zero 12 39,PolyHom.zero 12 39,PolyHom.zero 12 39] b
theorem polyLiftFree12_39 : ∀ b : Fin 3, (polyLift12_39 b).freeBlock=basisInt (homKind 12 39) b := by decide
def polyLift12_40 (b : Fin 3) : PolyHom 12 40 :=
  ![PolyHom.zero 12 40,PolyHom.zero 12 40,PolyHom.zero 12 40] b
theorem polyLiftFree12_40 : ∀ b : Fin 3, (polyLift12_40 b).freeBlock=basisInt (homKind 12 40) b := by decide
def polyLift12_41 (b : Fin 3) : PolyHom 12 41 :=
  ![PolyHom.zero 12 41,PolyHom.zero 12 41,PolyHom.zero 12 41] b
theorem polyLiftFree12_41 : ∀ b : Fin 3, (polyLift12_41 b).freeBlock=basisInt (homKind 12 41) b := by decide
def polyRep12_42_0 : PolyHom 12 42 where
  M := !![0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),(mono6 (-1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (-1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift12_42 (b : Fin 3) : PolyHom 12 42 :=
  ![polyRep12_42_0,PolyHom.zero 12 42,PolyHom.zero 12 42] b
theorem polyLiftFree12_42 : ∀ b : Fin 3, (polyLift12_42 b).freeBlock=basisInt (homKind 12 42) b := by decide
def polyLift12_43 (b : Fin 3) : PolyHom 12 43 :=
  ![PolyHom.zero 12 43,PolyHom.zero 12 43,PolyHom.zero 12 43] b
theorem polyLiftFree12_43 : ∀ b : Fin 3, (polyLift12_43 b).freeBlock=basisInt (homKind 12 43) b := by decide
def polyRep12_44_0 : PolyHom 12 44 where
  M := !![0,(mono6 (1) 0),0,0;0,0,(mono6 (1) 0),(mono6 (-1) 1);0,0,0,0;0,0,0,0]
  U := !![(mono6 (1) 1),(mono6 (-1) 0);0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift12_44 (b : Fin 3) : PolyHom 12 44 :=
  ![polyRep12_44_0,PolyHom.zero 12 44,PolyHom.zero 12 44] b
theorem polyLiftFree12_44 : ∀ b : Fin 3, (polyLift12_44 b).freeBlock=basisInt (homKind 12 44) b := by decide
def polyRep12_45_0 : PolyHom 12 45 where
  M := !![0,0,0,0;(mono6 (1) 0),0,0,0;0,0,0,0;0,0,0,0]
  U := !![0,0;0,0]
  ambient_descent := by decide
  source_descent := by decide
  commutes := by decide
def polyLift12_45 (b : Fin 3) : PolyHom 12 45 :=
  ![polyRep12_45_0,PolyHom.zero 12 45,PolyHom.zero 12 45] b
theorem polyLiftFree12_45 : ∀ b : Fin 3, (polyLift12_45 b).freeBlock=basisInt (homKind 12 45) b := by decide
def polyLift12_46 (b : Fin 3) : PolyHom 12 46 :=
  ![PolyHom.zero 12 46,PolyHom.zero 12 46,PolyHom.zero 12 46] b
theorem polyLiftFree12_46 : ∀ b : Fin 3, (polyLift12_46 b).freeBlock=basisInt (homKind 12 46) b := by decide
def polyLiftRow12 (j : Fin 47) (b : Fin 3) : PolyHom 12 j :=
  match j with
  | ⟨0,_⟩ => polyLift12_0 b
  | ⟨1,_⟩ => polyLift12_1 b
  | ⟨2,_⟩ => polyLift12_2 b
  | ⟨3,_⟩ => polyLift12_3 b
  | ⟨4,_⟩ => polyLift12_4 b
  | ⟨5,_⟩ => polyLift12_5 b
  | ⟨6,_⟩ => polyLift12_6 b
  | ⟨7,_⟩ => polyLift12_7 b
  | ⟨8,_⟩ => polyLift12_8 b
  | ⟨9,_⟩ => polyLift12_9 b
  | ⟨10,_⟩ => polyLift12_10 b
  | ⟨11,_⟩ => polyLift12_11 b
  | ⟨12,_⟩ => polyLift12_12 b
  | ⟨13,_⟩ => polyLift12_13 b
  | ⟨14,_⟩ => polyLift12_14 b
  | ⟨15,_⟩ => polyLift12_15 b
  | ⟨16,_⟩ => polyLift12_16 b
  | ⟨17,_⟩ => polyLift12_17 b
  | ⟨18,_⟩ => polyLift12_18 b
  | ⟨19,_⟩ => polyLift12_19 b
  | ⟨20,_⟩ => polyLift12_20 b
  | ⟨21,_⟩ => polyLift12_21 b
  | ⟨22,_⟩ => polyLift12_22 b
  | ⟨23,_⟩ => polyLift12_23 b
  | ⟨24,_⟩ => polyLift12_24 b
  | ⟨25,_⟩ => polyLift12_25 b
  | ⟨26,_⟩ => polyLift12_26 b
  | ⟨27,_⟩ => polyLift12_27 b
  | ⟨28,_⟩ => polyLift12_28 b
  | ⟨29,_⟩ => polyLift12_29 b
  | ⟨30,_⟩ => polyLift12_30 b
  | ⟨31,_⟩ => polyLift12_31 b
  | ⟨32,_⟩ => polyLift12_32 b
  | ⟨33,_⟩ => polyLift12_33 b
  | ⟨34,_⟩ => polyLift12_34 b
  | ⟨35,_⟩ => polyLift12_35 b
  | ⟨36,_⟩ => polyLift12_36 b
  | ⟨37,_⟩ => polyLift12_37 b
  | ⟨38,_⟩ => polyLift12_38 b
  | ⟨39,_⟩ => polyLift12_39 b
  | ⟨40,_⟩ => polyLift12_40 b
  | ⟨41,_⟩ => polyLift12_41 b
  | ⟨42,_⟩ => polyLift12_42 b
  | ⟨43,_⟩ => polyLift12_43 b
  | ⟨44,_⟩ => polyLift12_44 b
  | ⟨45,_⟩ => polyLift12_45 b
  | ⟨46,_⟩ => polyLift12_46 b
  | ⟨n+47,h⟩ => False.elim (by omega)
theorem polyLiftRowFree12 (j : Fin 47) (b : Fin 3) : (polyLiftRow12 j b).freeBlock=basisInt (homKind 12 j) b := by
  fin_cases j
  · exact polyLiftFree12_0 b
  · exact polyLiftFree12_1 b
  · exact polyLiftFree12_2 b
  · exact polyLiftFree12_3 b
  · exact polyLiftFree12_4 b
  · exact polyLiftFree12_5 b
  · exact polyLiftFree12_6 b
  · exact polyLiftFree12_7 b
  · exact polyLiftFree12_8 b
  · exact polyLiftFree12_9 b
  · exact polyLiftFree12_10 b
  · exact polyLiftFree12_11 b
  · exact polyLiftFree12_12 b
  · exact polyLiftFree12_13 b
  · exact polyLiftFree12_14 b
  · exact polyLiftFree12_15 b
  · exact polyLiftFree12_16 b
  · exact polyLiftFree12_17 b
  · exact polyLiftFree12_18 b
  · exact polyLiftFree12_19 b
  · exact polyLiftFree12_20 b
  · exact polyLiftFree12_21 b
  · exact polyLiftFree12_22 b
  · exact polyLiftFree12_23 b
  · exact polyLiftFree12_24 b
  · exact polyLiftFree12_25 b
  · exact polyLiftFree12_26 b
  · exact polyLiftFree12_27 b
  · exact polyLiftFree12_28 b
  · exact polyLiftFree12_29 b
  · exact polyLiftFree12_30 b
  · exact polyLiftFree12_31 b
  · exact polyLiftFree12_32 b
  · exact polyLiftFree12_33 b
  · exact polyLiftFree12_34 b
  · exact polyLiftFree12_35 b
  · exact polyLiftFree12_36 b
  · exact polyLiftFree12_37 b
  · exact polyLiftFree12_38 b
  · exact polyLiftFree12_39 b
  · exact polyLiftFree12_40 b
  · exact polyLiftFree12_41 b
  · exact polyLiftFree12_42 b
  · exact polyLiftFree12_43 b
  · exact polyLiftFree12_44 b
  · exact polyLiftFree12_45 b
  · exact polyLiftFree12_46 b
end UniserialComputations.N6
