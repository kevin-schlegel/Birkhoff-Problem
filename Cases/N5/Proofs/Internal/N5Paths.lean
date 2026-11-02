import N5Quiver
noncomputable section
namespace UniserialComputations.N5
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxRecDepth 10000
def normalWord (i j : Fin 19) : List (Fin 23) :=
  match i.val,j.val with
  | 1,0 => [0]
  | 6,0 => [0, 1]
  | 9,0 => [0, 1, 5]
  | 17,0 => [0, 1, 5, 8]
  | 10,0 => [0, 1, 5, 8, 21]
  | 13,0 => [0, 1, 5, 8, 22]
  | 16,0 => [0, 1, 5, 8, 21, 9]
  | 2,0 => [0, 1, 5, 8, 22, 13]
  | 7,0 => [0, 1, 5, 8, 21, 9, 18]
  | 14,0 => [0, 1, 5, 8, 21, 9, 19]
  | 11,0 => [0, 1, 5, 8, 21, 9, 18, 6]
  | 15,0 => [0, 1, 5, 8, 21, 9, 19, 16]
  | 3,0 => [0, 1, 5, 8, 21, 9, 18, 6, 10]
  | 12,0 => [0, 1, 5, 8, 21, 9, 18, 6, 11]
  | 18,0 => [0, 1, 5, 8, 21, 9, 18, 6, 10, 3]
  | 8,0 => [0, 1, 5, 8, 21, 9, 18, 6, 10, 3, 20]
  | 4,0 => [0, 1, 5, 8, 21, 9, 18, 6, 10, 3, 20, 7]
  | 5,0 => [0, 1, 5, 8, 21, 9, 18, 6, 10, 3, 20, 7, 4]
  | 6,1 => [1]
  | 9,1 => [1, 5]
  | 17,1 => [1, 5, 8]
  | 10,1 => [1, 5, 8, 21]
  | 13,1 => [1, 5, 8, 22]
  | 16,1 => [1, 5, 8, 21, 9]
  | 2,1 => [1, 5, 8, 22, 13]
  | 7,1 => [1, 5, 8, 21, 9, 18]
  | 14,1 => [1, 5, 8, 21, 9, 19]
  | 11,1 => [1, 5, 8, 21, 9, 18, 6]
  | 15,1 => [1, 5, 8, 21, 9, 19, 16]
  | 3,1 => [1, 5, 8, 21, 9, 18, 6, 10]
  | 12,1 => [1, 5, 8, 21, 9, 18, 6, 11]
  | 18,1 => [1, 5, 8, 21, 9, 18, 6, 10, 3]
  | 8,1 => [1, 5, 8, 21, 9, 18, 6, 10, 3, 20]
  | 4,1 => [1, 5, 8, 21, 9, 18, 6, 10, 3, 20, 7]
  | 5,1 => [1, 5, 8, 21, 9, 18, 6, 10, 3, 20, 7, 4]
  | 7,2 => [2]
  | 11,2 => [2, 6]
  | 3,2 => [2, 6, 10]
  | 12,2 => [2, 6, 11]
  | 18,2 => [2, 6, 10, 3]
  | 8,2 => [2, 6, 10, 3, 20]
  | 4,2 => [2, 6, 10, 3, 20, 7]
  | 5,2 => [2, 6, 10, 3, 20, 7, 4]
  | 18,3 => [3]
  | 8,3 => [3, 20]
  | 4,3 => [3, 20, 7]
  | 5,3 => [3, 20, 7, 4]
  | 5,4 => [4]
  | 9,6 => [5]
  | 17,6 => [5, 8]
  | 10,6 => [5, 8, 21]
  | 13,6 => [5, 8, 22]
  | 16,6 => [5, 8, 21, 9]
  | 2,6 => [5, 8, 22, 13]
  | 7,6 => [5, 8, 21, 9, 18]
  | 14,6 => [5, 8, 21, 9, 19]
  | 11,6 => [5, 8, 21, 9, 18, 6]
  | 15,6 => [5, 8, 21, 9, 19, 16]
  | 3,6 => [5, 8, 21, 9, 18, 6, 10]
  | 12,6 => [5, 8, 21, 9, 18, 6, 11]
  | 18,6 => [5, 8, 21, 9, 18, 6, 10, 3]
  | 8,6 => [5, 8, 21, 9, 18, 6, 10, 3, 20]
  | 4,6 => [5, 8, 21, 9, 18, 6, 10, 3, 20, 7]
  | 5,6 => [5, 8, 21, 9, 18, 6, 10, 3, 20, 7, 4]
  | 11,7 => [6]
  | 3,7 => [6, 10]
  | 12,7 => [6, 11]
  | 18,7 => [6, 10, 3]
  | 8,7 => [6, 10, 3, 20]
  | 4,7 => [6, 10, 3, 20, 7]
  | 5,7 => [6, 10, 3, 20, 7, 4]
  | 4,8 => [7]
  | 5,8 => [7, 4]
  | 17,9 => [8]
  | 10,9 => [8, 21]
  | 13,9 => [8, 22]
  | 16,9 => [8, 21, 9]
  | 2,9 => [8, 22, 13]
  | 7,9 => [8, 21, 9, 18]
  | 14,9 => [8, 21, 9, 19]
  | 11,9 => [8, 21, 9, 18, 6]
  | 15,9 => [8, 21, 9, 19, 16]
  | 3,9 => [8, 21, 9, 18, 6, 10]
  | 12,9 => [8, 21, 9, 18, 6, 11]
  | 18,9 => [8, 21, 9, 18, 6, 10, 3]
  | 8,9 => [8, 21, 9, 18, 6, 10, 3, 20]
  | 4,9 => [8, 21, 9, 18, 6, 10, 3, 20, 7]
  | 5,9 => [8, 21, 9, 18, 6, 10, 3, 20, 7, 4]
  | 16,10 => [9]
  | 7,10 => [9, 18]
  | 14,10 => [9, 19]
  | 11,10 => [9, 18, 6]
  | 15,10 => [9, 19, 16]
  | 3,10 => [9, 18, 6, 10]
  | 12,10 => [9, 18, 6, 11]
  | 18,10 => [9, 18, 6, 10, 3]
  | 8,10 => [9, 18, 6, 10, 3, 20]
  | 4,10 => [9, 18, 6, 10, 3, 20, 7]
  | 5,10 => [9, 18, 6, 10, 3, 20, 7, 4]
  | 3,11 => [10]
  | 12,11 => [11]
  | 18,11 => [10, 3]
  | 8,11 => [10, 3, 20]
  | 4,11 => [10, 3, 20, 7]
  | 5,11 => [10, 3, 20, 7, 4]
  | 18,12 => [12]
  | 8,12 => [12, 20]
  | 4,12 => [12, 20, 7]
  | 5,12 => [12, 20, 7, 4]
  | 2,13 => [13]
  | 16,13 => [14]
  | 7,13 => [13, 2]
  | 14,13 => [14, 19]
  | 11,13 => [13, 2, 6]
  | 15,13 => [14, 19, 16]
  | 3,13 => [13, 2, 6, 10]
  | 12,13 => [13, 2, 6, 11]
  | 18,13 => [13, 2, 6, 10, 3]
  | 8,13 => [13, 2, 6, 10, 3, 20]
  | 4,13 => [13, 2, 6, 10, 3, 20, 7]
  | 5,13 => [13, 2, 6, 10, 3, 20, 7, 4]
  | 11,14 => [15]
  | 15,14 => [16]
  | 3,14 => [15, 10]
  | 12,14 => [15, 11]
  | 18,14 => [15, 10, 3]
  | 8,14 => [15, 10, 3, 20]
  | 4,14 => [15, 10, 3, 20, 7]
  | 5,14 => [15, 10, 3, 20, 7, 4]
  | 12,15 => [17]
  | 18,15 => [17, 12]
  | 8,15 => [17, 12, 20]
  | 4,15 => [17, 12, 20, 7]
  | 5,15 => [17, 12, 20, 7, 4]
  | 7,16 => [18]
  | 14,16 => [19]
  | 11,16 => [18, 6]
  | 15,16 => [19, 16]
  | 3,16 => [18, 6, 10]
  | 12,16 => [18, 6, 11]
  | 18,16 => [18, 6, 10, 3]
  | 8,16 => [18, 6, 10, 3, 20]
  | 4,16 => [18, 6, 10, 3, 20, 7]
  | 5,16 => [18, 6, 10, 3, 20, 7, 4]
  | 8,18 => [20]
  | 10,17 => [21]
  | 13,17 => [22]
  | 4,18 => [20, 7]
  | 16,17 => [21, 9]
  | 2,17 => [22, 13]
  | 5,18 => [20, 7, 4]
  | 7,17 => [21, 9, 18]
  | 14,17 => [21, 9, 19]
  | 11,17 => [21, 9, 18, 6]
  | 15,17 => [21, 9, 19, 16]
  | 3,17 => [21, 9, 18, 6, 10]
  | 12,17 => [21, 9, 18, 6, 11]
  | 18,17 => [21, 9, 18, 6, 10, 3]
  | 8,17 => [21, 9, 18, 6, 10, 3, 20]
  | 4,17 => [21, 9, 18, 6, 10, 3, 20, 7]
  | 5,17 => [21, 9, 18, 6, 10, 3, 20, 7, 4]
  | _,_ => []
variable (k : Type*) [Field k]
def wordValue {A : Type*} [Monoid A] (a : Fin 23 → A) (p : List (Fin 23)) : A := (p.reverse.map a).prod
def representative (c : Coord) : PathAlgebra k :=
  if c.val.1=c.val.2 then pathVertex k (slotVertex c.val.1) else wordValue (pathArrow k) (normalWord c.val.1 c.val.2)
def basisMatrix (c : Coord) : Mat k := Matrix.single c.val.1 c.val.2 1 +
  if c.val=(17,17) then Matrix.single 18 18 1 else 0

theorem image_0_0 : (pathMap k (representative k ⟨(0,0),by decide⟩)).val=basisMatrix k ⟨(0,0),by decide⟩ := by
  change (vertex k 0).val = Matrix.single 0 0 1+0
  ext r c
  fin_cases r <;> fin_cases c <;> simp [vertex,Matrix.single_apply,Matrix.diagonal_apply,slotVertex]
theorem image_1_0 : (pathMap k (representative k ⟨(1,0),by decide⟩)).val=basisMatrix k ⟨(1,0),by decide⟩ := by
  change (pathMap k (pathArrow k 0*1)).val = Matrix.single 1 0 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 1 0 (1:k)*(1 : Mat k)) = Matrix.single 1 0 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_1_1 : (pathMap k (representative k ⟨(1,1),by decide⟩)).val=basisMatrix k ⟨(1,1),by decide⟩ := by
  change (vertex k 1).val = Matrix.single 1 1 1+0
  ext r c
  fin_cases r <;> fin_cases c <;> simp [vertex,Matrix.single_apply,Matrix.diagonal_apply,slotVertex]
theorem image_2_0 : (pathMap k (representative k ⟨(2,0),by decide⟩)).val=basisMatrix k ⟨(2,0),by decide⟩ := by
  change (pathMap k (pathArrow k 13*(pathArrow k 22*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*(pathArrow k 0*1))))))).val = Matrix.single 2 0 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 2 13 (1:k)*(Matrix.single 13 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(Matrix.single 1 0 (1:k)*(1 : Mat k))))))) = Matrix.single 2 0 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_2_1 : (pathMap k (representative k ⟨(2,1),by decide⟩)).val=basisMatrix k ⟨(2,1),by decide⟩ := by
  change (pathMap k (pathArrow k 13*(pathArrow k 22*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*1)))))).val = Matrix.single 2 1 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 2 13 (1:k)*(Matrix.single 13 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(1 : Mat k)))))) = Matrix.single 2 1 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_2_2 : (pathMap k (representative k ⟨(2,2),by decide⟩)).val=basisMatrix k ⟨(2,2),by decide⟩ := by
  change (vertex k 2).val = Matrix.single 2 2 1+0
  ext r c
  fin_cases r <;> fin_cases c <;> simp [vertex,Matrix.single_apply,Matrix.diagonal_apply,slotVertex]
theorem image_2_6 : (pathMap k (representative k ⟨(2,6),by decide⟩)).val=basisMatrix k ⟨(2,6),by decide⟩ := by
  change (pathMap k (pathArrow k 13*(pathArrow k 22*(pathArrow k 8*(pathArrow k 5*1))))).val = Matrix.single 2 6 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 2 13 (1:k)*(Matrix.single 13 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(1 : Mat k))))) = Matrix.single 2 6 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_2_9 : (pathMap k (representative k ⟨(2,9),by decide⟩)).val=basisMatrix k ⟨(2,9),by decide⟩ := by
  change (pathMap k (pathArrow k 13*(pathArrow k 22*(pathArrow k 8*1)))).val = Matrix.single 2 9 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 2 13 (1:k)*(Matrix.single 13 17 (1:k)*(Matrix.single 17 9 (1:k)*(1 : Mat k)))) = Matrix.single 2 9 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_2_13 : (pathMap k (representative k ⟨(2,13),by decide⟩)).val=basisMatrix k ⟨(2,13),by decide⟩ := by
  change (pathMap k (pathArrow k 13*1)).val = Matrix.single 2 13 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 2 13 (1:k)*(1 : Mat k)) = Matrix.single 2 13 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_2_17 : (pathMap k (representative k ⟨(2,17),by decide⟩)).val=basisMatrix k ⟨(2,17),by decide⟩ := by
  change (pathMap k (pathArrow k 13*(pathArrow k 22*1))).val = Matrix.single 2 17 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 2 13 (1:k)*(Matrix.single 13 17 (1:k)*(1 : Mat k))) = Matrix.single 2 17 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_3_0 : (pathMap k (representative k ⟨(3,0),by decide⟩)).val=basisMatrix k ⟨(3,0),by decide⟩ := by
  change (pathMap k (pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*(pathArrow k 0*1)))))))))).val = Matrix.single 3 0 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(Matrix.single 1 0 (1:k)*(1 : Mat k)))))))))) = Matrix.single 3 0 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_3_1 : (pathMap k (representative k ⟨(3,1),by decide⟩)).val=basisMatrix k ⟨(3,1),by decide⟩ := by
  change (pathMap k (pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*1))))))))).val = Matrix.single 3 1 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(1 : Mat k))))))))) = Matrix.single 3 1 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_3_2 : (pathMap k (representative k ⟨(3,2),by decide⟩)).val=basisMatrix k ⟨(3,2),by decide⟩ := by
  change (pathMap k (pathArrow k 10*(pathArrow k 6*(pathArrow k 2*1)))).val = Matrix.single 3 2 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 2 (1:k)*(1 : Mat k)))) = Matrix.single 3 2 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_3_3 : (pathMap k (representative k ⟨(3,3),by decide⟩)).val=basisMatrix k ⟨(3,3),by decide⟩ := by
  change (vertex k 3).val = Matrix.single 3 3 1+0
  ext r c
  fin_cases r <;> fin_cases c <;> simp [vertex,Matrix.single_apply,Matrix.diagonal_apply,slotVertex]
theorem image_3_6 : (pathMap k (representative k ⟨(3,6),by decide⟩)).val=basisMatrix k ⟨(3,6),by decide⟩ := by
  change (pathMap k (pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*1)))))))).val = Matrix.single 3 6 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(1 : Mat k)))))))) = Matrix.single 3 6 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_3_7 : (pathMap k (representative k ⟨(3,7),by decide⟩)).val=basisMatrix k ⟨(3,7),by decide⟩ := by
  change (pathMap k (pathArrow k 10*(pathArrow k 6*1))).val = Matrix.single 3 7 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(1 : Mat k))) = Matrix.single 3 7 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_3_9 : (pathMap k (representative k ⟨(3,9),by decide⟩)).val=basisMatrix k ⟨(3,9),by decide⟩ := by
  change (pathMap k (pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*1))))))).val = Matrix.single 3 9 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(1 : Mat k))))))) = Matrix.single 3 9 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_3_10 : (pathMap k (representative k ⟨(3,10),by decide⟩)).val=basisMatrix k ⟨(3,10),by decide⟩ := by
  change (pathMap k (pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*1))))).val = Matrix.single 3 10 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(1 : Mat k))))) = Matrix.single 3 10 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_3_11 : (pathMap k (representative k ⟨(3,11),by decide⟩)).val=basisMatrix k ⟨(3,11),by decide⟩ := by
  change (pathMap k (pathArrow k 10*1)).val = Matrix.single 3 11 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 3 11 (1:k)*(1 : Mat k)) = Matrix.single 3 11 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_3_13 : (pathMap k (representative k ⟨(3,13),by decide⟩)).val=basisMatrix k ⟨(3,13),by decide⟩ := by
  change (pathMap k (pathArrow k 10*(pathArrow k 6*(pathArrow k 2*(pathArrow k 13*1))))).val = Matrix.single 3 13 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 2 (1:k)*(Matrix.single 2 13 (1:k)*(1 : Mat k))))) = Matrix.single 3 13 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_3_14 : (pathMap k (representative k ⟨(3,14),by decide⟩)).val=basisMatrix k ⟨(3,14),by decide⟩ := by
  change (pathMap k (pathArrow k 10*(pathArrow k 15*1))).val = Matrix.single 3 14 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 3 11 (1:k)*(Matrix.single 11 14 (1:k)*(1 : Mat k))) = Matrix.single 3 14 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_3_16 : (pathMap k (representative k ⟨(3,16),by decide⟩)).val=basisMatrix k ⟨(3,16),by decide⟩ := by
  change (pathMap k (pathArrow k 10*(pathArrow k 6*(pathArrow k 18*1)))).val = Matrix.single 3 16 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(1 : Mat k)))) = Matrix.single 3 16 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_3_17 : (pathMap k (representative k ⟨(3,17),by decide⟩)).val=basisMatrix k ⟨(3,17),by decide⟩ := by
  change (pathMap k (pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*1)))))).val = Matrix.single 3 17 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(1 : Mat k)))))) = Matrix.single 3 17 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_4_0 : (pathMap k (representative k ⟨(4,0),by decide⟩)).val=basisMatrix k ⟨(4,0),by decide⟩ := by
  change (pathMap k (pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*(pathArrow k 0*1))))))))))))).val = Matrix.single 4 0 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(Matrix.single 1 0 (1:k)*(1 : Mat k))))))))))))) = Matrix.single 4 0 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_4_1 : (pathMap k (representative k ⟨(4,1),by decide⟩)).val=basisMatrix k ⟨(4,1),by decide⟩ := by
  change (pathMap k (pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*1)))))))))))).val = Matrix.single 4 1 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(1 : Mat k)))))))))))) = Matrix.single 4 1 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_4_2 : (pathMap k (representative k ⟨(4,2),by decide⟩)).val=basisMatrix k ⟨(4,2),by decide⟩ := by
  change (pathMap k (pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 2*1))))))).val = Matrix.single 4 2 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 2 (1:k)*(1 : Mat k))))))) = Matrix.single 4 2 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_4_3 : (pathMap k (representative k ⟨(4,3),by decide⟩)).val=basisMatrix k ⟨(4,3),by decide⟩ := by
  change (pathMap k (pathArrow k 7*(pathArrow k 20*(pathArrow k 3*1)))).val = Matrix.single 4 3 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(1 : Mat k)))) = Matrix.single 4 3 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_4_4 : (pathMap k (representative k ⟨(4,4),by decide⟩)).val=basisMatrix k ⟨(4,4),by decide⟩ := by
  change (vertex k 4).val = Matrix.single 4 4 1+0
  ext r c
  fin_cases r <;> fin_cases c <;> simp [vertex,Matrix.single_apply,Matrix.diagonal_apply,slotVertex]
theorem image_4_6 : (pathMap k (representative k ⟨(4,6),by decide⟩)).val=basisMatrix k ⟨(4,6),by decide⟩ := by
  change (pathMap k (pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*1))))))))))).val = Matrix.single 4 6 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(1 : Mat k))))))))))) = Matrix.single 4 6 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_4_7 : (pathMap k (representative k ⟨(4,7),by decide⟩)).val=basisMatrix k ⟨(4,7),by decide⟩ := by
  change (pathMap k (pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*1)))))).val = Matrix.single 4 7 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(1 : Mat k)))))) = Matrix.single 4 7 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_4_8 : (pathMap k (representative k ⟨(4,8),by decide⟩)).val=basisMatrix k ⟨(4,8),by decide⟩ := by
  change (pathMap k (pathArrow k 7*1)).val = Matrix.single 4 8 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 4 8 (1:k)*(1 : Mat k)) = Matrix.single 4 8 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_4_9 : (pathMap k (representative k ⟨(4,9),by decide⟩)).val=basisMatrix k ⟨(4,9),by decide⟩ := by
  change (pathMap k (pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*1)))))))))).val = Matrix.single 4 9 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(1 : Mat k)))))))))) = Matrix.single 4 9 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_4_10 : (pathMap k (representative k ⟨(4,10),by decide⟩)).val=basisMatrix k ⟨(4,10),by decide⟩ := by
  change (pathMap k (pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*1)))))))).val = Matrix.single 4 10 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(1 : Mat k)))))))) = Matrix.single 4 10 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_4_11 : (pathMap k (representative k ⟨(4,11),by decide⟩)).val=basisMatrix k ⟨(4,11),by decide⟩ := by
  change (pathMap k (pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*1))))).val = Matrix.single 4 11 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(1 : Mat k))))) = Matrix.single 4 11 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_4_12 : (pathMap k (representative k ⟨(4,12),by decide⟩)).val=basisMatrix k ⟨(4,12),by decide⟩ := by
  change (pathMap k (pathArrow k 7*(pathArrow k 20*(pathArrow k 12*1)))).val = Matrix.single 4 12 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 12 (1:k)*(1 : Mat k)))) = Matrix.single 4 12 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_4_13 : (pathMap k (representative k ⟨(4,13),by decide⟩)).val=basisMatrix k ⟨(4,13),by decide⟩ := by
  change (pathMap k (pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 2*(pathArrow k 13*1)))))))).val = Matrix.single 4 13 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 2 (1:k)*(Matrix.single 2 13 (1:k)*(1 : Mat k)))))))) = Matrix.single 4 13 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_4_14 : (pathMap k (representative k ⟨(4,14),by decide⟩)).val=basisMatrix k ⟨(4,14),by decide⟩ := by
  change (pathMap k (pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 15*1)))))).val = Matrix.single 4 14 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 14 (1:k)*(1 : Mat k)))))) = Matrix.single 4 14 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_4_15 : (pathMap k (representative k ⟨(4,15),by decide⟩)).val=basisMatrix k ⟨(4,15),by decide⟩ := by
  change (pathMap k (pathArrow k 7*(pathArrow k 20*(pathArrow k 12*(pathArrow k 17*1))))).val = Matrix.single 4 15 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 12 (1:k)*(Matrix.single 12 15 (1:k)*(1 : Mat k))))) = Matrix.single 4 15 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_4_16 : (pathMap k (representative k ⟨(4,16),by decide⟩)).val=basisMatrix k ⟨(4,16),by decide⟩ := by
  change (pathMap k (pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*1))))))).val = Matrix.single 4 16 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(1 : Mat k))))))) = Matrix.single 4 16 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_4_17 : (pathMap k (representative k ⟨(4,17),by decide⟩)).val=basisMatrix k ⟨(4,17),by decide⟩ := by
  change (pathMap k (pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*1))))))))).val = Matrix.single 4 17 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(1 : Mat k))))))))) = Matrix.single 4 17 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_4_18 : (pathMap k (representative k ⟨(4,18),by decide⟩)).val=basisMatrix k ⟨(4,18),by decide⟩ := by
  change (pathMap k (pathArrow k 7*(pathArrow k 20*1))).val = Matrix.single 4 18 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(1 : Mat k))) = Matrix.single 4 18 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_5_0 : (pathMap k (representative k ⟨(5,0),by decide⟩)).val=basisMatrix k ⟨(5,0),by decide⟩ := by
  change (pathMap k (pathArrow k 4*(pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*(pathArrow k 0*1)))))))))))))).val = Matrix.single 5 0 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 5 4 (1:k)*(Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(Matrix.single 1 0 (1:k)*(1 : Mat k)))))))))))))) = Matrix.single 5 0 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_5_1 : (pathMap k (representative k ⟨(5,1),by decide⟩)).val=basisMatrix k ⟨(5,1),by decide⟩ := by
  change (pathMap k (pathArrow k 4*(pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*1))))))))))))).val = Matrix.single 5 1 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 5 4 (1:k)*(Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(1 : Mat k))))))))))))) = Matrix.single 5 1 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_5_2 : (pathMap k (representative k ⟨(5,2),by decide⟩)).val=basisMatrix k ⟨(5,2),by decide⟩ := by
  change (pathMap k (pathArrow k 4*(pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 2*1)))))))).val = Matrix.single 5 2 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 5 4 (1:k)*(Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 2 (1:k)*(1 : Mat k)))))))) = Matrix.single 5 2 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_5_3 : (pathMap k (representative k ⟨(5,3),by decide⟩)).val=basisMatrix k ⟨(5,3),by decide⟩ := by
  change (pathMap k (pathArrow k 4*(pathArrow k 7*(pathArrow k 20*(pathArrow k 3*1))))).val = Matrix.single 5 3 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 5 4 (1:k)*(Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(1 : Mat k))))) = Matrix.single 5 3 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_5_4 : (pathMap k (representative k ⟨(5,4),by decide⟩)).val=basisMatrix k ⟨(5,4),by decide⟩ := by
  change (pathMap k (pathArrow k 4*1)).val = Matrix.single 5 4 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 5 4 (1:k)*(1 : Mat k)) = Matrix.single 5 4 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_5_5 : (pathMap k (representative k ⟨(5,5),by decide⟩)).val=basisMatrix k ⟨(5,5),by decide⟩ := by
  change (vertex k 5).val = Matrix.single 5 5 1+0
  ext r c
  fin_cases r <;> fin_cases c <;> simp [vertex,Matrix.single_apply,Matrix.diagonal_apply,slotVertex]
theorem image_5_6 : (pathMap k (representative k ⟨(5,6),by decide⟩)).val=basisMatrix k ⟨(5,6),by decide⟩ := by
  change (pathMap k (pathArrow k 4*(pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*1)))))))))))).val = Matrix.single 5 6 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 5 4 (1:k)*(Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(1 : Mat k)))))))))))) = Matrix.single 5 6 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_5_7 : (pathMap k (representative k ⟨(5,7),by decide⟩)).val=basisMatrix k ⟨(5,7),by decide⟩ := by
  change (pathMap k (pathArrow k 4*(pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*1))))))).val = Matrix.single 5 7 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 5 4 (1:k)*(Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(1 : Mat k))))))) = Matrix.single 5 7 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_5_8 : (pathMap k (representative k ⟨(5,8),by decide⟩)).val=basisMatrix k ⟨(5,8),by decide⟩ := by
  change (pathMap k (pathArrow k 4*(pathArrow k 7*1))).val = Matrix.single 5 8 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 5 4 (1:k)*(Matrix.single 4 8 (1:k)*(1 : Mat k))) = Matrix.single 5 8 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_5_9 : (pathMap k (representative k ⟨(5,9),by decide⟩)).val=basisMatrix k ⟨(5,9),by decide⟩ := by
  change (pathMap k (pathArrow k 4*(pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*1))))))))))).val = Matrix.single 5 9 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 5 4 (1:k)*(Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(1 : Mat k))))))))))) = Matrix.single 5 9 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_5_10 : (pathMap k (representative k ⟨(5,10),by decide⟩)).val=basisMatrix k ⟨(5,10),by decide⟩ := by
  change (pathMap k (pathArrow k 4*(pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*1))))))))).val = Matrix.single 5 10 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 5 4 (1:k)*(Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(1 : Mat k))))))))) = Matrix.single 5 10 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_5_11 : (pathMap k (representative k ⟨(5,11),by decide⟩)).val=basisMatrix k ⟨(5,11),by decide⟩ := by
  change (pathMap k (pathArrow k 4*(pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*1)))))).val = Matrix.single 5 11 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 5 4 (1:k)*(Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(1 : Mat k)))))) = Matrix.single 5 11 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_5_12 : (pathMap k (representative k ⟨(5,12),by decide⟩)).val=basisMatrix k ⟨(5,12),by decide⟩ := by
  change (pathMap k (pathArrow k 4*(pathArrow k 7*(pathArrow k 20*(pathArrow k 12*1))))).val = Matrix.single 5 12 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 5 4 (1:k)*(Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 12 (1:k)*(1 : Mat k))))) = Matrix.single 5 12 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_5_13 : (pathMap k (representative k ⟨(5,13),by decide⟩)).val=basisMatrix k ⟨(5,13),by decide⟩ := by
  change (pathMap k (pathArrow k 4*(pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 2*(pathArrow k 13*1))))))))).val = Matrix.single 5 13 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 5 4 (1:k)*(Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 2 (1:k)*(Matrix.single 2 13 (1:k)*(1 : Mat k))))))))) = Matrix.single 5 13 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_5_14 : (pathMap k (representative k ⟨(5,14),by decide⟩)).val=basisMatrix k ⟨(5,14),by decide⟩ := by
  change (pathMap k (pathArrow k 4*(pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 15*1))))))).val = Matrix.single 5 14 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 5 4 (1:k)*(Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 14 (1:k)*(1 : Mat k))))))) = Matrix.single 5 14 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_5_15 : (pathMap k (representative k ⟨(5,15),by decide⟩)).val=basisMatrix k ⟨(5,15),by decide⟩ := by
  change (pathMap k (pathArrow k 4*(pathArrow k 7*(pathArrow k 20*(pathArrow k 12*(pathArrow k 17*1)))))).val = Matrix.single 5 15 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 5 4 (1:k)*(Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 12 (1:k)*(Matrix.single 12 15 (1:k)*(1 : Mat k)))))) = Matrix.single 5 15 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_5_16 : (pathMap k (representative k ⟨(5,16),by decide⟩)).val=basisMatrix k ⟨(5,16),by decide⟩ := by
  change (pathMap k (pathArrow k 4*(pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*1)))))))).val = Matrix.single 5 16 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 5 4 (1:k)*(Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(1 : Mat k)))))))) = Matrix.single 5 16 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_5_17 : (pathMap k (representative k ⟨(5,17),by decide⟩)).val=basisMatrix k ⟨(5,17),by decide⟩ := by
  change (pathMap k (pathArrow k 4*(pathArrow k 7*(pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*1)))))))))).val = Matrix.single 5 17 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 5 4 (1:k)*(Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(1 : Mat k)))))))))) = Matrix.single 5 17 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_5_18 : (pathMap k (representative k ⟨(5,18),by decide⟩)).val=basisMatrix k ⟨(5,18),by decide⟩ := by
  change (pathMap k (pathArrow k 4*(pathArrow k 7*(pathArrow k 20*1)))).val = Matrix.single 5 18 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 5 4 (1:k)*(Matrix.single 4 8 (1:k)*(Matrix.single 8 18 (1:k)*(1 : Mat k)))) = Matrix.single 5 18 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_6_0 : (pathMap k (representative k ⟨(6,0),by decide⟩)).val=basisMatrix k ⟨(6,0),by decide⟩ := by
  change (pathMap k (pathArrow k 1*(pathArrow k 0*1))).val = Matrix.single 6 0 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 6 1 (1:k)*(Matrix.single 1 0 (1:k)*(1 : Mat k))) = Matrix.single 6 0 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_6_1 : (pathMap k (representative k ⟨(6,1),by decide⟩)).val=basisMatrix k ⟨(6,1),by decide⟩ := by
  change (pathMap k (pathArrow k 1*1)).val = Matrix.single 6 1 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 6 1 (1:k)*(1 : Mat k)) = Matrix.single 6 1 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_6_6 : (pathMap k (representative k ⟨(6,6),by decide⟩)).val=basisMatrix k ⟨(6,6),by decide⟩ := by
  change (vertex k 6).val = Matrix.single 6 6 1+0
  ext r c
  fin_cases r <;> fin_cases c <;> simp [vertex,Matrix.single_apply,Matrix.diagonal_apply,slotVertex]
theorem image_7_0 : (pathMap k (representative k ⟨(7,0),by decide⟩)).val=basisMatrix k ⟨(7,0),by decide⟩ := by
  change (pathMap k (pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*(pathArrow k 0*1)))))))).val = Matrix.single 7 0 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(Matrix.single 1 0 (1:k)*(1 : Mat k)))))))) = Matrix.single 7 0 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_7_1 : (pathMap k (representative k ⟨(7,1),by decide⟩)).val=basisMatrix k ⟨(7,1),by decide⟩ := by
  change (pathMap k (pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*1))))))).val = Matrix.single 7 1 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(1 : Mat k))))))) = Matrix.single 7 1 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_7_2 : (pathMap k (representative k ⟨(7,2),by decide⟩)).val=basisMatrix k ⟨(7,2),by decide⟩ := by
  change (pathMap k (pathArrow k 2*1)).val = Matrix.single 7 2 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 7 2 (1:k)*(1 : Mat k)) = Matrix.single 7 2 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_7_6 : (pathMap k (representative k ⟨(7,6),by decide⟩)).val=basisMatrix k ⟨(7,6),by decide⟩ := by
  change (pathMap k (pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*1)))))).val = Matrix.single 7 6 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(1 : Mat k)))))) = Matrix.single 7 6 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_7_7 : (pathMap k (representative k ⟨(7,7),by decide⟩)).val=basisMatrix k ⟨(7,7),by decide⟩ := by
  change (vertex k 7).val = Matrix.single 7 7 1+0
  ext r c
  fin_cases r <;> fin_cases c <;> simp [vertex,Matrix.single_apply,Matrix.diagonal_apply,slotVertex]
theorem image_7_9 : (pathMap k (representative k ⟨(7,9),by decide⟩)).val=basisMatrix k ⟨(7,9),by decide⟩ := by
  change (pathMap k (pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*1))))).val = Matrix.single 7 9 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(1 : Mat k))))) = Matrix.single 7 9 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_7_10 : (pathMap k (representative k ⟨(7,10),by decide⟩)).val=basisMatrix k ⟨(7,10),by decide⟩ := by
  change (pathMap k (pathArrow k 18*(pathArrow k 9*1))).val = Matrix.single 7 10 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(1 : Mat k))) = Matrix.single 7 10 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_7_13 : (pathMap k (representative k ⟨(7,13),by decide⟩)).val=basisMatrix k ⟨(7,13),by decide⟩ := by
  change (pathMap k (pathArrow k 2*(pathArrow k 13*1))).val = Matrix.single 7 13 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 7 2 (1:k)*(Matrix.single 2 13 (1:k)*(1 : Mat k))) = Matrix.single 7 13 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_7_16 : (pathMap k (representative k ⟨(7,16),by decide⟩)).val=basisMatrix k ⟨(7,16),by decide⟩ := by
  change (pathMap k (pathArrow k 18*1)).val = Matrix.single 7 16 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 7 16 (1:k)*(1 : Mat k)) = Matrix.single 7 16 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_7_17 : (pathMap k (representative k ⟨(7,17),by decide⟩)).val=basisMatrix k ⟨(7,17),by decide⟩ := by
  change (pathMap k (pathArrow k 18*(pathArrow k 9*(pathArrow k 21*1)))).val = Matrix.single 7 17 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(1 : Mat k)))) = Matrix.single 7 17 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_8_0 : (pathMap k (representative k ⟨(8,0),by decide⟩)).val=basisMatrix k ⟨(8,0),by decide⟩ := by
  change (pathMap k (pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*(pathArrow k 0*1)))))))))))).val = Matrix.single 8 0 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(Matrix.single 1 0 (1:k)*(1 : Mat k)))))))))))) = Matrix.single 8 0 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_8_1 : (pathMap k (representative k ⟨(8,1),by decide⟩)).val=basisMatrix k ⟨(8,1),by decide⟩ := by
  change (pathMap k (pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*1))))))))))).val = Matrix.single 8 1 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(1 : Mat k))))))))))) = Matrix.single 8 1 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_8_2 : (pathMap k (representative k ⟨(8,2),by decide⟩)).val=basisMatrix k ⟨(8,2),by decide⟩ := by
  change (pathMap k (pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 2*1)))))).val = Matrix.single 8 2 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 2 (1:k)*(1 : Mat k)))))) = Matrix.single 8 2 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_8_3 : (pathMap k (representative k ⟨(8,3),by decide⟩)).val=basisMatrix k ⟨(8,3),by decide⟩ := by
  change (pathMap k (pathArrow k 20*(pathArrow k 3*1))).val = Matrix.single 8 3 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(1 : Mat k))) = Matrix.single 8 3 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_8_6 : (pathMap k (representative k ⟨(8,6),by decide⟩)).val=basisMatrix k ⟨(8,6),by decide⟩ := by
  change (pathMap k (pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*1)))))))))).val = Matrix.single 8 6 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(1 : Mat k)))))))))) = Matrix.single 8 6 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_8_7 : (pathMap k (representative k ⟨(8,7),by decide⟩)).val=basisMatrix k ⟨(8,7),by decide⟩ := by
  change (pathMap k (pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*1))))).val = Matrix.single 8 7 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(1 : Mat k))))) = Matrix.single 8 7 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_8_8 : (pathMap k (representative k ⟨(8,8),by decide⟩)).val=basisMatrix k ⟨(8,8),by decide⟩ := by
  change (vertex k 8).val = Matrix.single 8 8 1+0
  ext r c
  fin_cases r <;> fin_cases c <;> simp [vertex,Matrix.single_apply,Matrix.diagonal_apply,slotVertex]
theorem image_8_9 : (pathMap k (representative k ⟨(8,9),by decide⟩)).val=basisMatrix k ⟨(8,9),by decide⟩ := by
  change (pathMap k (pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*1))))))))).val = Matrix.single 8 9 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(1 : Mat k))))))))) = Matrix.single 8 9 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_8_10 : (pathMap k (representative k ⟨(8,10),by decide⟩)).val=basisMatrix k ⟨(8,10),by decide⟩ := by
  change (pathMap k (pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*1))))))).val = Matrix.single 8 10 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(1 : Mat k))))))) = Matrix.single 8 10 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_8_11 : (pathMap k (representative k ⟨(8,11),by decide⟩)).val=basisMatrix k ⟨(8,11),by decide⟩ := by
  change (pathMap k (pathArrow k 20*(pathArrow k 3*(pathArrow k 10*1)))).val = Matrix.single 8 11 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(1 : Mat k)))) = Matrix.single 8 11 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_8_12 : (pathMap k (representative k ⟨(8,12),by decide⟩)).val=basisMatrix k ⟨(8,12),by decide⟩ := by
  change (pathMap k (pathArrow k 20*(pathArrow k 12*1))).val = Matrix.single 8 12 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 8 18 (1:k)*(Matrix.single 18 12 (1:k)*(1 : Mat k))) = Matrix.single 8 12 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_8_13 : (pathMap k (representative k ⟨(8,13),by decide⟩)).val=basisMatrix k ⟨(8,13),by decide⟩ := by
  change (pathMap k (pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 2*(pathArrow k 13*1))))))).val = Matrix.single 8 13 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 2 (1:k)*(Matrix.single 2 13 (1:k)*(1 : Mat k))))))) = Matrix.single 8 13 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_8_14 : (pathMap k (representative k ⟨(8,14),by decide⟩)).val=basisMatrix k ⟨(8,14),by decide⟩ := by
  change (pathMap k (pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 15*1))))).val = Matrix.single 8 14 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 14 (1:k)*(1 : Mat k))))) = Matrix.single 8 14 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_8_15 : (pathMap k (representative k ⟨(8,15),by decide⟩)).val=basisMatrix k ⟨(8,15),by decide⟩ := by
  change (pathMap k (pathArrow k 20*(pathArrow k 12*(pathArrow k 17*1)))).val = Matrix.single 8 15 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 8 18 (1:k)*(Matrix.single 18 12 (1:k)*(Matrix.single 12 15 (1:k)*(1 : Mat k)))) = Matrix.single 8 15 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_8_16 : (pathMap k (representative k ⟨(8,16),by decide⟩)).val=basisMatrix k ⟨(8,16),by decide⟩ := by
  change (pathMap k (pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*1)))))).val = Matrix.single 8 16 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(1 : Mat k)))))) = Matrix.single 8 16 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_8_17 : (pathMap k (representative k ⟨(8,17),by decide⟩)).val=basisMatrix k ⟨(8,17),by decide⟩ := by
  change (pathMap k (pathArrow k 20*(pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*1)))))))).val = Matrix.single 8 17 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 8 18 (1:k)*(Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(1 : Mat k)))))))) = Matrix.single 8 17 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_8_18 : (pathMap k (representative k ⟨(8,18),by decide⟩)).val=basisMatrix k ⟨(8,18),by decide⟩ := by
  change (pathMap k (pathArrow k 20*1)).val = Matrix.single 8 18 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 8 18 (1:k)*(1 : Mat k)) = Matrix.single 8 18 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_9_0 : (pathMap k (representative k ⟨(9,0),by decide⟩)).val=basisMatrix k ⟨(9,0),by decide⟩ := by
  change (pathMap k (pathArrow k 5*(pathArrow k 1*(pathArrow k 0*1)))).val = Matrix.single 9 0 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(Matrix.single 1 0 (1:k)*(1 : Mat k)))) = Matrix.single 9 0 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_9_1 : (pathMap k (representative k ⟨(9,1),by decide⟩)).val=basisMatrix k ⟨(9,1),by decide⟩ := by
  change (pathMap k (pathArrow k 5*(pathArrow k 1*1))).val = Matrix.single 9 1 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(1 : Mat k))) = Matrix.single 9 1 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_9_6 : (pathMap k (representative k ⟨(9,6),by decide⟩)).val=basisMatrix k ⟨(9,6),by decide⟩ := by
  change (pathMap k (pathArrow k 5*1)).val = Matrix.single 9 6 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 9 6 (1:k)*(1 : Mat k)) = Matrix.single 9 6 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_9_9 : (pathMap k (representative k ⟨(9,9),by decide⟩)).val=basisMatrix k ⟨(9,9),by decide⟩ := by
  change (vertex k 9).val = Matrix.single 9 9 1+0
  ext r c
  fin_cases r <;> fin_cases c <;> simp [vertex,Matrix.single_apply,Matrix.diagonal_apply,slotVertex]
theorem image_10_0 : (pathMap k (representative k ⟨(10,0),by decide⟩)).val=basisMatrix k ⟨(10,0),by decide⟩ := by
  change (pathMap k (pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*(pathArrow k 0*1)))))).val = Matrix.single 10 0 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(Matrix.single 1 0 (1:k)*(1 : Mat k)))))) = Matrix.single 10 0 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_10_1 : (pathMap k (representative k ⟨(10,1),by decide⟩)).val=basisMatrix k ⟨(10,1),by decide⟩ := by
  change (pathMap k (pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*1))))).val = Matrix.single 10 1 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(1 : Mat k))))) = Matrix.single 10 1 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_10_6 : (pathMap k (representative k ⟨(10,6),by decide⟩)).val=basisMatrix k ⟨(10,6),by decide⟩ := by
  change (pathMap k (pathArrow k 21*(pathArrow k 8*(pathArrow k 5*1)))).val = Matrix.single 10 6 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(1 : Mat k)))) = Matrix.single 10 6 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_10_9 : (pathMap k (representative k ⟨(10,9),by decide⟩)).val=basisMatrix k ⟨(10,9),by decide⟩ := by
  change (pathMap k (pathArrow k 21*(pathArrow k 8*1))).val = Matrix.single 10 9 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(1 : Mat k))) = Matrix.single 10 9 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_10_10 : (pathMap k (representative k ⟨(10,10),by decide⟩)).val=basisMatrix k ⟨(10,10),by decide⟩ := by
  change (vertex k 10).val = Matrix.single 10 10 1+0
  ext r c
  fin_cases r <;> fin_cases c <;> simp [vertex,Matrix.single_apply,Matrix.diagonal_apply,slotVertex]
theorem image_10_17 : (pathMap k (representative k ⟨(10,17),by decide⟩)).val=basisMatrix k ⟨(10,17),by decide⟩ := by
  change (pathMap k (pathArrow k 21*1)).val = Matrix.single 10 17 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 10 17 (1:k)*(1 : Mat k)) = Matrix.single 10 17 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_11_0 : (pathMap k (representative k ⟨(11,0),by decide⟩)).val=basisMatrix k ⟨(11,0),by decide⟩ := by
  change (pathMap k (pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*(pathArrow k 0*1))))))))).val = Matrix.single 11 0 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(Matrix.single 1 0 (1:k)*(1 : Mat k))))))))) = Matrix.single 11 0 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_11_1 : (pathMap k (representative k ⟨(11,1),by decide⟩)).val=basisMatrix k ⟨(11,1),by decide⟩ := by
  change (pathMap k (pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*1)))))))).val = Matrix.single 11 1 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(1 : Mat k)))))))) = Matrix.single 11 1 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_11_2 : (pathMap k (representative k ⟨(11,2),by decide⟩)).val=basisMatrix k ⟨(11,2),by decide⟩ := by
  change (pathMap k (pathArrow k 6*(pathArrow k 2*1))).val = Matrix.single 11 2 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 11 7 (1:k)*(Matrix.single 7 2 (1:k)*(1 : Mat k))) = Matrix.single 11 2 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_11_6 : (pathMap k (representative k ⟨(11,6),by decide⟩)).val=basisMatrix k ⟨(11,6),by decide⟩ := by
  change (pathMap k (pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*1))))))).val = Matrix.single 11 6 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(1 : Mat k))))))) = Matrix.single 11 6 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_11_7 : (pathMap k (representative k ⟨(11,7),by decide⟩)).val=basisMatrix k ⟨(11,7),by decide⟩ := by
  change (pathMap k (pathArrow k 6*1)).val = Matrix.single 11 7 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 11 7 (1:k)*(1 : Mat k)) = Matrix.single 11 7 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_11_9 : (pathMap k (representative k ⟨(11,9),by decide⟩)).val=basisMatrix k ⟨(11,9),by decide⟩ := by
  change (pathMap k (pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*1)))))).val = Matrix.single 11 9 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(1 : Mat k)))))) = Matrix.single 11 9 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_11_10 : (pathMap k (representative k ⟨(11,10),by decide⟩)).val=basisMatrix k ⟨(11,10),by decide⟩ := by
  change (pathMap k (pathArrow k 6*(pathArrow k 18*(pathArrow k 9*1)))).val = Matrix.single 11 10 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(1 : Mat k)))) = Matrix.single 11 10 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_11_11 : (pathMap k (representative k ⟨(11,11),by decide⟩)).val=basisMatrix k ⟨(11,11),by decide⟩ := by
  change (vertex k 11).val = Matrix.single 11 11 1+0
  ext r c
  fin_cases r <;> fin_cases c <;> simp [vertex,Matrix.single_apply,Matrix.diagonal_apply,slotVertex]
theorem image_11_13 : (pathMap k (representative k ⟨(11,13),by decide⟩)).val=basisMatrix k ⟨(11,13),by decide⟩ := by
  change (pathMap k (pathArrow k 6*(pathArrow k 2*(pathArrow k 13*1)))).val = Matrix.single 11 13 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 11 7 (1:k)*(Matrix.single 7 2 (1:k)*(Matrix.single 2 13 (1:k)*(1 : Mat k)))) = Matrix.single 11 13 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_11_14 : (pathMap k (representative k ⟨(11,14),by decide⟩)).val=basisMatrix k ⟨(11,14),by decide⟩ := by
  change (pathMap k (pathArrow k 15*1)).val = Matrix.single 11 14 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 11 14 (1:k)*(1 : Mat k)) = Matrix.single 11 14 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_11_16 : (pathMap k (representative k ⟨(11,16),by decide⟩)).val=basisMatrix k ⟨(11,16),by decide⟩ := by
  change (pathMap k (pathArrow k 6*(pathArrow k 18*1))).val = Matrix.single 11 16 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(1 : Mat k))) = Matrix.single 11 16 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_11_17 : (pathMap k (representative k ⟨(11,17),by decide⟩)).val=basisMatrix k ⟨(11,17),by decide⟩ := by
  change (pathMap k (pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*1))))).val = Matrix.single 11 17 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(1 : Mat k))))) = Matrix.single 11 17 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_12_0 : (pathMap k (representative k ⟨(12,0),by decide⟩)).val=basisMatrix k ⟨(12,0),by decide⟩ := by
  change (pathMap k (pathArrow k 11*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*(pathArrow k 0*1)))))))))).val = Matrix.single 12 0 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 12 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(Matrix.single 1 0 (1:k)*(1 : Mat k)))))))))) = Matrix.single 12 0 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_12_1 : (pathMap k (representative k ⟨(12,1),by decide⟩)).val=basisMatrix k ⟨(12,1),by decide⟩ := by
  change (pathMap k (pathArrow k 11*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*1))))))))).val = Matrix.single 12 1 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 12 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(1 : Mat k))))))))) = Matrix.single 12 1 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_12_2 : (pathMap k (representative k ⟨(12,2),by decide⟩)).val=basisMatrix k ⟨(12,2),by decide⟩ := by
  change (pathMap k (pathArrow k 11*(pathArrow k 6*(pathArrow k 2*1)))).val = Matrix.single 12 2 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 12 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 2 (1:k)*(1 : Mat k)))) = Matrix.single 12 2 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_12_6 : (pathMap k (representative k ⟨(12,6),by decide⟩)).val=basisMatrix k ⟨(12,6),by decide⟩ := by
  change (pathMap k (pathArrow k 11*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*1)))))))).val = Matrix.single 12 6 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 12 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(1 : Mat k)))))))) = Matrix.single 12 6 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_12_7 : (pathMap k (representative k ⟨(12,7),by decide⟩)).val=basisMatrix k ⟨(12,7),by decide⟩ := by
  change (pathMap k (pathArrow k 11*(pathArrow k 6*1))).val = Matrix.single 12 7 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 12 11 (1:k)*(Matrix.single 11 7 (1:k)*(1 : Mat k))) = Matrix.single 12 7 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_12_9 : (pathMap k (representative k ⟨(12,9),by decide⟩)).val=basisMatrix k ⟨(12,9),by decide⟩ := by
  change (pathMap k (pathArrow k 11*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*1))))))).val = Matrix.single 12 9 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 12 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(1 : Mat k))))))) = Matrix.single 12 9 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_12_10 : (pathMap k (representative k ⟨(12,10),by decide⟩)).val=basisMatrix k ⟨(12,10),by decide⟩ := by
  change (pathMap k (pathArrow k 11*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*1))))).val = Matrix.single 12 10 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 12 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(1 : Mat k))))) = Matrix.single 12 10 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_12_11 : (pathMap k (representative k ⟨(12,11),by decide⟩)).val=basisMatrix k ⟨(12,11),by decide⟩ := by
  change (pathMap k (pathArrow k 11*1)).val = Matrix.single 12 11 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 12 11 (1:k)*(1 : Mat k)) = Matrix.single 12 11 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_12_12 : (pathMap k (representative k ⟨(12,12),by decide⟩)).val=basisMatrix k ⟨(12,12),by decide⟩ := by
  change (vertex k 12).val = Matrix.single 12 12 1+0
  ext r c
  fin_cases r <;> fin_cases c <;> simp [vertex,Matrix.single_apply,Matrix.diagonal_apply,slotVertex]
theorem image_12_13 : (pathMap k (representative k ⟨(12,13),by decide⟩)).val=basisMatrix k ⟨(12,13),by decide⟩ := by
  change (pathMap k (pathArrow k 11*(pathArrow k 6*(pathArrow k 2*(pathArrow k 13*1))))).val = Matrix.single 12 13 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 12 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 2 (1:k)*(Matrix.single 2 13 (1:k)*(1 : Mat k))))) = Matrix.single 12 13 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_12_14 : (pathMap k (representative k ⟨(12,14),by decide⟩)).val=basisMatrix k ⟨(12,14),by decide⟩ := by
  change (pathMap k (pathArrow k 11*(pathArrow k 15*1))).val = Matrix.single 12 14 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 12 11 (1:k)*(Matrix.single 11 14 (1:k)*(1 : Mat k))) = Matrix.single 12 14 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_12_15 : (pathMap k (representative k ⟨(12,15),by decide⟩)).val=basisMatrix k ⟨(12,15),by decide⟩ := by
  change (pathMap k (pathArrow k 17*1)).val = Matrix.single 12 15 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 12 15 (1:k)*(1 : Mat k)) = Matrix.single 12 15 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_12_16 : (pathMap k (representative k ⟨(12,16),by decide⟩)).val=basisMatrix k ⟨(12,16),by decide⟩ := by
  change (pathMap k (pathArrow k 11*(pathArrow k 6*(pathArrow k 18*1)))).val = Matrix.single 12 16 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 12 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(1 : Mat k)))) = Matrix.single 12 16 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_12_17 : (pathMap k (representative k ⟨(12,17),by decide⟩)).val=basisMatrix k ⟨(12,17),by decide⟩ := by
  change (pathMap k (pathArrow k 11*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*1)))))).val = Matrix.single 12 17 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 12 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(1 : Mat k)))))) = Matrix.single 12 17 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_13_0 : (pathMap k (representative k ⟨(13,0),by decide⟩)).val=basisMatrix k ⟨(13,0),by decide⟩ := by
  change (pathMap k (pathArrow k 22*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*(pathArrow k 0*1)))))).val = Matrix.single 13 0 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 13 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(Matrix.single 1 0 (1:k)*(1 : Mat k)))))) = Matrix.single 13 0 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_13_1 : (pathMap k (representative k ⟨(13,1),by decide⟩)).val=basisMatrix k ⟨(13,1),by decide⟩ := by
  change (pathMap k (pathArrow k 22*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*1))))).val = Matrix.single 13 1 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 13 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(1 : Mat k))))) = Matrix.single 13 1 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_13_6 : (pathMap k (representative k ⟨(13,6),by decide⟩)).val=basisMatrix k ⟨(13,6),by decide⟩ := by
  change (pathMap k (pathArrow k 22*(pathArrow k 8*(pathArrow k 5*1)))).val = Matrix.single 13 6 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 13 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(1 : Mat k)))) = Matrix.single 13 6 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_13_9 : (pathMap k (representative k ⟨(13,9),by decide⟩)).val=basisMatrix k ⟨(13,9),by decide⟩ := by
  change (pathMap k (pathArrow k 22*(pathArrow k 8*1))).val = Matrix.single 13 9 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 13 17 (1:k)*(Matrix.single 17 9 (1:k)*(1 : Mat k))) = Matrix.single 13 9 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_13_13 : (pathMap k (representative k ⟨(13,13),by decide⟩)).val=basisMatrix k ⟨(13,13),by decide⟩ := by
  change (vertex k 13).val = Matrix.single 13 13 1+0
  ext r c
  fin_cases r <;> fin_cases c <;> simp [vertex,Matrix.single_apply,Matrix.diagonal_apply,slotVertex]
theorem image_13_17 : (pathMap k (representative k ⟨(13,17),by decide⟩)).val=basisMatrix k ⟨(13,17),by decide⟩ := by
  change (pathMap k (pathArrow k 22*1)).val = Matrix.single 13 17 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 13 17 (1:k)*(1 : Mat k)) = Matrix.single 13 17 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_14_0 : (pathMap k (representative k ⟨(14,0),by decide⟩)).val=basisMatrix k ⟨(14,0),by decide⟩ := by
  change (pathMap k (pathArrow k 19*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*(pathArrow k 0*1)))))))).val = Matrix.single 14 0 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 14 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(Matrix.single 1 0 (1:k)*(1 : Mat k)))))))) = Matrix.single 14 0 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_14_1 : (pathMap k (representative k ⟨(14,1),by decide⟩)).val=basisMatrix k ⟨(14,1),by decide⟩ := by
  change (pathMap k (pathArrow k 19*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*1))))))).val = Matrix.single 14 1 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 14 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(1 : Mat k))))))) = Matrix.single 14 1 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_14_6 : (pathMap k (representative k ⟨(14,6),by decide⟩)).val=basisMatrix k ⟨(14,6),by decide⟩ := by
  change (pathMap k (pathArrow k 19*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*1)))))).val = Matrix.single 14 6 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 14 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(1 : Mat k)))))) = Matrix.single 14 6 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_14_9 : (pathMap k (representative k ⟨(14,9),by decide⟩)).val=basisMatrix k ⟨(14,9),by decide⟩ := by
  change (pathMap k (pathArrow k 19*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*1))))).val = Matrix.single 14 9 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 14 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(1 : Mat k))))) = Matrix.single 14 9 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_14_10 : (pathMap k (representative k ⟨(14,10),by decide⟩)).val=basisMatrix k ⟨(14,10),by decide⟩ := by
  change (pathMap k (pathArrow k 19*(pathArrow k 9*1))).val = Matrix.single 14 10 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 14 16 (1:k)*(Matrix.single 16 10 (1:k)*(1 : Mat k))) = Matrix.single 14 10 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_14_13 : (pathMap k (representative k ⟨(14,13),by decide⟩)).val=basisMatrix k ⟨(14,13),by decide⟩ := by
  change (pathMap k (pathArrow k 19*(pathArrow k 14*1))).val = Matrix.single 14 13 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 14 16 (1:k)*(Matrix.single 16 13 (1:k)*(1 : Mat k))) = Matrix.single 14 13 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_14_14 : (pathMap k (representative k ⟨(14,14),by decide⟩)).val=basisMatrix k ⟨(14,14),by decide⟩ := by
  change (vertex k 14).val = Matrix.single 14 14 1+0
  ext r c
  fin_cases r <;> fin_cases c <;> simp [vertex,Matrix.single_apply,Matrix.diagonal_apply,slotVertex]
theorem image_14_16 : (pathMap k (representative k ⟨(14,16),by decide⟩)).val=basisMatrix k ⟨(14,16),by decide⟩ := by
  change (pathMap k (pathArrow k 19*1)).val = Matrix.single 14 16 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 14 16 (1:k)*(1 : Mat k)) = Matrix.single 14 16 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_14_17 : (pathMap k (representative k ⟨(14,17),by decide⟩)).val=basisMatrix k ⟨(14,17),by decide⟩ := by
  change (pathMap k (pathArrow k 19*(pathArrow k 9*(pathArrow k 21*1)))).val = Matrix.single 14 17 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 14 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(1 : Mat k)))) = Matrix.single 14 17 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_15_0 : (pathMap k (representative k ⟨(15,0),by decide⟩)).val=basisMatrix k ⟨(15,0),by decide⟩ := by
  change (pathMap k (pathArrow k 16*(pathArrow k 19*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*(pathArrow k 0*1))))))))).val = Matrix.single 15 0 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 15 14 (1:k)*(Matrix.single 14 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(Matrix.single 1 0 (1:k)*(1 : Mat k))))))))) = Matrix.single 15 0 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_15_1 : (pathMap k (representative k ⟨(15,1),by decide⟩)).val=basisMatrix k ⟨(15,1),by decide⟩ := by
  change (pathMap k (pathArrow k 16*(pathArrow k 19*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*1)))))))).val = Matrix.single 15 1 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 15 14 (1:k)*(Matrix.single 14 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(1 : Mat k)))))))) = Matrix.single 15 1 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_15_6 : (pathMap k (representative k ⟨(15,6),by decide⟩)).val=basisMatrix k ⟨(15,6),by decide⟩ := by
  change (pathMap k (pathArrow k 16*(pathArrow k 19*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*1))))))).val = Matrix.single 15 6 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 15 14 (1:k)*(Matrix.single 14 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(1 : Mat k))))))) = Matrix.single 15 6 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_15_9 : (pathMap k (representative k ⟨(15,9),by decide⟩)).val=basisMatrix k ⟨(15,9),by decide⟩ := by
  change (pathMap k (pathArrow k 16*(pathArrow k 19*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*1)))))).val = Matrix.single 15 9 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 15 14 (1:k)*(Matrix.single 14 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(1 : Mat k)))))) = Matrix.single 15 9 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_15_10 : (pathMap k (representative k ⟨(15,10),by decide⟩)).val=basisMatrix k ⟨(15,10),by decide⟩ := by
  change (pathMap k (pathArrow k 16*(pathArrow k 19*(pathArrow k 9*1)))).val = Matrix.single 15 10 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 15 14 (1:k)*(Matrix.single 14 16 (1:k)*(Matrix.single 16 10 (1:k)*(1 : Mat k)))) = Matrix.single 15 10 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_15_13 : (pathMap k (representative k ⟨(15,13),by decide⟩)).val=basisMatrix k ⟨(15,13),by decide⟩ := by
  change (pathMap k (pathArrow k 16*(pathArrow k 19*(pathArrow k 14*1)))).val = Matrix.single 15 13 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 15 14 (1:k)*(Matrix.single 14 16 (1:k)*(Matrix.single 16 13 (1:k)*(1 : Mat k)))) = Matrix.single 15 13 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_15_14 : (pathMap k (representative k ⟨(15,14),by decide⟩)).val=basisMatrix k ⟨(15,14),by decide⟩ := by
  change (pathMap k (pathArrow k 16*1)).val = Matrix.single 15 14 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 15 14 (1:k)*(1 : Mat k)) = Matrix.single 15 14 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_15_15 : (pathMap k (representative k ⟨(15,15),by decide⟩)).val=basisMatrix k ⟨(15,15),by decide⟩ := by
  change (vertex k 15).val = Matrix.single 15 15 1+0
  ext r c
  fin_cases r <;> fin_cases c <;> simp [vertex,Matrix.single_apply,Matrix.diagonal_apply,slotVertex]
theorem image_15_16 : (pathMap k (representative k ⟨(15,16),by decide⟩)).val=basisMatrix k ⟨(15,16),by decide⟩ := by
  change (pathMap k (pathArrow k 16*(pathArrow k 19*1))).val = Matrix.single 15 16 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 15 14 (1:k)*(Matrix.single 14 16 (1:k)*(1 : Mat k))) = Matrix.single 15 16 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_15_17 : (pathMap k (representative k ⟨(15,17),by decide⟩)).val=basisMatrix k ⟨(15,17),by decide⟩ := by
  change (pathMap k (pathArrow k 16*(pathArrow k 19*(pathArrow k 9*(pathArrow k 21*1))))).val = Matrix.single 15 17 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 15 14 (1:k)*(Matrix.single 14 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(1 : Mat k))))) = Matrix.single 15 17 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_16_0 : (pathMap k (representative k ⟨(16,0),by decide⟩)).val=basisMatrix k ⟨(16,0),by decide⟩ := by
  change (pathMap k (pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*(pathArrow k 0*1))))))).val = Matrix.single 16 0 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(Matrix.single 1 0 (1:k)*(1 : Mat k))))))) = Matrix.single 16 0 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_16_1 : (pathMap k (representative k ⟨(16,1),by decide⟩)).val=basisMatrix k ⟨(16,1),by decide⟩ := by
  change (pathMap k (pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*1)))))).val = Matrix.single 16 1 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(1 : Mat k)))))) = Matrix.single 16 1 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_16_6 : (pathMap k (representative k ⟨(16,6),by decide⟩)).val=basisMatrix k ⟨(16,6),by decide⟩ := by
  change (pathMap k (pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*1))))).val = Matrix.single 16 6 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(1 : Mat k))))) = Matrix.single 16 6 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_16_9 : (pathMap k (representative k ⟨(16,9),by decide⟩)).val=basisMatrix k ⟨(16,9),by decide⟩ := by
  change (pathMap k (pathArrow k 9*(pathArrow k 21*(pathArrow k 8*1)))).val = Matrix.single 16 9 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(1 : Mat k)))) = Matrix.single 16 9 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_16_10 : (pathMap k (representative k ⟨(16,10),by decide⟩)).val=basisMatrix k ⟨(16,10),by decide⟩ := by
  change (pathMap k (pathArrow k 9*1)).val = Matrix.single 16 10 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 16 10 (1:k)*(1 : Mat k)) = Matrix.single 16 10 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_16_13 : (pathMap k (representative k ⟨(16,13),by decide⟩)).val=basisMatrix k ⟨(16,13),by decide⟩ := by
  change (pathMap k (pathArrow k 14*1)).val = Matrix.single 16 13 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 16 13 (1:k)*(1 : Mat k)) = Matrix.single 16 13 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_16_16 : (pathMap k (representative k ⟨(16,16),by decide⟩)).val=basisMatrix k ⟨(16,16),by decide⟩ := by
  change (vertex k 16).val = Matrix.single 16 16 1+0
  ext r c
  fin_cases r <;> fin_cases c <;> simp [vertex,Matrix.single_apply,Matrix.diagonal_apply,slotVertex]
theorem image_16_17 : (pathMap k (representative k ⟨(16,17),by decide⟩)).val=basisMatrix k ⟨(16,17),by decide⟩ := by
  change (pathMap k (pathArrow k 9*(pathArrow k 21*1))).val = Matrix.single 16 17 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(1 : Mat k))) = Matrix.single 16 17 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_17_0 : (pathMap k (representative k ⟨(17,0),by decide⟩)).val=basisMatrix k ⟨(17,0),by decide⟩ := by
  change (pathMap k (pathArrow k 8*(pathArrow k 5*(pathArrow k 1*(pathArrow k 0*1))))).val = Matrix.single 17 0 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(Matrix.single 1 0 (1:k)*(1 : Mat k))))) = Matrix.single 17 0 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_17_1 : (pathMap k (representative k ⟨(17,1),by decide⟩)).val=basisMatrix k ⟨(17,1),by decide⟩ := by
  change (pathMap k (pathArrow k 8*(pathArrow k 5*(pathArrow k 1*1)))).val = Matrix.single 17 1 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(1 : Mat k)))) = Matrix.single 17 1 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_17_6 : (pathMap k (representative k ⟨(17,6),by decide⟩)).val=basisMatrix k ⟨(17,6),by decide⟩ := by
  change (pathMap k (pathArrow k 8*(pathArrow k 5*1))).val = Matrix.single 17 6 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(1 : Mat k))) = Matrix.single 17 6 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_17_9 : (pathMap k (representative k ⟨(17,9),by decide⟩)).val=basisMatrix k ⟨(17,9),by decide⟩ := by
  change (pathMap k (pathArrow k 8*1)).val = Matrix.single 17 9 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 17 9 (1:k)*(1 : Mat k)) = Matrix.single 17 9 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem slotVertex_seventeen : ∀ r : Fin 19, slotVertex r=17 ↔ r=17 ∨ r=18 := by decide
theorem image_17_17 : (pathMap k (representative k ⟨(17,17),by decide⟩)).val=basisMatrix k ⟨(17,17),by decide⟩ := by
  change (vertex k 17).val = Matrix.single 17 17 1+Matrix.single 18 18 1
  ext r c
  simp only [vertex,Matrix.diagonal_apply,Matrix.single_apply,Matrix.add_apply,slotVertex_seventeen]
  split_ifs <;> (try simp_all) <;> aesop
theorem image_18_0 : (pathMap k (representative k ⟨(18,0),by decide⟩)).val=basisMatrix k ⟨(18,0),by decide⟩ := by
  change (pathMap k (pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*(pathArrow k 0*1))))))))))).val = Matrix.single 18 0 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(Matrix.single 1 0 (1:k)*(1 : Mat k))))))))))) = Matrix.single 18 0 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_18_1 : (pathMap k (representative k ⟨(18,1),by decide⟩)).val=basisMatrix k ⟨(18,1),by decide⟩ := by
  change (pathMap k (pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*(pathArrow k 1*1)))))))))).val = Matrix.single 18 1 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(Matrix.single 6 1 (1:k)*(1 : Mat k)))))))))) = Matrix.single 18 1 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_18_2 : (pathMap k (representative k ⟨(18,2),by decide⟩)).val=basisMatrix k ⟨(18,2),by decide⟩ := by
  change (pathMap k (pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 2*1))))).val = Matrix.single 18 2 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 2 (1:k)*(1 : Mat k))))) = Matrix.single 18 2 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_18_3 : (pathMap k (representative k ⟨(18,3),by decide⟩)).val=basisMatrix k ⟨(18,3),by decide⟩ := by
  change (pathMap k (pathArrow k 3*1)).val = Matrix.single 18 3 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 18 3 (1:k)*(1 : Mat k)) = Matrix.single 18 3 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_18_6 : (pathMap k (representative k ⟨(18,6),by decide⟩)).val=basisMatrix k ⟨(18,6),by decide⟩ := by
  change (pathMap k (pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*(pathArrow k 5*1))))))))).val = Matrix.single 18 6 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(Matrix.single 9 6 (1:k)*(1 : Mat k))))))))) = Matrix.single 18 6 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_18_7 : (pathMap k (representative k ⟨(18,7),by decide⟩)).val=basisMatrix k ⟨(18,7),by decide⟩ := by
  change (pathMap k (pathArrow k 3*(pathArrow k 10*(pathArrow k 6*1)))).val = Matrix.single 18 7 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(1 : Mat k)))) = Matrix.single 18 7 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_18_9 : (pathMap k (representative k ⟨(18,9),by decide⟩)).val=basisMatrix k ⟨(18,9),by decide⟩ := by
  change (pathMap k (pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*(pathArrow k 8*1)))))))).val = Matrix.single 18 9 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(Matrix.single 17 9 (1:k)*(1 : Mat k)))))))) = Matrix.single 18 9 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_18_10 : (pathMap k (representative k ⟨(18,10),by decide⟩)).val=basisMatrix k ⟨(18,10),by decide⟩ := by
  change (pathMap k (pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*1)))))).val = Matrix.single 18 10 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(1 : Mat k)))))) = Matrix.single 18 10 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_18_11 : (pathMap k (representative k ⟨(18,11),by decide⟩)).val=basisMatrix k ⟨(18,11),by decide⟩ := by
  change (pathMap k (pathArrow k 3*(pathArrow k 10*1))).val = Matrix.single 18 11 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(1 : Mat k))) = Matrix.single 18 11 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_18_12 : (pathMap k (representative k ⟨(18,12),by decide⟩)).val=basisMatrix k ⟨(18,12),by decide⟩ := by
  change (pathMap k (pathArrow k 12*1)).val = Matrix.single 18 12 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 18 12 (1:k)*(1 : Mat k)) = Matrix.single 18 12 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_18_13 : (pathMap k (representative k ⟨(18,13),by decide⟩)).val=basisMatrix k ⟨(18,13),by decide⟩ := by
  change (pathMap k (pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 2*(pathArrow k 13*1)))))).val = Matrix.single 18 13 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 2 (1:k)*(Matrix.single 2 13 (1:k)*(1 : Mat k)))))) = Matrix.single 18 13 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_18_14 : (pathMap k (representative k ⟨(18,14),by decide⟩)).val=basisMatrix k ⟨(18,14),by decide⟩ := by
  change (pathMap k (pathArrow k 3*(pathArrow k 10*(pathArrow k 15*1)))).val = Matrix.single 18 14 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 14 (1:k)*(1 : Mat k)))) = Matrix.single 18 14 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_18_15 : (pathMap k (representative k ⟨(18,15),by decide⟩)).val=basisMatrix k ⟨(18,15),by decide⟩ := by
  change (pathMap k (pathArrow k 12*(pathArrow k 17*1))).val = Matrix.single 18 15 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 18 12 (1:k)*(Matrix.single 12 15 (1:k)*(1 : Mat k))) = Matrix.single 18 15 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_18_16 : (pathMap k (representative k ⟨(18,16),by decide⟩)).val=basisMatrix k ⟨(18,16),by decide⟩ := by
  change (pathMap k (pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*1))))).val = Matrix.single 18 16 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(1 : Mat k))))) = Matrix.single 18 16 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem image_18_17 : (pathMap k (representative k ⟨(18,17),by decide⟩)).val=basisMatrix k ⟨(18,17),by decide⟩ := by
  change (pathMap k (pathArrow k 3*(pathArrow k 10*(pathArrow k 6*(pathArrow k 18*(pathArrow k 9*(pathArrow k 21*1))))))).val = Matrix.single 18 17 1+0
  rw [add_zero]
  simp only [map_mul,map_one,pathMap_arrow,Subalgebra.coe_mul,Subalgebra.coe_one]
  change (Matrix.single 18 3 (1:k)*(Matrix.single 3 11 (1:k)*(Matrix.single 11 7 (1:k)*(Matrix.single 7 16 (1:k)*(Matrix.single 16 10 (1:k)*(Matrix.single 10 17 (1:k)*(1 : Mat k))))))) = Matrix.single 18 17 1
  simp only [mul_one,Matrix.single_mul_single_same,one_mul]
theorem representative_image (c : Coord) : (pathMap k (representative k c)).val=basisMatrix k c := by
  rcases c with ⟨⟨i,j⟩,h⟩
  fin_cases i
  · fin_cases j
    · exact image_0_0 k
    · exact False.elim ((by decide : ¬(Allowed 0 1 ∧ ((0,1) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 0 2 ∧ ((0,2) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 0 3 ∧ ((0,3) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 0 4 ∧ ((0,4) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 0 5 ∧ ((0,5) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 0 6 ∧ ((0,6) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 0 7 ∧ ((0,7) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 0 8 ∧ ((0,8) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 0 9 ∧ ((0,9) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 0 10 ∧ ((0,10) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 0 11 ∧ ((0,11) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 0 12 ∧ ((0,12) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 0 13 ∧ ((0,13) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 0 14 ∧ ((0,14) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 0 15 ∧ ((0,15) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 0 16 ∧ ((0,16) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 0 17 ∧ ((0,17) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 0 18 ∧ ((0,18) : Fin 19 × Fin 19) ≠ (18,18))) h)
  · fin_cases j
    · exact image_1_0 k
    · exact image_1_1 k
    · exact False.elim ((by decide : ¬(Allowed 1 2 ∧ ((1,2) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 1 3 ∧ ((1,3) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 1 4 ∧ ((1,4) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 1 5 ∧ ((1,5) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 1 6 ∧ ((1,6) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 1 7 ∧ ((1,7) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 1 8 ∧ ((1,8) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 1 9 ∧ ((1,9) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 1 10 ∧ ((1,10) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 1 11 ∧ ((1,11) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 1 12 ∧ ((1,12) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 1 13 ∧ ((1,13) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 1 14 ∧ ((1,14) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 1 15 ∧ ((1,15) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 1 16 ∧ ((1,16) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 1 17 ∧ ((1,17) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 1 18 ∧ ((1,18) : Fin 19 × Fin 19) ≠ (18,18))) h)
  · fin_cases j
    · exact image_2_0 k
    · exact image_2_1 k
    · exact image_2_2 k
    · exact False.elim ((by decide : ¬(Allowed 2 3 ∧ ((2,3) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 2 4 ∧ ((2,4) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 2 5 ∧ ((2,5) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_2_6 k
    · exact False.elim ((by decide : ¬(Allowed 2 7 ∧ ((2,7) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 2 8 ∧ ((2,8) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_2_9 k
    · exact False.elim ((by decide : ¬(Allowed 2 10 ∧ ((2,10) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 2 11 ∧ ((2,11) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 2 12 ∧ ((2,12) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_2_13 k
    · exact False.elim ((by decide : ¬(Allowed 2 14 ∧ ((2,14) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 2 15 ∧ ((2,15) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 2 16 ∧ ((2,16) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_2_17 k
    · exact False.elim ((by decide : ¬(Allowed 2 18 ∧ ((2,18) : Fin 19 × Fin 19) ≠ (18,18))) h)
  · fin_cases j
    · exact image_3_0 k
    · exact image_3_1 k
    · exact image_3_2 k
    · exact image_3_3 k
    · exact False.elim ((by decide : ¬(Allowed 3 4 ∧ ((3,4) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 3 5 ∧ ((3,5) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_3_6 k
    · exact image_3_7 k
    · exact False.elim ((by decide : ¬(Allowed 3 8 ∧ ((3,8) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_3_9 k
    · exact image_3_10 k
    · exact image_3_11 k
    · exact False.elim ((by decide : ¬(Allowed 3 12 ∧ ((3,12) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_3_13 k
    · exact image_3_14 k
    · exact False.elim ((by decide : ¬(Allowed 3 15 ∧ ((3,15) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_3_16 k
    · exact image_3_17 k
    · exact False.elim ((by decide : ¬(Allowed 3 18 ∧ ((3,18) : Fin 19 × Fin 19) ≠ (18,18))) h)
  · fin_cases j
    · exact image_4_0 k
    · exact image_4_1 k
    · exact image_4_2 k
    · exact image_4_3 k
    · exact image_4_4 k
    · exact False.elim ((by decide : ¬(Allowed 4 5 ∧ ((4,5) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_4_6 k
    · exact image_4_7 k
    · exact image_4_8 k
    · exact image_4_9 k
    · exact image_4_10 k
    · exact image_4_11 k
    · exact image_4_12 k
    · exact image_4_13 k
    · exact image_4_14 k
    · exact image_4_15 k
    · exact image_4_16 k
    · exact image_4_17 k
    · exact image_4_18 k
  · fin_cases j
    · exact image_5_0 k
    · exact image_5_1 k
    · exact image_5_2 k
    · exact image_5_3 k
    · exact image_5_4 k
    · exact image_5_5 k
    · exact image_5_6 k
    · exact image_5_7 k
    · exact image_5_8 k
    · exact image_5_9 k
    · exact image_5_10 k
    · exact image_5_11 k
    · exact image_5_12 k
    · exact image_5_13 k
    · exact image_5_14 k
    · exact image_5_15 k
    · exact image_5_16 k
    · exact image_5_17 k
    · exact image_5_18 k
  · fin_cases j
    · exact image_6_0 k
    · exact image_6_1 k
    · exact False.elim ((by decide : ¬(Allowed 6 2 ∧ ((6,2) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 6 3 ∧ ((6,3) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 6 4 ∧ ((6,4) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 6 5 ∧ ((6,5) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_6_6 k
    · exact False.elim ((by decide : ¬(Allowed 6 7 ∧ ((6,7) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 6 8 ∧ ((6,8) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 6 9 ∧ ((6,9) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 6 10 ∧ ((6,10) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 6 11 ∧ ((6,11) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 6 12 ∧ ((6,12) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 6 13 ∧ ((6,13) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 6 14 ∧ ((6,14) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 6 15 ∧ ((6,15) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 6 16 ∧ ((6,16) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 6 17 ∧ ((6,17) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 6 18 ∧ ((6,18) : Fin 19 × Fin 19) ≠ (18,18))) h)
  · fin_cases j
    · exact image_7_0 k
    · exact image_7_1 k
    · exact image_7_2 k
    · exact False.elim ((by decide : ¬(Allowed 7 3 ∧ ((7,3) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 7 4 ∧ ((7,4) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 7 5 ∧ ((7,5) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_7_6 k
    · exact image_7_7 k
    · exact False.elim ((by decide : ¬(Allowed 7 8 ∧ ((7,8) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_7_9 k
    · exact image_7_10 k
    · exact False.elim ((by decide : ¬(Allowed 7 11 ∧ ((7,11) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 7 12 ∧ ((7,12) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_7_13 k
    · exact False.elim ((by decide : ¬(Allowed 7 14 ∧ ((7,14) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 7 15 ∧ ((7,15) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_7_16 k
    · exact image_7_17 k
    · exact False.elim ((by decide : ¬(Allowed 7 18 ∧ ((7,18) : Fin 19 × Fin 19) ≠ (18,18))) h)
  · fin_cases j
    · exact image_8_0 k
    · exact image_8_1 k
    · exact image_8_2 k
    · exact image_8_3 k
    · exact False.elim ((by decide : ¬(Allowed 8 4 ∧ ((8,4) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 8 5 ∧ ((8,5) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_8_6 k
    · exact image_8_7 k
    · exact image_8_8 k
    · exact image_8_9 k
    · exact image_8_10 k
    · exact image_8_11 k
    · exact image_8_12 k
    · exact image_8_13 k
    · exact image_8_14 k
    · exact image_8_15 k
    · exact image_8_16 k
    · exact image_8_17 k
    · exact image_8_18 k
  · fin_cases j
    · exact image_9_0 k
    · exact image_9_1 k
    · exact False.elim ((by decide : ¬(Allowed 9 2 ∧ ((9,2) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 9 3 ∧ ((9,3) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 9 4 ∧ ((9,4) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 9 5 ∧ ((9,5) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_9_6 k
    · exact False.elim ((by decide : ¬(Allowed 9 7 ∧ ((9,7) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 9 8 ∧ ((9,8) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_9_9 k
    · exact False.elim ((by decide : ¬(Allowed 9 10 ∧ ((9,10) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 9 11 ∧ ((9,11) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 9 12 ∧ ((9,12) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 9 13 ∧ ((9,13) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 9 14 ∧ ((9,14) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 9 15 ∧ ((9,15) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 9 16 ∧ ((9,16) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 9 17 ∧ ((9,17) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 9 18 ∧ ((9,18) : Fin 19 × Fin 19) ≠ (18,18))) h)
  · fin_cases j
    · exact image_10_0 k
    · exact image_10_1 k
    · exact False.elim ((by decide : ¬(Allowed 10 2 ∧ ((10,2) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 10 3 ∧ ((10,3) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 10 4 ∧ ((10,4) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 10 5 ∧ ((10,5) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_10_6 k
    · exact False.elim ((by decide : ¬(Allowed 10 7 ∧ ((10,7) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 10 8 ∧ ((10,8) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_10_9 k
    · exact image_10_10 k
    · exact False.elim ((by decide : ¬(Allowed 10 11 ∧ ((10,11) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 10 12 ∧ ((10,12) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 10 13 ∧ ((10,13) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 10 14 ∧ ((10,14) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 10 15 ∧ ((10,15) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 10 16 ∧ ((10,16) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_10_17 k
    · exact False.elim ((by decide : ¬(Allowed 10 18 ∧ ((10,18) : Fin 19 × Fin 19) ≠ (18,18))) h)
  · fin_cases j
    · exact image_11_0 k
    · exact image_11_1 k
    · exact image_11_2 k
    · exact False.elim ((by decide : ¬(Allowed 11 3 ∧ ((11,3) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 11 4 ∧ ((11,4) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 11 5 ∧ ((11,5) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_11_6 k
    · exact image_11_7 k
    · exact False.elim ((by decide : ¬(Allowed 11 8 ∧ ((11,8) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_11_9 k
    · exact image_11_10 k
    · exact image_11_11 k
    · exact False.elim ((by decide : ¬(Allowed 11 12 ∧ ((11,12) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_11_13 k
    · exact image_11_14 k
    · exact False.elim ((by decide : ¬(Allowed 11 15 ∧ ((11,15) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_11_16 k
    · exact image_11_17 k
    · exact False.elim ((by decide : ¬(Allowed 11 18 ∧ ((11,18) : Fin 19 × Fin 19) ≠ (18,18))) h)
  · fin_cases j
    · exact image_12_0 k
    · exact image_12_1 k
    · exact image_12_2 k
    · exact False.elim ((by decide : ¬(Allowed 12 3 ∧ ((12,3) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 12 4 ∧ ((12,4) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 12 5 ∧ ((12,5) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_12_6 k
    · exact image_12_7 k
    · exact False.elim ((by decide : ¬(Allowed 12 8 ∧ ((12,8) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_12_9 k
    · exact image_12_10 k
    · exact image_12_11 k
    · exact image_12_12 k
    · exact image_12_13 k
    · exact image_12_14 k
    · exact image_12_15 k
    · exact image_12_16 k
    · exact image_12_17 k
    · exact False.elim ((by decide : ¬(Allowed 12 18 ∧ ((12,18) : Fin 19 × Fin 19) ≠ (18,18))) h)
  · fin_cases j
    · exact image_13_0 k
    · exact image_13_1 k
    · exact False.elim ((by decide : ¬(Allowed 13 2 ∧ ((13,2) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 13 3 ∧ ((13,3) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 13 4 ∧ ((13,4) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 13 5 ∧ ((13,5) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_13_6 k
    · exact False.elim ((by decide : ¬(Allowed 13 7 ∧ ((13,7) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 13 8 ∧ ((13,8) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_13_9 k
    · exact False.elim ((by decide : ¬(Allowed 13 10 ∧ ((13,10) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 13 11 ∧ ((13,11) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 13 12 ∧ ((13,12) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_13_13 k
    · exact False.elim ((by decide : ¬(Allowed 13 14 ∧ ((13,14) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 13 15 ∧ ((13,15) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 13 16 ∧ ((13,16) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_13_17 k
    · exact False.elim ((by decide : ¬(Allowed 13 18 ∧ ((13,18) : Fin 19 × Fin 19) ≠ (18,18))) h)
  · fin_cases j
    · exact image_14_0 k
    · exact image_14_1 k
    · exact False.elim ((by decide : ¬(Allowed 14 2 ∧ ((14,2) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 14 3 ∧ ((14,3) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 14 4 ∧ ((14,4) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 14 5 ∧ ((14,5) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_14_6 k
    · exact False.elim ((by decide : ¬(Allowed 14 7 ∧ ((14,7) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 14 8 ∧ ((14,8) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_14_9 k
    · exact image_14_10 k
    · exact False.elim ((by decide : ¬(Allowed 14 11 ∧ ((14,11) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 14 12 ∧ ((14,12) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_14_13 k
    · exact image_14_14 k
    · exact False.elim ((by decide : ¬(Allowed 14 15 ∧ ((14,15) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_14_16 k
    · exact image_14_17 k
    · exact False.elim ((by decide : ¬(Allowed 14 18 ∧ ((14,18) : Fin 19 × Fin 19) ≠ (18,18))) h)
  · fin_cases j
    · exact image_15_0 k
    · exact image_15_1 k
    · exact False.elim ((by decide : ¬(Allowed 15 2 ∧ ((15,2) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 15 3 ∧ ((15,3) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 15 4 ∧ ((15,4) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 15 5 ∧ ((15,5) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_15_6 k
    · exact False.elim ((by decide : ¬(Allowed 15 7 ∧ ((15,7) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 15 8 ∧ ((15,8) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_15_9 k
    · exact image_15_10 k
    · exact False.elim ((by decide : ¬(Allowed 15 11 ∧ ((15,11) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 15 12 ∧ ((15,12) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_15_13 k
    · exact image_15_14 k
    · exact image_15_15 k
    · exact image_15_16 k
    · exact image_15_17 k
    · exact False.elim ((by decide : ¬(Allowed 15 18 ∧ ((15,18) : Fin 19 × Fin 19) ≠ (18,18))) h)
  · fin_cases j
    · exact image_16_0 k
    · exact image_16_1 k
    · exact False.elim ((by decide : ¬(Allowed 16 2 ∧ ((16,2) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 16 3 ∧ ((16,3) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 16 4 ∧ ((16,4) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 16 5 ∧ ((16,5) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_16_6 k
    · exact False.elim ((by decide : ¬(Allowed 16 7 ∧ ((16,7) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 16 8 ∧ ((16,8) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_16_9 k
    · exact image_16_10 k
    · exact False.elim ((by decide : ¬(Allowed 16 11 ∧ ((16,11) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 16 12 ∧ ((16,12) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_16_13 k
    · exact False.elim ((by decide : ¬(Allowed 16 14 ∧ ((16,14) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 16 15 ∧ ((16,15) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_16_16 k
    · exact image_16_17 k
    · exact False.elim ((by decide : ¬(Allowed 16 18 ∧ ((16,18) : Fin 19 × Fin 19) ≠ (18,18))) h)
  · fin_cases j
    · exact image_17_0 k
    · exact image_17_1 k
    · exact False.elim ((by decide : ¬(Allowed 17 2 ∧ ((17,2) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 17 3 ∧ ((17,3) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 17 4 ∧ ((17,4) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 17 5 ∧ ((17,5) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_17_6 k
    · exact False.elim ((by decide : ¬(Allowed 17 7 ∧ ((17,7) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 17 8 ∧ ((17,8) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_17_9 k
    · exact False.elim ((by decide : ¬(Allowed 17 10 ∧ ((17,10) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 17 11 ∧ ((17,11) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 17 12 ∧ ((17,12) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 17 13 ∧ ((17,13) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 17 14 ∧ ((17,14) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 17 15 ∧ ((17,15) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 17 16 ∧ ((17,16) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_17_17 k
    · exact False.elim ((by decide : ¬(Allowed 17 18 ∧ ((17,18) : Fin 19 × Fin 19) ≠ (18,18))) h)
  · fin_cases j
    · exact image_18_0 k
    · exact image_18_1 k
    · exact image_18_2 k
    · exact image_18_3 k
    · exact False.elim ((by decide : ¬(Allowed 18 4 ∧ ((18,4) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact False.elim ((by decide : ¬(Allowed 18 5 ∧ ((18,5) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_18_6 k
    · exact image_18_7 k
    · exact False.elim ((by decide : ¬(Allowed 18 8 ∧ ((18,8) : Fin 19 × Fin 19) ≠ (18,18))) h)
    · exact image_18_9 k
    · exact image_18_10 k
    · exact image_18_11 k
    · exact image_18_12 k
    · exact image_18_13 k
    · exact image_18_14 k
    · exact image_18_15 k
    · exact image_18_16 k
    · exact image_18_17 k
    · exact False.elim ((by decide : ¬(Allowed 18 18 ∧ ((18,18) : Fin 19 × Fin 19) ≠ (18,18))) h)
lemma basisMatrix_coordinate (c d : Coord) :
    basisMatrix k c d.val.1 d.val.2=if c=d then 1 else 0 := by
  have hn := d.property.2
  simp only [basisMatrix,Matrix.add_apply,Matrix.single_apply,ite_apply,Matrix.zero_apply]
  split_ifs <;> simp_all [Subtype.ext_iff,Prod.ext_iff,Matrix.single_apply] <;> aesop

theorem representative_coordinates (c : Coord) :
    endCoordinates k (pathMap k (representative k c))=Pi.single c 1 := by
  funext d
  change (pathMap k (representative k c)).val d.val.1 d.val.2= (Pi.single c (1:k) : Coord → k) d
  rw [representative_image,basisMatrix_coordinate]
  by_cases h : c=d
  · subst d; simp
  · simp [h,Ne.symm h,Pi.single_apply]

def liftCoordinates (v : Coord → k) : PathAlgebra k := ∑ c, v c • representative k c

theorem liftCoordinates_spec (v : Coord → k) :
    endCoordinates k (pathMap k (liftCoordinates k v))=v := by
  simp only [liftCoordinates,map_sum,map_smul,representative_coordinates]
  ext c
  simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]

theorem pathMap_surjective : Function.Surjective (pathMap k) := by
  intro M
  refine ⟨liftCoordinates k (endCoordinates k M),?_⟩
  apply (endCoordinates k).injective
  exact liftCoordinates_spec k _
end UniserialComputations.N5
