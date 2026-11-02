import Final
import Mathlib.Algebra.FreeAlgebra

noncomputable section
namespace UniserialComputations.N5
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
def vertexIDs : List Nat := [15, 16, 17, 18, 19, 20, 27, 28, 29, 30, 31, 32, 34, 36, 37, 39, 43, 50]
def extraIDs : List Nat := [33, 35, 38, 40, 41, 42, 44, 45, 46, 47, 48, 49]
def objects : List DBObject := [
  ⟨15,[],[5],[]⟩,
  ⟨16,[1],[5],[[some 4]]⟩,
  ⟨17,[2],[5],[[some 3]]⟩,
  ⟨18,[3],[5],[[some 2]]⟩,
  ⟨19,[4],[5],[[some 1]]⟩,
  ⟨20,[5],[5],[[some 0]]⟩,
  ⟨27,[2],[5, 1],[[some 3,some 0]]⟩,
  ⟨28,[3],[5, 1],[[some 2,some 0]]⟩,
  ⟨29,[4],[5, 1],[[some 1,some 0]]⟩,
  ⟨30,[2],[5, 2],[[some 3,some 1]]⟩,
  ⟨31,[3],[5, 2],[[some 2,some 0]]⟩,
  ⟨32,[3],[5, 2],[[some 2,some 1]]⟩,
  ⟨33,[3, 1],[5, 2],[[some 2,some 0],[none,some 1]]⟩,
  ⟨34,[4],[5, 2],[[some 1,some 0]]⟩,
  ⟨35,[4, 1],[5, 2],[[some 1,some 0],[none,some 1]]⟩,
  ⟨36,[2],[5, 3],[[some 3,some 2]]⟩,
  ⟨37,[3],[5, 3],[[some 2,some 1]]⟩,
  ⟨38,[3, 1],[5, 3],[[some 2,some 1],[none,some 2]]⟩,
  ⟨39,[4],[5, 3],[[some 1,some 0]]⟩,
  ⟨40,[4, 1],[5, 3],[[some 1,some 0],[none,some 2]]⟩,
  ⟨41,[4, 2],[5, 3],[[some 1,some 0],[none,some 1]]⟩,
  ⟨42,[4, 2],[5, 3, 1],[[some 1,some 0,none],[none,some 1,some 0]]⟩,
  ⟨43,[3],[5, 3, 1],[[some 2,some 1,some 0]]⟩,
  ⟨44,[3, 1],[5, 3, 1],[[some 2,some 1,some 0],[none,some 2,none]]⟩,
  ⟨45,[3, 2],[5, 3, 1],[[some 2,some 1,none],[none,some 1,some 0]]⟩,
  ⟨46,[3, 1],[5, 3, 2],[[some 2,some 1,some 0],[none,none,some 1]]⟩,
  ⟨47,[4, 2],[5, 3, 2],[[some 1,some 0,none],[none,some 1,some 1]]⟩,
  ⟨48,[3, 2],[5, 4, 2],[[none,some 1,some 0],[some 3,none,some 1]]⟩,
  ⟨49,[4, 2],[5, 4, 2],[[some 1,none,some 0],[none,some 2,some 1]]⟩,
  ⟨50,[4, 2],[5, 5, 2],[[none,some 1,some 0],[some 3,none,some 1]]⟩
]
def c1Objects := objects.filter (fun o => vertexIDs.contains o.id)
def c3Objects := objects.filter (fun o => extraIDs.contains o.id)
theorem c1_count : c1Objects.length = 18 := by decide
theorem c3_count : c3Objects.length = 12 := by decide
theorem layer_partition : objects.all (fun o => vertexIDs.contains o.id != extraIDs.contains o.id) = true := by decide
def escapingTranslateIDs : List (Nat × Nat) := [(1,19),(3,18),(4,29),(6,17),(7,28),(8,34),(10,16),(11,27),(12,31),(13,39),(21,32),(22,30),(23,37),(24,50),(25,36),(26,43)]
def supportMask : Fin 19 → Nat := ![1,3,139847,224975,524255,524287,67,206535,524239,579,132675,224967,261831,139843,222787,255555,206403,131651,523983]
def Allowed (i j : Fin 19) : Prop := (supportMask i).testBit j = true
instance (i j : Fin 19) : Decidable (Allowed i j) := inferInstanceAs (Decidable (_ = _))
theorem allowed_refl : ∀ i, Allowed i i := by decide
theorem allowed_trans : ∀ i j l, Allowed i j → Allowed j l → Allowed i l := by decide
theorem allowed_antisymm : ∀ i j, Allowed i j → Allowed j i → i=j := by decide
variable (k : Type*) [Field k]
abbrev Mat := Matrix (Fin 19) (Fin 19) k
def Supported (M : Mat k) : Prop := ∀ i j, ¬Allowed i j → M i j=0
lemma diag_mul (M N : Mat k) (hM : Supported k M) (hN : Supported k N) (i : Fin 19) :
    (M*N) i i=M i i*N i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hj
    by_cases h : Allowed i j
    · have h' : ¬Allowed j i := fun g => hj (allowed_antisymm i j h g).symm
      simp [hN j i h']
    · simp [hM i j h]
  · simp

def endAlgebra : Subalgebra k (Mat k) where
  carrier := {M | Supported k M ∧ M 17 17=M 18 18}
  zero_mem' := by constructor <;> simp [Supported]
  add_mem' := by
    rintro M N ⟨hM,eM⟩ ⟨hN,eN⟩
    constructor
    · intro i j h; change M i j+N i j=0; rw [hM i j h,hN i j h]; simp
    · change M 17 17+N 17 17=M 18 18+N 18 18
      rw [eM,eN]
  one_mem' := by
    constructor
    · intro i j h
      have hij : i≠j := by rintro rfl; exact h (allowed_refl i)
      simp [hij]
    · simp
  mul_mem' := by
    rintro M N ⟨hM,eM⟩ ⟨hN,eN⟩
    constructor
    · intro i j hij
      change ∑ l, M i l*N l j=0
      apply Finset.sum_eq_zero
      intro l _
      by_cases h : Allowed i l
      · have hn : ¬Allowed l j := fun g => hij (allowed_trans i l j h g)
        simp [hN l j hn]
      · simp [hM i l h]
    · rw [diag_mul k M N hM hN,diag_mul k M N hM hN,eM,eN]
  algebraMap_mem' := by
    intro r
    constructor
    · intro i j h
      have hij : i≠j := by rintro rfl; exact h (allowed_refl i)
      simp [Algebra.algebraMap_eq_smul_one,hij]
    · simp [Algebra.algebraMap_eq_smul_one]
abbrev End := endAlgebra k
abbrev Coord := {p : Fin 19 × Fin 19 // Allowed p.1 p.2 ∧ p ≠ (18,18)}
theorem coordinate_count : Fintype.card Coord=179 := by decide

def endCoordinates : End k ≃ₗ[k] (Coord → k) where
  toFun M p := M.val p.val.1 p.val.2
  invFun v := ⟨fun i j => if h : Allowed i j ∧ (i,j)≠(18,18) then v ⟨(i,j),h⟩
    else if (i,j)=(18,18) then v ⟨(17,17),by decide⟩ else 0, by
      constructor
      · intro i j h
        have hn : (i,j)≠(18,18) := by rintro ⟨⟩; exact h (allowed_refl 18)
        simp [h,hn]
      · simp [allowed_refl]⟩
  left_inv M := by
    apply Subtype.ext
    ext i j
    by_cases h : Allowed i j ∧ (i,j)≠(18,18)
    · simp [h]
    · by_cases h' : (i,j)=(18,18)
      · obtain ⟨rfl,rfl⟩ := Prod.mk.inj h'
        simpa using M.property.2
      · have hz : ¬Allowed i j := fun g => h ⟨g,h'⟩
        simp [h,h',M.property.1 i j hz]
  right_inv v := by funext p; simp [p.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem end_dimension : Module.finrank k (End k)=179 := by
  rw [(endCoordinates k).finrank_eq]
  simp [coordinate_count]
end UniserialComputations.N5
