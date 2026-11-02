import N6CompositionTable
import N6Identity
import N6Support
import N6Dimensions
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
variable (k : Type*) [Field k]
def endAlgebra : Subalgebra k (TotalMatrix k) where
  carrier := {A | ∀ i j, Normal k (homKind i j) (block k A i j)}
  add_mem' := by
    intro A B ha hb i j
    rw [block_add]
    exact normal_add k (ha i j) (hb i j)
  mul_mem' := by
    intro A B ha hb i j
    rw [block_mul]
    apply normal_sum
    intro l
    exact normal_mul k (allowed_products _ _ _ (kind_allowed i l j)) (ha i l) (hb l j)
  algebraMap_mem' := by
    intro a i j
    rw [Algebra.algebraMap_eq_smul_one,block_smul]
    exact normal_smul k a (block_one_normal k i j)
abbrev End := endAlgebra k
def endBlockEquiv : End k ≃ₗ[k] EndBlocks k where
  toFun A := fun i j => ⟨block k A.val i j,A.property i j⟩
  invFun F := ⟨assemble k (fun i j => (F i j).val),by
    intro i j
    rw [block_assemble k _ (fun i j => normal_padded k i j (F i j).property)]
    exact (F i j).property⟩
  left_inv A := by apply Subtype.ext; exact assemble_block k A.val
  right_inv F := by
    funext i j
    apply Subtype.ext
    exact block_assemble k _ (fun i j => normal_padded k i j (F i j).property) i j
  map_add' A B := by
    funext i j
    apply Subtype.ext
    exact block_add k A.val B.val i j
  map_smul' a A := by
    funext i j
    apply Subtype.ext
    exact block_smul k a A.val i j
instance endFinite : FiniteDimensional k (End k) :=
  (endBlockEquiv k).symm.finiteDimensional
theorem end_finrank : Module.finrank k (End k)=1708 := by
  rw [(endBlockEquiv k).finrank_eq,endBlocks_finrank]
end UniserialComputations.N6
