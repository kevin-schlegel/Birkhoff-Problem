import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic

/-!
Elementary certificates for the database computations, organized by ring length.
No AR-translation or categorical theorem is asserted here.

N2 uses vertex order C=(R=R), B=(C₁ --π--> R), A=(0-->R).
Matrices have target rows and source columns; multiplication is composition.
The quiver is A --> B --> C. Its paths are exactly the intervals i ≤ j
of Fin 3, with interval (i,j) denoting the path j --> i. Thus its path
algebra is the incidence algebra below, with the usual convolution product.
There are no relations: I=0. This finite-path encoding is specific to N2;
future N3, N4, ... namespaces may use different path encodings.
-/
noncomputable section
namespace UniserialComputations

structure DBObject where
  id : Nat
  source : List Nat
  ambient : List Nat
  generators : List (List (Option Nat))
  deriving DecidableEq, Repr

namespace N2

def oldObjects : List DBObject :=
  [⟨1, [], [1], []⟩, ⟨2, [1], [1], [[some 0]]⟩]

def newObjects : List DBObject :=
  [⟨3, [], [2], []⟩, ⟨4, [1], [2], [[some 1]]⟩,
   ⟨5, [2], [2], [[some 0]]⟩]

-- C1: the non-isomorphism with ID 1 gives ID 4 by the supplied formula.
def escapingTranslateIDs : List (Nat × Nat) := [(1, 4)]
-- C3: all database objects of ambient height exactly two are already in C1.
theorem new_ids : newObjects.map DBObject.id = [3, 4, 5] := rfl

def remainingIDs : List Nat := [3, 4, 5].filter (fun i => !(newObjects.map DBObject.id).contains i)
theorem no_remaining_objects : remainingIDs = [] := by decide

variable (k : Type*) [Field k]
abbrev Mat := Matrix (Fin 3) (Fin 3) k

/-- The elementary quotient endomorphism algebra, realized by reduced matrices.
The reduction and its exact equivalence relation are verified below. -/
def endAlgebra : Subalgebra k (Mat k) where
  carrier := {M | ∀ i j, j < i → M i j = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb i j h; simp [ha i j h, hb i j h]
  one_mem' := by intro i j h; simp [ne_of_gt h]
  mul_mem' := by
    intro a b ha hb i j h
    change ∑ l, a i l * b l j = 0
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l < i
    · simp [ha i l hl]
    · have hj : j < l := lt_of_lt_of_le h (le_of_not_gt hl)
      simp [hb l j hj]
  algebraMap_mem' := by
    intro r i j h
    simp [Algebra.algebraMap_eq_smul_one, ne_of_gt h]

abbrev End := endAlgebra k
abbrev PathAlgebra := IncidenceAlgebra k (Fin 3)

/-- Evaluate each directed path at its commuting-square matrix. -/
def pathMap : PathAlgebra k →ₐ[k] End k where
  toFun f := ⟨fun i j => f i j, fun i j h =>
    f.apply_eq_zero_of_not_le (not_le_of_gt h)⟩
  map_zero' := rfl
  map_add' _ _ := rfl
  map_one' := by apply Subtype.ext; ext i j; simp [Matrix.one_apply]
  map_mul' f g := by
    apply Subtype.ext
    ext i j
    change (∑ x ∈ Finset.Icc i j, f i x * g x j) = ∑ x, f i x * g x j
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    by_cases hix : i ≤ x
    · have hxj : ¬ x ≤ j := fun h => hx (Finset.mem_Icc.mpr ⟨hix, h⟩)
      simp [g.apply_eq_zero_of_not_le hxj]
    · simp [f.apply_eq_zero_of_not_le hix]
  commutes' r := by
    apply Subtype.ext
    ext i j
    simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply]

/-- A basis path, including length-zero paths. -/
def basisPath (i j : Fin 3) (hij : i ≤ j) : PathAlgebra k :=
  ⟨Matrix.single i j 1, by
    intro a b hab
    simp only [Matrix.single_apply]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      exact (hab hij).elim
    · rfl⟩

theorem pathMap_basis (i j : Fin 3) (hij : i ≤ j) :
    (pathMap k (basisPath k i j hij)).val = Matrix.single i j 1 := rfl

-- α : A→B, β : B→C. Their composite is nonzero.
def alpha : PathAlgebra k := basisPath k 1 2 (by decide)
def beta : PathAlgebra k := basisPath k 0 1 (by decide)

theorem arrows_compose :
    (pathMap k (beta k * alpha k)).val = Matrix.single 0 2 1 := by
  rw [map_mul]
  change Matrix.single 0 1 (1 : k) * Matrix.single 1 2 1 = _
  simp

theorem composite_nonzero : pathMap k (beta k * alpha k) ≠ 0 := by
  intro h
  have hh := congrArg (fun M : End k => M.val 0 2) h
  rw [arrows_compose] at hh
  simp at hh

/-- Every quotient matrix is the image of a linear combination of paths. -/
theorem pathMap_surjective : Function.Surjective (pathMap k) := by
  intro M
  refine ⟨⟨M.val, ?_⟩, rfl⟩
  intro i j h
  exact M.property i j (lt_of_not_ge h)

theorem pathMap_injective : Function.Injective (pathMap k) := by
  intro f g h
  apply IncidenceAlgebra.ext
  intro i j _
  exact congrFun (congrFun (congrArg Subtype.val h) i) j

def relations : Ideal (PathAlgebra k) := ⊥
theorem relations_vanish (x : PathAlgebra k) (hx : x ∈ relations k) :
    pathMap k x = 0 := by
  have : x = 0 := hx
  simp [this]

/-- Six paths: e_C, β, βα, e_B, α, e_A (lexicographic intervals). -/
abbrev Path := {p : Fin 3 × Fin 3 // p.1 ≤ p.2}
theorem path_count : Fintype.card Path = 6 := by decide

/-- Coordinates on actual paths, independent of the matrix target. -/
def pathCoordinates : PathAlgebra k ≃ₗ[k] (Path → k) where
  toFun f p := f p.val.1 p.val.2
  invFun v := ⟨fun i j => if h : i ≤ j then v ⟨(i,j), h⟩ else 0, by
    intro i j h; simp [h]⟩
  left_inv f := by
    apply IncidenceAlgebra.ext
    intro i j h
    simp [h]
  right_inv v := by funext p; simp [p.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem path_dimension : Module.finrank k (PathAlgebra k) = 6 := by
  rw [(pathCoordinates k).finrank_eq]
  simp [path_count]

def pathEndEquiv : PathAlgebra k ≃ₗ[k] End k :=
  LinearEquiv.ofBijective (pathMap k).toLinearMap
    ⟨pathMap_injective k, pathMap_surjective k⟩

theorem end_dimension : Module.finrank k (End k) = 6 := by
  rw [← (pathEndEquiv k).finrank_eq]
  exact path_dimension k

-- Since I=0, these are already the coordinates of kQ/I.
theorem dimension_equality :
    Module.finrank k (PathAlgebra k) = Module.finrank k (End k) :=
  (pathEndEquiv k).finrank_eq

/-- The underlying vector space of kQ/I; I is the zero two-sided ideal. -/
def relationSpace : Submodule k (PathAlgebra k) := ⊥
abbrev Presented := PathAlgebra k ⧸ relationSpace k

theorem relationSpace_matches (x : PathAlgebra k) :
    x ∈ relationSpace k ↔ x ∈ relations k := by
  simp [relationSpace, relations]

theorem presented_dimension : Module.finrank k (Presented k) = 6 := by
  rw [((relationSpace k).quotEquivOfEqBot rfl).finrank_eq]
  exact path_dimension k

/-- C2's requested certificates, with an actual vector-space quotient by I. -/
theorem C2_certificate :
    Function.Surjective (pathMap k) ∧
    (∀ x ∈ relations k, pathMap k x = 0) ∧
    Module.finrank k (Presented k) = Module.finrank k (End k) ∧
    Module.finrank k (End k) = 6 := by
  exact ⟨pathMap_surjective k, relations_vanish k,
    (presented_dimension k).trans (end_dimension k).symm, end_dimension k⟩

section Reduction
variable {R : Type*} [CommRing R]
variable (π : R) (ρ : R →+* k)
/- The only scalar facts needed from a length-two uniserial ring:
ρ is the residue map, it is onto, and ann(π)=ker(ρ).
These are explicit hypotheses, not assumptions about the desired algebra. -/
variable (residue_surj : Function.Surjective ρ)
variable (ann_pi : ∀ r : R, π * r = 0 ↔ ρ r = 0)

/-- Ambient matrices of commuting squares for C⊕B⊕A.
C→A must be zero; C→B and B→A have coefficients in (π).
The source component is uniquely determined because the embeddings are injective. -/
def Raw (M : Matrix (Fin 3) (Fin 3) R) : Prop :=
  ρ (M 1 0) = 0 ∧ M 2 0 = 0 ∧ ρ (M 2 1) = 0

def reduce (M : Matrix (Fin 3) (Fin 3) R) : Mat k := fun i j => ρ (M i j)

theorem raw_reduces (M : Matrix (Fin 3) (Fin 3) R) (hM : Raw k ρ M) :
    reduce k ρ M ∈ endAlgebra k := by
  intro i j hij
  rcases hM with ⟨h10, h20, h21⟩
  fin_cases i <;> fin_cases j <;>
    simp_all [reduce]

/-- The embedded source inside R³, in the order C,B,A. -/
def sourceSubmodule (u : Fin 3 → R) : Prop := ρ (u 1) = 0 ∧ u 2 = 0

include ann_pi in
/-- The raw constraints are exactly preservation of the embedded source.
`ker_pi` identifies the middle source with πR, hence with C₁. -/
theorem raw_iff_preserves
    (ker_pi : ∀ r : R, ρ r = 0 ↔ ∃ t, r = π * t)
    (M : Matrix (Fin 3) (Fin 3) R) :
    Raw k ρ M ↔ ∀ u, sourceSubmodule k ρ u →
      sourceSubmodule k ρ (M.mulVec u) := by
  have hpi : ρ π = 0 := (ker_pi π).mpr ⟨1, by simp⟩
  constructor
  · rintro ⟨h10, h20, h21⟩ u ⟨hu1, hu2⟩
    obtain ⟨t, ht⟩ := (ker_pi (u 1)).mp hu1
    have hz : M 2 1 * u 1 = 0 := by
      rw [ht, ← mul_assoc, mul_comm (M 2 1) π, (ann_pi _).mpr h21, zero_mul]
    constructor
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, map_add, map_mul,
        h10, hu1, hu2]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h20, hu2, hz]
  · intro h
    have h0 := h ![1,0,0] (by simp [sourceSubmodule])
    have h1 := h ![0,π,0] (by simp [sourceSubmodule, hpi])
    simp [sourceSubmodule, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
    refine ⟨h0.1, h0.2, (ann_pi _).mp ?_⟩
    simpa [mul_comm] using h1.2

/-- The user-specified quotient relation, on ambient matrices. -/
def Equivalent (M N : Matrix (Fin 3) (Fin 3) R) : Prop :=
  ∀ i j, π * (M i j - N i j) = 0

include ann_pi in
/-- No extra identifications and no missing identifications in the reduced model. -/
theorem quotient_exact (M N : Matrix (Fin 3) (Fin 3) R) :
    Equivalent π M N ↔ reduce k ρ M = reduce k ρ N := by
  constructor
  · intro h
    ext i j
    exact sub_eq_zero.mp (by simpa [reduce] using (ann_pi _).mp (h i j))
  · intro h i j
    apply (ann_pi _).mpr
    rw [map_sub, sub_eq_zero]
    exact congrFun (congrFun h i) j

theorem reduce_add (M N : Matrix (Fin 3) (Fin 3) R) :
    reduce k ρ (M + N) = reduce k ρ M + reduce k ρ N := by
  ext i j; exact map_add ρ _ _

theorem reduce_mul (M N : Matrix (Fin 3) (Fin 3) R) :
    reduce k ρ (M * N) = reduce k ρ M * reduce k ρ N := by
  ext i j
  simp [reduce, Matrix.mul_apply, map_sum, map_mul]

theorem reduce_scalar (r : R) (M : Matrix (Fin 3) (Fin 3) R) :
    reduce k ρ (r • M) = ρ r • reduce k ρ M := by
  ext i j
  exact map_mul ρ r (M i j)

include residue_surj in
/-- Every reduced triangular matrix has a genuine ambient-matrix lift. -/
theorem reduce_surjective (T : End k) :
    ∃ M : Matrix (Fin 3) (Fin 3) R, Raw k ρ M ∧ reduce k ρ M = T.val := by
  classical
  choose lift hlift using residue_surj
  let M : Matrix (Fin 3) (Fin 3) R :=
    fun i j => if i ≤ j then lift (T.val i j) else 0
  refine ⟨M, ?_, ?_⟩
  · simp [Raw, M]
  · ext i j
    by_cases h : i ≤ j
    · simp [reduce, M, h, hlift]
    · simp [reduce, M, h, T.property i j (lt_of_not_ge h)]

/-- Actual equivalence classes of raw commuting-square matrices.
`quotient_exact` identifies this kernel relation with π(M-N)=0. -/
def rawSetoid : Setoid {M : Matrix (Fin 3) (Fin 3) R // Raw k ρ M} :=
  Setoid.ker (fun M => reduce k ρ M.val)

def quotientToEnd : Quotient (rawSetoid k ρ) → End k :=
  Quotient.lift (fun M => ⟨reduce k ρ M.val, raw_reduces k ρ M.val M.property⟩)
    (by intro M N h; exact Subtype.ext h)

include residue_surj in
/-- This is a concrete quotient model, not an assumption identifying End. -/
theorem quotientToEnd_bijective : Function.Bijective (quotientToEnd k ρ) := by
  constructor
  · intro q q' h
    induction q, q' using Quotient.inductionOn₂ with
    | h M N =>
      apply Quotient.sound
      exact congrArg Subtype.val h
  · intro T
    obtain ⟨M, hM, he⟩ := reduce_surjective k ρ residue_surj T
    refine ⟨Quotient.mk _ ⟨M,hM⟩, ?_⟩
    exact Subtype.ext he

/-- Multiplication by π is zero in the specified length-two quotient. -/
theorem pi_scalar_killed (hπ : π * π = 0)
    (M : Matrix (Fin 3) (Fin 3) R) : Equivalent π (π • M) 0 := by
  intro i j
  change π * (π * M i j - 0) = 0
  rw [sub_zero, ← mul_assoc, hπ, zero_mul]
end Reduction

/-- Each vertex corner consists exactly of scalar multiples of its idempotent. -/
theorem corner_formula (v : Fin 3) (M : End k) :
    Matrix.single v v (1 : k) * M.val * Matrix.single v v 1 =
      Matrix.single v v (M.val v v) := by simp

/-- Elementary local-ring certificate in every vertex corner: either an element
or its complement has a two-sided inverse relative to the corner identity.
The inverse also belongs to that corner. -/
theorem corner_local (v : Fin 3) (a : k) :
    ∃ b : k,
      (Matrix.single v v a * Matrix.single v v b = Matrix.single v v 1 ∧
       Matrix.single v v b * Matrix.single v v a = Matrix.single v v 1) ∨
      (Matrix.single v v (1-a) * Matrix.single v v b = Matrix.single v v 1 ∧
       Matrix.single v v b * Matrix.single v v (1-a) = Matrix.single v v 1) := by
  by_cases ha : a = 0
  · exact ⟨1, Or.inr (by simp [ha])⟩
  · exact ⟨a⁻¹, Or.inl (by simp [ha])⟩

/-- C3: each surviving vertex corner is the residue field.
The local-ring certificate is the field criterion: x or 1-x is a unit. -/
theorem vertex_local_certificate (x : k) : IsUnit x ∨ IsUnit (1-x) := by
  by_cases h : x = 0
  · right; simp [h]
  · left; exact isUnit_iff_ne_zero.mpr h

end N2
namespace Chain
variable (k : Type*) [Field k] (m : Nat)
abbrev Mat := Matrix (Fin m) (Fin m) k

def endAlgebra : Subalgebra k (Mat k m) where
  carrier := {M | ∀ i j, j < i → M i j = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb i j h; simp [ha i j h, hb i j h]
  one_mem' := by intro i j h; simp [ne_of_gt h]
  mul_mem' := by
    intro a b ha hb i j h
    change ∑ l, a i l * b l j = 0
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l < i
    · simp [ha i l hl]
    · have hj : j < l := lt_of_lt_of_le h (le_of_not_gt hl)
      simp [hb l j hj]
  algebraMap_mem' := by
    intro r i j h
    simp [Algebra.algebraMap_eq_smul_one, ne_of_gt h]
abbrev End := endAlgebra k m
abbrev PathAlgebra := IncidenceAlgebra k (Fin m)

def pathMap : PathAlgebra k m →ₐ[k] End k m where
  toFun f := ⟨fun i j => f i j, fun i j h =>
    f.apply_eq_zero_of_not_le (not_le_of_gt h)⟩
  map_zero' := rfl
  map_add' _ _ := rfl
  map_one' := by apply Subtype.ext; ext i j; simp [Matrix.one_apply]
  map_mul' f g := by
    apply Subtype.ext
    ext i j
    change (∑ x ∈ Finset.Icc i j, f i x * g x j) = ∑ x, f i x * g x j
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    by_cases hix : i ≤ x
    · have hxj : ¬ x ≤ j := fun h => hx (Finset.mem_Icc.mpr ⟨hix, h⟩)
      simp [g.apply_eq_zero_of_not_le hxj]
    · simp [f.apply_eq_zero_of_not_le hix]
  commutes' r := by
    apply Subtype.ext
    ext i j
    simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply]

def basisPath (i j : Fin m) (hij : i ≤ j) : PathAlgebra k m :=
  ⟨Matrix.single i j 1, by
    intro a b hab
    simp only [Matrix.single_apply]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; exact (hab hij).elim
    · rfl⟩
theorem pathMap_basis (i j : Fin m) (hij : i ≤ j) :
    (pathMap k m (basisPath k m i j hij)).val = Matrix.single i j 1 := rfl

theorem pathMap_surjective : Function.Surjective (pathMap k m) := by
  intro M
  refine ⟨⟨M.val, ?_⟩, rfl⟩
  intro i j h
  exact M.property i j (lt_of_not_ge h)
theorem pathMap_injective : Function.Injective (pathMap k m) := by
  intro f g h
  apply IncidenceAlgebra.ext
  intro i j _
  exact congrFun (congrFun (congrArg Subtype.val h) i) j

def relations : Ideal (PathAlgebra k m) := ⊥
theorem relations_vanish (x : PathAlgebra k m) (hx : x ∈ relations k m) :
    pathMap k m x = 0 := by
  have : x = 0 := hx
  simp [this]
abbrev Path := {p : Fin m × Fin m // p.1 ≤ p.2}
def pathCoordinates : PathAlgebra k m ≃ₗ[k] (Path m → k) where
  toFun f p := f p.val.1 p.val.2
  invFun v := ⟨fun i j => if h : i ≤ j then v ⟨(i,j), h⟩ else 0, by
    intro i j h; simp [h]⟩
  left_inv f := by
    apply IncidenceAlgebra.ext
    intro i j h
    simp [h]
  right_inv v := by funext p; simp [p.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def pathEndEquiv : PathAlgebra k m ≃ₗ[k] End k m :=
  LinearEquiv.ofBijective (pathMap k m).toLinearMap
    ⟨pathMap_injective k m, pathMap_surjective k m⟩
def relationSpace : Submodule k (PathAlgebra k m) := ⊥
abbrev Presented := PathAlgebra k m ⧸ relationSpace k m

theorem path_dimension : Module.finrank k (PathAlgebra k m) = Fintype.card (Path m) := by
  rw [(pathCoordinates k m).finrank_eq]
  simp
theorem end_dimension : Module.finrank k (End k m) = Fintype.card (Path m) := by
  rw [← (pathEndEquiv k m).finrank_eq]
  exact path_dimension k m
theorem presented_dimension : Module.finrank k (Presented k m) = Fintype.card (Path m) := by
  rw [((relationSpace k m).quotEquivOfEqBot rfl).finrank_eq]
  exact path_dimension k m
theorem C2_certificate :
    Function.Surjective (pathMap k m) ∧
    (∀ x ∈ relations k m, pathMap k m x = 0) ∧
    Module.finrank k (Presented k m) = Module.finrank k (End k m) ∧
    Module.finrank k (End k m) = Fintype.card (Path m) :=
  ⟨pathMap_surjective k m, relations_vanish k m,
    (presented_dimension k m).trans (end_dimension k m).symm, end_dimension k m⟩

theorem corner_formula (v : Fin m) (M : End k m) :
    Matrix.single v v (1 : k) * M.val * Matrix.single v v 1 =
      Matrix.single v v (M.val v v) := by simp

theorem corner_scalar_mem (v : Fin m) (a : k) :
    Matrix.single v v a ∈ endAlgebra k m := by
  intro i j h
  simp only [Matrix.single_apply]
  split_ifs with he
  · obtain ⟨rfl, rfl⟩ := he
    exact (lt_irrefl _ h).elim
  · rfl

theorem corner_local (v : Fin m) (a : k) :
    ∃ b : k,
      (Matrix.single v v a * Matrix.single v v b = Matrix.single v v 1 ∧
       Matrix.single v v b * Matrix.single v v a = Matrix.single v v 1) ∨
      (Matrix.single v v (1-a) * Matrix.single v v b = Matrix.single v v 1 ∧
       Matrix.single v v b * Matrix.single v v (1-a) = Matrix.single v v 1) := by
  by_cases ha : a = 0
  · exact ⟨1, Or.inr (by simp [ha])⟩
  · exact ⟨a⁻¹, Or.inl (by simp [ha])⟩
end Chain

namespace N3
/-!
C1: old database IDs 1–5. Escaping translates: 1↦8, 3↦7, 4↦21.
For 4 the lemma gives (-1,π) in C₁⊕R; permute the summands and negate
C₁ to obtain the database embedding (π,1) in R⊕C₁.
Quiver order: A=6 → B=7 → D=21 → C=8 → E=9.
Matrix order is reversed: E,C,D,B,A, with D's extra C₁ coordinate last.
-/
def oldObjects : List DBObject := N2.oldObjects ++ N2.newObjects
def newObjects : List DBObject :=
  [⟨6, [], [3], []⟩, ⟨7, [1], [3], [[some 2]]⟩,
   ⟨21, [2], [3,1], [[some 1,some 0]]⟩,
   ⟨8, [2], [3], [[some 1]]⟩, ⟨9, [3], [3], [[some 0]]⟩]
def escapingTranslateIDs : List (Nat × Nat) := [(1,8),(3,7),(4,21)]
def remainingIDs : List Nat := [6,7,8,9,21].filter
  (fun i => !(newObjects.map DBObject.id).contains i)
theorem no_remaining_objects : remainingIDs = [] := by decide
variable (k : Type*) [Field k]
abbrev End := Chain.End k 5
abbrev PathAlgebra := Chain.PathAlgebra k 5
abbrev pathMap := Chain.pathMap k 5
abbrev Presented := Chain.Presented k 5
theorem path_count : Fintype.card (Chain.Path 5) = 15 := by decide
theorem C2_certificate :
    Function.Surjective (pathMap k) ∧
    (∀ x ∈ Chain.relations k 5, pathMap k x = 0) ∧
    Module.finrank k (Presented k) = Module.finrank k (End k) ∧
    Module.finrank k (End k) = 15 := by
  simpa [path_count] using Chain.C2_certificate k 5

def arrow (i : Fin 4) : PathAlgebra k :=
  Chain.basisPath k 5 i.castSucc i.succ (by change i.val ≤ i.val+1; omega)
theorem arrow_image (i : Fin 4) :
    (pathMap k (arrow k i)).val = Matrix.single i.castSucc i.succ 1 := rfl

theorem corner_local (v : Fin 5) (a : k) :
    ∃ b : k,
      (Matrix.single v v a * Matrix.single v v b = Matrix.single v v 1 ∧
       Matrix.single v v b * Matrix.single v v a = Matrix.single v v 1) ∨
      (Matrix.single v v (1-a) * Matrix.single v v b = Matrix.single v v 1 ∧
       Matrix.single v v b * Matrix.single v v (1-a) = Matrix.single v v 1) :=
  Chain.corner_local k 5 v a

section Reduction
variable {R : Type*} [CommRing R] (π : R) (ρ : R →+* k)
variable (hπ : ρ π = 0) (hπ3 : π^3 = 0)
variable (ann : ∀ r : R, π^2 * r = 0 ↔ ρ r = 0)
variable (residue_surj : Function.Surjective ρ)
abbrev AmbientMatrix := Matrix (Fin 6) (Fin 6) R

/-- L represents a map on R⁵⊕C₁: the last input coordinate is modulo π.
The condition says the relation πe₅ maps into the same relation module. -/
def Descends (L : AmbientMatrix (R := R)) : Prop :=
  ∀ i : Fin 5, π * L i.castSucc 5 = 0

/-- Preimage in R⁶ of the embedded source in R⁵⊕C₁.
The last congruence encodes D: C₂ → R⊕C₁, t ↦ (πt,t mod π).
The unconstrained coordinate 0 is E's full source R. -/
def Source (u : Fin 6 → R) : Prop :=
  u 4 = 0 ∧ ∃ b c d : R,
    u 1 = π*b ∧ u 2 = π*c ∧ u 3 = π^2*d ∧ ρ (u 5) = ρ c

def Raw (L : AmbientMatrix (R := R)) : Prop :=
  Descends π L ∧ ∀ u, Source k π ρ u → Source k π ρ (L.mulVec u)
def reduce (L : AmbientMatrix (R := R)) : Chain.Mat k 5 :=
  fun i j => ρ (L i.castSucc j.castSucc)

include ann in
theorem rho_of_annpi {a : R} (ha : π*a=0) : ρ a=0 := by
  apply (ann a).mp
  calc π^2*a = π*(π*a) := by ring
       _ = 0 := by rw [ha, mul_zero]

include ann in
theorem rho_of_pi_eq {a b : R} (hab : a*π=π*b) (hb : ρ b=0) : ρ a=0 := by
  apply (ann a).mp
  have hz := (ann b).mpr hb
  linear_combination π * hab + hz

include ann hπ3 in
theorem rho_of_pi_add {a p b : R} (hab : a*π+p=π^2*b) (hp : π*p=0) : ρ a=0 := by
  apply (ann a).mp
  linear_combination π * hab - hp + b * hπ3

include ann hπ hπ3 in
/-- The raw commuting-square calculation forces precisely an upper triangular
residue matrix. In particular the extra C₁ in D is not discarded prematurely. -/
theorem raw_reduces (L : AmbientMatrix (R := R)) (hL : Raw k π ρ L) :
    reduce k ρ L ∈ Chain.endAlgebra k 5 := by
  obtain ⟨hd,hp⟩ := hL
  have h0 := hp ![1,0,0,0,0,0] (by
    refine ⟨rfl,0,0,0,?_,?_,?_,?_⟩ <;> simp)
  have h1 := hp ![0,π,0,0,0,0] (by
    refine ⟨rfl,1,0,0,?_,?_,?_,?_⟩ <;> simp)
  have h2 := hp ![0,0,π,0,0,1] (by
    refine ⟨rfl,0,1,0,?_,?_,?_,?_⟩ <;> simp)
  have h3 := hp ![0,0,0,π^2,0,0] (by
    refine ⟨rfl,0,0,1,?_,?_,?_,?_⟩ <;> simp)
  simp only [Source, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Finset.univ_eq_empty, Finset.sum_empty,
    mul_zero, mul_one, zero_add, add_zero] at h0 h1 h2 h3
  obtain ⟨h40,b0,c0,d0,h10,h20,h30,h50⟩ := h0
  obtain ⟨h41,b1,c1,d1,h11,h21,h31,h51⟩ := h1
  obtain ⟨h42,b2,c2,d2,h12,h22,h32,h52⟩ := h2
  obtain ⟨h43,b3,c3,d3,h13,h23,h33,h53⟩ := h3
  have z10 : ρ (L 1 0)=0 := by simp [h10,hπ]
  have z20 : ρ (L 2 0)=0 := by simp [h20,hπ]
  have z30 : ρ (L 3 0)=0 := by simp [h30,hπ]
  have z40 : ρ (L 4 0)=0 := by simp [h40]
  have z21 : ρ (L 2 1)=0 := rho_of_pi_eq k π ρ ann h21 (by simpa [hπ] using h51.symm)
  have z31 : ρ (L 3 1)=0 :=
    rho_of_pi_add k π ρ hπ3 ann (p := 0) (b := d1) (by simpa using h31) (by simp)
  have z41 : ρ (L 4 1)=0 := rho_of_annpi k π ρ ann (by simpa [mul_comm] using h41)
  have z32 : ρ (L 3 2)=0 := rho_of_pi_add k π ρ hπ3 ann h32 (hd 3)
  have z42 : ρ (L 4 2)=0 :=
    rho_of_pi_add k π ρ hπ3 ann (b := 0) (by simpa using h42) (hd 4)
  have z43 : ρ (L 4 3)=0 := (ann _).mp (by simpa [mul_comm] using h43)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [reduce]

/-- Equality of ambient representatives in R⁵⊕k. -/
def AmbientEq (u v : Fin 6 → R) : Prop :=
  (∀ i : Fin 5, u i.castSucc = v i.castSucc) ∧ ρ (u 5)=ρ (v 5)

include hπ in
/-- Descent is exactly well-definedness on the ambient module, checked on
representatives. `ker_pi` is the defining kernel property of the residue map. -/
theorem descends_iff_well_defined
    (ker_pi : ∀ r : R, ρ r=0 ↔ ∃ t, r=π*t)
    (L : AmbientMatrix (R := R)) :
    Descends π L ↔ ∀ u v, AmbientEq k ρ u v →
      AmbientEq k ρ (L.mulVec u) (L.mulVec v) := by
  constructor
  · intro hd u v huv
    obtain ⟨hu,hv⟩ := huv
    have hz : ρ (u 5-v 5)=0 := by rw [map_sub,hv,sub_self]
    obtain ⟨t,ht⟩ := (ker_pi _).mp hz
    constructor
    · intro i
      have hh : L i.castSucc 5 * u 5 = L i.castSucc 5 * v 5 := by
        apply sub_eq_zero.mp
        rw [← mul_sub,ht,← mul_assoc,mul_comm (L i.castSucc 5) π,hd i,zero_mul]
      simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_castSucc (n := 5)]
      refine congrArg₂ (· + ·) ?_ hh
      apply Finset.sum_congr rfl
      intro j _
      rw [hu j]
    · simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_castSucc (n := 5),map_add,map_mul,map_sum]
      refine congrArg₂ (· + ·) ?_ (congrArg (fun x => ρ (L 5 (Fin.last 5))*x) hv)
      apply Finset.sum_congr rfl
      intro j _
      rw [hu j]
  · intro hw i
    have h := (hw ![0,0,0,0,0,π] 0 (by
      constructor
      · intro j; fin_cases j <;> rfl
      · simp [hπ])).1 i
    simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,mul_comm] using h

/-- π² annihilates the final C₁ output coordinate automatically.
Thus these six input-column tests are exactly π² times the represented map. -/
def Equivalent (L M : AmbientMatrix (R := R)) : Prop :=
  ∀ (i : Fin 5) (j : Fin 6), π^2 * (L i.castSucc j - M i.castSucc j) = 0

include hπ in
/-- The entrywise quotient test is equivalent to π² annihilating the represented
map on every ambient input, including its torsion coordinate. -/
theorem annihilator_test (L M : AmbientMatrix (R := R)) :
    Equivalent π L M ↔ ∀ u, AmbientEq k ρ (π^2 • ((L-M).mulVec u)) 0 := by
  constructor
  · intro h u
    constructor
    · intro i
      change π^2 * (∑ j, (L i.castSucc j-M i.castSucc j)*u j)=0
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j _
      rw [← mul_assoc,h i j,zero_mul]
    · simp [hπ]
  · intro h i j
    have hi := (h (Pi.single j 1)).1 i
    simpa [Matrix.mulVec,dotProduct,Pi.single_apply] using hi

include ann in
theorem quotient_exact (L M : AmbientMatrix (R := R))
    (hL : Descends π L) (hM : Descends π M) :
    Equivalent π L M ↔ reduce k ρ L = reduce k ρ M := by
  constructor
  · intro h
    ext i j
    apply sub_eq_zero.mp
    simpa [reduce] using (ann _).mp (h i j.castSucc)
  · intro h i j
    apply (ann _).mpr
    rw [map_sub, sub_eq_zero]
    by_cases hj : j.val < 5
    · let j' : Fin 5 := ⟨j.val,hj⟩
      have he : j'.castSucc = j := Fin.ext rfl
      rw [← he]
      exact congrFun (congrFun h i) j'
    · have he : j=5 := by apply Fin.ext; simp; omega
      subst j
      rw [rho_of_annpi k π ρ ann (hL i), rho_of_annpi k π ρ ann (hM i)]

theorem reduce_add (L M : AmbientMatrix (R := R)) :
    reduce k ρ (L+M) = reduce k ρ L + reduce k ρ M := by ext i j; exact map_add ρ _ _
theorem reduce_scalar (r : R) (L : AmbientMatrix (R := R)) :
    reduce k ρ (r • L) = ρ r • reduce k ρ L := by ext i j; exact map_mul ρ _ _
include ann in
theorem reduce_mul (L M : AmbientMatrix (R := R)) (hL : Descends π L) :
    reduce k ρ (L*M) = reduce k ρ L * reduce k ρ M := by
  ext i j
  simp [reduce, Matrix.mul_apply, map_mul, Fin.sum_univ_castSucc,
    rho_of_annpi k π ρ ann (hL i)]

/-- A lift of a triangular 5×5 matrix to the actual six ambient coordinates.
D's last coordinate must receive its diagonal coefficient, not zero. -/
def liftMatrix (T : Matrix (Fin 5) (Fin 5) R) : AmbientMatrix (R := R) :=
  fun i j => if hi : i.val < 5 then
    if hj : j.val < 5 then T ⟨i.val,hi⟩ ⟨j.val,hj⟩ else 0
  else if j=5 then T 2 2 else 0

include hπ in
theorem lift_raw (T : Matrix (Fin 5) (Fin 5) R)
    (hT : ∀ i j, j < i → T i j = 0) : Raw k π ρ (liftMatrix T) := by
  constructor
  · intro i; simp [liftMatrix, i.isLt]
  · rintro u ⟨hu4,b,c,d,hu1,hu2,hu3,hu5⟩
    have ht10 := hT 1 0 (by decide)
    have ht20 := hT 2 0 (by decide)
    have ht21 := hT 2 1 (by decide)
    have ht30 := hT 3 0 (by decide)
    have ht31 := hT 3 1 (by decide)
    have ht32 := hT 3 2 (by decide)
    have ht40 := hT 4 0 (by decide)
    have ht41 := hT 4 1 (by decide)
    have ht42 := hT 4 2 (by decide)
    have ht43 := hT 4 3 (by decide)
    refine ⟨?_, T 1 1*b + T 1 2*c + π*T 1 3*d,
      T 2 2*c + π*T 2 3*d, T 3 3*d, ?_, ?_, ?_, ?_⟩
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, liftMatrix,
      hu1,hu2,hu3,hu4,hu5,ht10,ht20,ht21,ht30,ht31,ht32,ht40,ht41,ht42,ht43,hπ]
    all_goals ring

/-- Explicit ambient matrices for the four quiver arrows. -/
def arrowAmbient (i : Fin 4) : AmbientMatrix (R := R) :=
  liftMatrix (Matrix.single i.castSucc i.succ 1)

include hπ in
theorem arrowAmbient_raw (i : Fin 4) : Raw k π ρ (arrowAmbient (R := R) i) := by
  apply lift_raw k π ρ hπ
  intro a b h
  simp only [Matrix.single_apply]
  split_ifs with he
  · obtain ⟨rfl,rfl⟩ := he
    have hi : i.castSucc ≤ i.succ := by change i.val ≤ i.val+1; omega
    exact (not_lt_of_ge hi h).elim
  · rfl

theorem arrowAmbient_image (i : Fin 4) :
    reduce k ρ (arrowAmbient (R := R) i) = (pathMap k (arrow k i)).val := by
  rw [arrow_image]
  ext a b
  simp [reduce,arrowAmbient,liftMatrix,a.isLt,b.isLt,Matrix.single]

include residue_surj hπ in
theorem reduce_surjective (T : End k) :
    ∃ L : AmbientMatrix (R := R), Raw k π ρ L ∧ reduce k ρ L = T.val := by
  classical
  choose lift hlift using residue_surj
  let U : Matrix (Fin 5) (Fin 5) R := fun i j => if i ≤ j then lift (T.val i j) else 0
  have hU : ∀ i j, j < i → U i j=0 := by intro i j h; simp [U,not_le_of_gt h]
  refine ⟨liftMatrix U, lift_raw k π ρ hπ U hU, ?_⟩
  ext i j
  by_cases h : i ≤ j
  · simp [reduce,liftMatrix,U,i.isLt,j.isLt,h,hlift]
  · simp [reduce,liftMatrix,U,i.isLt,j.isLt,h,T.property i j (lt_of_not_ge h)]

/-- Equivalence classes of actual raw maps; `quotient_exact` and
`annihilator_test` identify the relation with the prescribed ideal quotient. -/
def rawSetoid : Setoid {L : AmbientMatrix (R := R) // Raw k π ρ L} :=
  Setoid.ker (fun L => reduce k ρ L.val)

def quotientToEnd : Quotient (rawSetoid k π ρ) → End k :=
  Quotient.lift (fun L =>
    ⟨reduce k ρ L.val, raw_reduces k π ρ hπ hπ3 ann L.val L.property⟩)
    (by intro L M h; exact Subtype.ext h)

include residue_surj in
theorem quotientToEnd_bijective :
    Function.Bijective (quotientToEnd k π ρ hπ hπ3 ann) := by
  constructor
  · intro q q' h
    induction q,q' using Quotient.inductionOn₂ with
    | h L M =>
      apply Quotient.sound
      exact congrArg Subtype.val h
  · intro T
    obtain ⟨L,hL,he⟩ := reduce_surjective k π ρ hπ residue_surj T
    exact ⟨Quotient.mk _ ⟨L,hL⟩,Subtype.ext he⟩

/-- The user observation: π acts by zero on this ideal quotient. -/
theorem pi_scalar_killed (L : AmbientMatrix (R := R)) (h : π^3=0) :
    Equivalent π (π • L) 0 := by
  intro i j
  change π^2 * (π * L i.castSucc j - 0)=0
  calc π^2 * (π * L i.castSucc j - 0) = π^3 * L i.castSucc j := by ring
       _ = 0 := by rw [h,zero_mul]
end Reduction
end N3

namespace N4
variable (k : Type*) [Field k]
section ScalarHom
variable {R : Type*} [CommRing R] (π : R) (ρ : R →+* k)
variable (hπ4 : π^4=0) (ann : ∀ x : R, π^3*x=0 ↔ ρ x=0)
def vertexIDs : Fin 9 → Nat := ![14,13,23,12,25,24,22,11,10]
def a : Fin 9 → Nat := ![0,1,1,2,1,2,2,3,4]
def ell : Fin 9 → Nat := ![0,0,1,0,2,2,1,0,0]
def b : Fin 9 → Nat := ![0,0,0,0,0,1,0,0,0]
def Allowed (i j : Fin 9) : Prop := i ≤ j ∧ ¬(i=3 ∧ j=4)
instance (i j : Fin 9) : Decidable (Allowed i j) := inferInstanceAs (Decidable (_ ∧ _))
/-- A lift of an ambient map R⊕C_ell(j) → R⊕C_ell(i).
The last three entries witness descent and preservation of the cyclic source.
All equations are literal equations in R, including the torsion congruences. -/
structure HomData (i j : Fin 9) where
  r : R
  p : R
  q : R
  d : R
  t : R
  w : R
  v : R
  descent_free : π^(ell j)*p=0
  descent_torsion : π^(ell j)*d=π^(ell i)*w
  source_free : π^(a j)*r+π^(b j)*p=π^(a i)*t
  source_torsion : π^(a j)*q+π^(b j)*d=π^(b i)*t+π^(ell i)*v

include hπ4 ann in
theorem forbidden_1_0 (f : HomData π 1 0) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π^3)*h1 + (π^3)*h3 + (t)*hπ4
include hπ4 ann in
theorem forbidden_2_0 (f : HomData π 2 0) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π^3)*h1 + (π^3)*h3 + (t)*hπ4
include hπ4 ann in
theorem forbidden_3_0 (f : HomData π 3 0) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π^3)*h1 + (π^3)*h3 + (t*π)*hπ4
include hπ4 ann in
theorem forbidden_4_0 (f : HomData π 4 0) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π^3)*h1 + (π^3)*h3 + (t)*hπ4
include hπ4 ann in
theorem forbidden_5_0 (f : HomData π 5 0) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π^3)*h1 + (π^3)*h3 + (t*π)*hπ4
include hπ4 ann in
theorem forbidden_6_0 (f : HomData π 6 0) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π^3)*h1 + (π^3)*h3 + (t*π)*hπ4
include hπ4 ann in
theorem forbidden_7_0 (f : HomData π 7 0) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π^3)*h1 + (π^3)*h3 + (t*π^2)*hπ4
include hπ4 ann in
theorem forbidden_8_0 (f : HomData π 8 0) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π^3)*h1 + (π^3)*h3 + (t*π^3)*hπ4
include hπ4 ann in
theorem forbidden_2_1 (f : HomData π 2 1) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π^2)*h1 + (π^3)*h2 + (π^2)*h3 + ((-1)*π^3)*h4 + (q + w + (-1)*v)*hπ4
include hπ4 ann in
theorem forbidden_3_1 (f : HomData π 3 1) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π^2)*h1 + (π^2)*h3 + (t)*hπ4
include hπ4 ann in
theorem forbidden_4_1 (f : HomData π 4 1) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π^2)*h1 + (π^3)*h2 + (π^2)*h3 + ((-1)*π^3)*h4 + (q + w*π + (-1)*v*π)*hπ4
include hπ4 ann in
theorem forbidden_5_1 (f : HomData π 5 1) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π^2)*h1 + (π^2)*h3 + (t)*hπ4
include hπ4 ann in
theorem forbidden_6_1 (f : HomData π 6 1) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π^2)*h1 + (π^2)*h3 + (t)*hπ4
include hπ4 ann in
theorem forbidden_7_1 (f : HomData π 7 1) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π^2)*h1 + (π^2)*h3 + (t*π)*hπ4
include hπ4 ann in
theorem forbidden_8_1 (f : HomData π 8 1) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π^2)*h1 + (π^2)*h3 + (t*π^2)*hπ4
include hπ4 ann in
theorem forbidden_3_2 (f : HomData π 3 2) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π)*h1 + (π^2)*h3 + (t)*hπ4
include hπ4 ann in
theorem forbidden_4_2 (f : HomData π 4 2) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π)*h1 + (π^2)*h2 + (π^2)*h3 + ((-1)*π^3)*h4 + (q + w + (-1)*v*π)*hπ4
include hπ4 ann in
theorem forbidden_5_2 (f : HomData π 5 2) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π)*h1 + (π^2)*h3 + (t)*hπ4
include hπ4 ann in
theorem forbidden_6_2 (f : HomData π 6 2) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π)*h1 + (π^2)*h3 + (t)*hπ4
include hπ4 ann in
theorem forbidden_7_2 (f : HomData π 7 2) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π)*h1 + (π^2)*h3 + (t*π)*hπ4
include hπ4 ann in
theorem forbidden_8_2 (f : HomData π 8 2) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π)*h1 + (π^2)*h3 + (t*π^2)*hπ4
include hπ4 ann in
theorem forbidden_4_3 (f : HomData π 4 3) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π)*h1 + (π^2)*h2 + (π)*h3 + ((-1)*π^2)*h4 + (q + w + (-1)*v)*hπ4
include hπ4 ann in
theorem forbidden_5_3 (f : HomData π 5 3) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π)*h1 + (π^2)*h2 + (π)*h3 + ((-1)*π^2)*h4 + (q + w + (-1)*v)*hπ4
include hπ4 ann in
theorem forbidden_6_3 (f : HomData π 6 3) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π)*h1 + (π^3)*h2 + (π)*h3 + ((-1)*π^3)*h4 + (w + (-1)*v + q*π)*hπ4
include hπ4 ann in
theorem forbidden_7_3 (f : HomData π 7 3) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π)*h1 + (π)*h3 + (t)*hπ4
include hπ4 ann in
theorem forbidden_8_3 (f : HomData π 8 3) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1)*π)*h1 + (π)*h3 + (t*π)*hπ4
include hπ4 ann in
theorem forbidden_3_4 (f : HomData π 3 4) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1))*h1 + (π^2)*h3 + (t)*hπ4
include hπ4 ann in
theorem forbidden_5_4 (f : HomData π 5 4) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1))*h1 + (π^2)*h3 + (t)*hπ4
include hπ4 ann in
theorem forbidden_6_4 (f : HomData π 6 4) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1))*h1 + (π^2)*h3 + (t)*hπ4
include hπ4 ann in
theorem forbidden_7_4 (f : HomData π 7 4) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1))*h1 + (π^2)*h3 + (t*π)*hπ4
include hπ4 ann in
theorem forbidden_8_4 (f : HomData π 8 4) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1))*h1 + (π^2)*h3 + (t*π^2)*hπ4
include hπ4 ann in
theorem forbidden_6_5 (f : HomData π 6 5) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1))*h1 + (π)*h3 + ((-1)*π^3)*h4 + (d + (-1)*v + q*π)*hπ4
include hπ4 ann in
theorem forbidden_7_5 (f : HomData π 7 5) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1))*h1 + (π)*h3 + (t)*hπ4
include hπ4 ann in
theorem forbidden_8_5 (f : HomData π 8 5) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1))*h1 + (π)*h3 + (t*π)*hπ4
include hπ4 ann in
theorem forbidden_7_6 (f : HomData π 7 6) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1))*h1 + (π)*h3 + (t)*hπ4
include hπ4 ann in
theorem forbidden_8_6 (f : HomData π 8 6) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1))*h1 + (π)*h3 + (t*π)*hπ4
include hπ4 ann in
theorem forbidden_8_7 (f : HomData π 8 7) : ρ f.r=0 := by
  apply (ann f.r).mp
  rcases f with ⟨r,p,q,d,t,w,v,h1,h2,h3,h4⟩
  norm_num [a,b,ell] at h1 h2 h3 h4 ⊢
  linear_combination ((-1))*h1 + (1)*h3 + (t)*hπ4
include hπ4 ann in
theorem hom_reduces (i j : Fin 9) (f : HomData π i j) (h : ¬ Allowed i j) : ρ f.r=0 := by
  fin_cases i <;> fin_cases j <;> try exact (h (by decide)).elim
  all_goals first
    | exact forbidden_1_0 k π ρ hπ4 ann f
    | exact forbidden_2_0 k π ρ hπ4 ann f
    | exact forbidden_3_0 k π ρ hπ4 ann f
    | exact forbidden_4_0 k π ρ hπ4 ann f
    | exact forbidden_5_0 k π ρ hπ4 ann f
    | exact forbidden_6_0 k π ρ hπ4 ann f
    | exact forbidden_7_0 k π ρ hπ4 ann f
    | exact forbidden_8_0 k π ρ hπ4 ann f
    | exact forbidden_2_1 k π ρ hπ4 ann f
    | exact forbidden_3_1 k π ρ hπ4 ann f
    | exact forbidden_4_1 k π ρ hπ4 ann f
    | exact forbidden_5_1 k π ρ hπ4 ann f
    | exact forbidden_6_1 k π ρ hπ4 ann f
    | exact forbidden_7_1 k π ρ hπ4 ann f
    | exact forbidden_8_1 k π ρ hπ4 ann f
    | exact forbidden_3_2 k π ρ hπ4 ann f
    | exact forbidden_4_2 k π ρ hπ4 ann f
    | exact forbidden_5_2 k π ρ hπ4 ann f
    | exact forbidden_6_2 k π ρ hπ4 ann f
    | exact forbidden_7_2 k π ρ hπ4 ann f
    | exact forbidden_8_2 k π ρ hπ4 ann f
    | exact forbidden_4_3 k π ρ hπ4 ann f
    | exact forbidden_5_3 k π ρ hπ4 ann f
    | exact forbidden_6_3 k π ρ hπ4 ann f
    | exact forbidden_7_3 k π ρ hπ4 ann f
    | exact forbidden_8_3 k π ρ hπ4 ann f
    | exact forbidden_3_4 k π ρ hπ4 ann f
    | exact forbidden_5_4 k π ρ hπ4 ann f
    | exact forbidden_6_4 k π ρ hπ4 ann f
    | exact forbidden_7_4 k π ρ hπ4 ann f
    | exact forbidden_8_4 k π ρ hπ4 ann f
    | exact forbidden_6_5 k π ρ hπ4 ann f
    | exact forbidden_7_5 k π ρ hπ4 ann f
    | exact forbidden_8_5 k π ρ hπ4 ann f
    | exact forbidden_7_6 k π ρ hπ4 ann f
    | exact forbidden_8_6 k π ρ hπ4 ann f
    | exact forbidden_8_7 k π ρ hπ4 ann f
def witness : Fin 9 → Fin 9 → Fin 6 → R := ![
  ![![0,1,0,1,0,0],![0,1,0,π,0,0],![0,1,0,π,0,0],![0,1,0,π^2,0,0],![0,1,0,π,0,0],![0,1,0,π^2,0,0],![0,1,0,π^2,0,0],![0,1,0,π^3,0,0],![0,0,0,0,0,0]],
  ![![0,0,0,0,0,0],![0,0,1,1,1,0],![0,0,1,1,π,0],![0,0,π,π,π,0],![0,0,1,1,π^2,0],![0,0,1,π,π^2,0],![0,0,π,π,π^2,0],![0,0,π^2,π^2,π^2,0],![0,0,0,0,0,0]],
  ![![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,1,1,1,0],![0,0,π,π,1,0],![0,0,1,1,π,0],![0,0,1,π,π,0],![0,0,π,π,π,0],![0,0,π^2,π^2,π,0],![0,0,0,0,0,0]],
  ![![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,1,1,1,0],![0,0,0,0,0,0],![0,0,0,1,0,(-1)],![0,0,1,1,π,0],![0,0,π,π,π,0],![0,0,0,0,0,0]],
  ![![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,1,1,1,0],![0,0,1,π,1,0],![0,0,π,π,1,0],![0,0,π^2,π^2,1,0],![0,0,0,0,0,0]],
  ![![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,1,1,1,0],![0,0,π,1,1,0],![0,0,π^2,π,1,0],![0,0,0,0,0,0]],
  ![![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,1,1,1,0],![0,0,π,π,1,0],![0,0,0,0,0,0]],
  ![![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,1,1,1,0],![0,0,0,0,0,0]],
  ![![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0]]
]
include hπ4 in
def homLift (i j : Fin 9) (h : Allowed i j) : HomData π i j where
  r := 1
  p := witness π i j 0
  q := witness π i j 1
  d := witness π i j 2
  t := witness π i j 3
  w := witness π i j 4
  v := witness π i j 5
  descent_free := by
    fin_cases i <;> fin_cases j <;> norm_num [Allowed] at h
    all_goals norm_num [witness,a,b,ell] <;> ring_nf <;> simp_all
  descent_torsion := by
    fin_cases i <;> fin_cases j <;> norm_num [Allowed] at h
    all_goals norm_num [witness,a,b,ell] <;> ring_nf <;> simp_all
  source_free := by
    fin_cases i <;> fin_cases j <;> norm_num [Allowed] at h
    all_goals norm_num [witness,a,b,ell] <;> ring_nf <;> simp_all
  source_torsion := by
    fin_cases i <;> fin_cases j <;> norm_num [Allowed] at h
    all_goals norm_num [witness,a,b,ell] <;> ring_nf <;> simp_all

end ScalarHom
end N4

set_option maxHeartbeats 5000000
namespace N4
variable (k : Type*) [Field k]
abbrev M8 := Matrix (Fin 8) (Fin 8) k
abbrev M9 := Matrix (Fin 9) (Fin 9) k

theorem allowed_trans {i j l : Fin 9} (h : Allowed i j) (g : Allowed j l) : Allowed i l := by
  rcases h with ⟨hij,hij'⟩
  rcases g with ⟨hjl,hjl'⟩
  refine ⟨le_trans hij hjl, ?_⟩
  rintro ⟨rfl,rfl⟩
  have hj : j=3 ∨ j=4 := by omega
  rcases hj with rfl | rfl
  · exact hjl' ⟨rfl,rfl⟩
  · exact hij' ⟨rfl,rfl⟩

def endAlgebra : Subalgebra k (M9 k) where
  carrier := {M | ∀ i j, ¬ Allowed i j → M i j=0}
  zero_mem' := by simp
  add_mem' := by intro M N hM hN i j h; simp [hM i j h,hN i j h]
  one_mem' := by
    intro i j h
    have hij : i≠j := by rintro rfl; exact h ⟨le_rfl,by omega⟩
    simp [hij]
  mul_mem' := by
    intro M N hM hN i j hij
    change ∑ l, M i l*N l j=0
    apply Finset.sum_eq_zero
    intro l _
    by_cases h : Allowed i l
    · have hn : ¬Allowed l j := fun g => hij (allowed_trans h g)
      simp [hN l j hn]
    · simp [hM i l h]
  algebraMap_mem' := by
    intro r i j h
    have hij : i≠j := by rintro rfl; exact h ⟨le_rfl,by omega⟩
    simp [Algebra.algebraMap_eq_smul_one,hij]
abbrev End := endAlgebra k

/-- Common subpaths stay entirely before or entirely after the diamond.
Paths crossing the diamond have two independent coefficients in kQ. -/
def Shared (i j : Fin 8) : Prop := j ≤ 2 ∨ 4 ≤ i
instance (i j : Fin 8) : Decidable (Shared i j) := inferInstanceAs (Decidable (_ ∨ _))

def pathAlgebra : Subalgebra k (M8 k × M8 k) where
  carrier := {P | P.1 ∈ Chain.endAlgebra k 8 ∧ P.2 ∈ Chain.endAlgebra k 8 ∧
    ∀ i j, Shared i j → P.1 i j=P.2 i j}
  zero_mem' := by simp
  add_mem' := by
    rintro P Q ⟨hp,hp',hs⟩ ⟨hq,hq',ht⟩
    refine ⟨(Chain.endAlgebra k 8).add_mem hp hq,(Chain.endAlgebra k 8).add_mem hp' hq',?_⟩
    intro i j h
    change P.1 i j+Q.1 i j=P.2 i j+Q.2 i j
    rw [hs i j h,ht i j h]
  one_mem' := by exact ⟨(Chain.endAlgebra k 8).one_mem,(Chain.endAlgebra k 8).one_mem,by intros; rfl⟩
  mul_mem' := by
    rintro P Q ⟨hp,hp',hs⟩ ⟨hq,hq',ht⟩
    refine ⟨(Chain.endAlgebra k 8).mul_mem hp hq,(Chain.endAlgebra k 8).mul_mem hp' hq',?_⟩
    intro i j hij
    change (∑ l, P.1 i l*Q.1 l j)=(∑ l, P.2 i l*Q.2 l j)
    apply Finset.sum_congr rfl
    intro l _
    rcases hij with hj | hi
    · by_cases hl : l ≤ 2
      · rw [hs i l (Or.inl hl),ht l j (Or.inl hj)]
      · have hlj : j < l := by omega
        rw [hq l j hlj,hq' l j hlj,mul_zero,mul_zero]
    · by_cases hl : 4 ≤ l
      · rw [hs i l (Or.inr hi),ht l j (Or.inr hl)]
      · have hli : l < i := by omega
        rw [hp i l hli,hp' i l hli,zero_mul,zero_mul]
  algebraMap_mem' := by
    intro r
    exact ⟨(Chain.endAlgebra k 8).algebraMap_mem r,
      (Chain.endAlgebra k 8).algebraMap_mem r,by intros; rfl⟩
abbrev PathAlgebra := pathAlgebra k

lemma lower_left (P : PathAlgebra k) (i j : Fin 8) (h : j < i) : P.val.1 i j=0 := P.property.1 i j h
lemma lower_right (P : PathAlgebra k) (i j : Fin 8) (h : j < i) : P.val.2 i j=0 := P.property.2.1 i j h
lemma right_shared (P : PathAlgebra k) (i j : Fin 8) (h : Shared i j) : P.val.2 i j=P.val.1 i j :=
  (P.property.2.2 i j h).symm
lemma end_zero (T : End k) (i j : Fin 9) (h : ¬Allowed i j) : T.val i j=0 := T.property i j h

@[simp] lemma shared_col0 (P : PathAlgebra k) (i : Fin 8) : P.val.2 i 0=P.val.1 i 0 := right_shared k P i 0 (Or.inl (by decide))
@[simp] lemma shared_col1 (P : PathAlgebra k) (i : Fin 8) : P.val.2 i 1=P.val.1 i 1 := right_shared k P i 1 (Or.inl (by decide))
@[simp] lemma shared_col2 (P : PathAlgebra k) (i : Fin 8) : P.val.2 i 2=P.val.1 i 2 := right_shared k P i 2 (Or.inl (by decide))
@[simp] lemma shared_row4 (P : PathAlgebra k) (j : Fin 8) : P.val.2 4 j=P.val.1 4 j := right_shared k P 4 j (Or.inr (by decide))
@[simp] lemma shared_row5 (P : PathAlgebra k) (j : Fin 8) : P.val.2 5 j=P.val.1 5 j := right_shared k P 5 j (Or.inr (by decide))
@[simp] lemma shared_row6 (P : PathAlgebra k) (j : Fin 8) : P.val.2 6 j=P.val.1 6 j := right_shared k P 6 j (Or.inr (by decide))
@[simp] lemma shared_row7 (P : PathAlgebra k) (j : Fin 8) : P.val.2 7 j=P.val.1 7 j := right_shared k P 7 j (Or.inr (by decide))

def compress : Fin 9 → Fin 8 := ![0,1,2,3,3,4,5,6,7]
def Cross (i j : Fin 8) : Prop := i < 3 ∧ 4 ≤ j
instance (i j : Fin 8) : Decidable (Cross i j) := inferInstanceAs (Decidable (_ ∧ _))
def phi (P : M8 k × M8 k) : M9 k := fun i j =>
  if Allowed i j then
    if i=3 ∨ j=3 then P.1 (compress i) (compress j)
    else if i=4 ∨ j=4 then P.2 (compress i) (compress j)
    else if i < 3 ∧ 5 ≤ j then P.1 (compress i) (compress j)+P.2 (compress i) (compress j)
    else P.1 (compress i) (compress j)
  else 0

def pathMap : PathAlgebra k →ₐ[k] End k where
  toFun P := ⟨phi k P.val, by
    intro i j h
    simp only [phi,if_neg h]⟩
  map_zero' := by apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply,Pi.add_apply,compress,Allowed,phi]
  map_add' P Q := by
    apply Subtype.ext
    change phi k (P.val+Q.val)=phi k P.val+phi k Q.val
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply,Pi.add_apply,compress,Allowed,phi] <;> ring
  map_one' := by
    apply Subtype.ext; ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply,Pi.add_apply,compress,Allowed,phi,Matrix.one_apply]
  map_mul' P Q := by
    apply Subtype.ext
    change phi k (P.val.1*Q.val.1,P.val.2*Q.val.2)=phi k P.val * phi k Q.val
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp only [Matrix.mul_apply,Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
    all_goals simp [Matrix.add_apply,Pi.add_apply,compress,Allowed,phi,Matrix.mul_apply,Fin.sum_univ_succ,lower_left,lower_right,right_shared,Shared] <;> ring
  commutes' r := by
    apply Subtype.ext; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply,Pi.add_apply,compress,Allowed,phi,Algebra.algebraMap_eq_smul_one,Matrix.one_apply]

def leftIndex : Fin 8 → Fin 9 := ![0,1,2,3,5,6,7,8]
def rightIndex : Fin 8 → Fin 9 := ![0,1,2,4,5,6,7,8]
def sectionPair (T : M9 k) : M8 k × M8 k :=
  (fun i j => if i ≤ j then T (leftIndex i) (leftIndex j) else 0,
   fun i j => if i ≤ j ∧ ¬Cross i j then T (rightIndex i) (rightIndex j) else 0)

def sectionMap (T : End k) : PathAlgebra k := ⟨sectionPair k T.val, by
  constructor
  · intro i j h; fin_cases i <;> fin_cases j <;> norm_num at h
    all_goals simp [Matrix.add_apply,Pi.add_apply,leftIndex,rightIndex,Cross,compress,Allowed,sectionPair,leftIndex,rightIndex,Cross]
  constructor
  · intro i j h; fin_cases i <;> fin_cases j <;> norm_num at h
    all_goals simp [Matrix.add_apply,Pi.add_apply,leftIndex,rightIndex,Cross,compress,Allowed,sectionPair,leftIndex,rightIndex,Cross]
  · intro i j h
    fin_cases i <;> fin_cases j <;> norm_num [Shared] at h
    all_goals simp [Matrix.add_apply,Pi.add_apply,leftIndex,rightIndex,Cross,compress,Allowed,sectionPair,leftIndex,rightIndex,Cross]⟩

theorem section_right_inverse (T : End k) : pathMap k (sectionMap k T)=T := by
  apply Subtype.ext
  ext i j
  change phi k (sectionPair k T.val) i j=T.val i j
  by_cases h : Allowed i j
  · fin_cases i <;> fin_cases j <;> norm_num [Allowed] at h
    all_goals simp [phi,compress,Allowed,sectionPair,leftIndex,rightIndex,Cross]
  · simp only [phi,if_neg h]
    exact (T.property i j h).symm

theorem pathMap_surjective : Function.Surjective (pathMap k) :=
  fun T => ⟨sectionMap k T,section_right_inverse k T⟩

abbrev EndCoord := {p : Fin 9 × Fin 9 // Allowed p.1 p.2}
theorem end_count : Fintype.card EndCoord = 44 := by decide

def endCoordinates : End k ≃ₗ[k] (EndCoord → k) where
  toFun T p := T.val p.val.1 p.val.2
  invFun v := ⟨fun i j => if h : Allowed i j then v ⟨(i,j),h⟩ else 0, by
    intro i j h; simp [h]⟩
  left_inv T := by
    apply Subtype.ext; ext i j
    by_cases h : Allowed i j
    · simp [h]
    · simp [h,T.property i j h]
  right_inv v := by funext p; simp [p.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem end_dimension : Module.finrank k (End k)=44 := by
  rw [(endCoordinates k).finrank_eq]
  simp [end_count]

/-- Independent coefficients for all 56 actual quiver paths. The right-hand
copy of a shared path is omitted; the two diamond paths remain distinct. -/
abbrev PathCoord := {p : Bool × Fin 8 × Fin 8 //
  p.2.1  ≤  p.2.2 ∧ (p.1=false ∨ ¬Shared p.2.1 p.2.2)}
theorem path_count : Fintype.card PathCoord=56 := by decide

def crossRow : Fin 8 → Fin 3 := ![0,1,2,0,0,0,0,0]
def crossCol : Fin 8 → Fin 4 := ![0,0,0,0,0,1,2,3]
def relationPair (v : Fin 3 → Fin 4 → k) : M8 k × M8 k :=
  (fun i j => if Cross i j then v (crossRow i) (crossCol j) else 0,
   fun i j => if Cross i j then -(v (crossRow i) (crossCol j)) else 0)

def relationCombination (v : Fin 3 → Fin 4 → k) : PathAlgebra k :=
  ⟨relationPair k v, by
    constructor
    · intro i j h; fin_cases i <;> fin_cases j <;> norm_num at h
      all_goals simp [relationPair,Cross]
    constructor
    · intro i j h; fin_cases i <;> fin_cases j <;> norm_num at h
      all_goals simp [relationPair,Cross]
    · intro i j h; fin_cases i <;> fin_cases j <;> norm_num [Shared] at h
      all_goals simp [relationPair,Cross]⟩

def kernelCoefficients (P : PathAlgebra k) : Fin 3 → Fin 4 → k :=
  fun i j => -(P.val.2 ⟨i.val,by omega⟩ ⟨j.val+4,by omega⟩)

theorem normal_form_pair (P : PathAlgebra k) :
    P.val=sectionPair k (phi k P.val)+relationPair k (kernelCoefficients k P) := by
  apply Prod.ext
  · ext i j
    change P.val.1 i j=(sectionPair k (phi k P.val)).1 i j+(relationPair k (kernelCoefficients k P)).1 i j
    fin_cases i <;> fin_cases j <;>
      simp [sectionPair,leftIndex,rightIndex,phi,compress,Allowed,relationPair,Cross,crossRow,crossCol,kernelCoefficients,lower_left,lower_right] <;> ring
  · ext i j
    change P.val.2 i j=(sectionPair k (phi k P.val)).2 i j+(relationPair k (kernelCoefficients k P)).2 i j
    fin_cases i <;> fin_cases j <;>
      simp [sectionPair,leftIndex,rightIndex,phi,compress,Allowed,relationPair,Cross,crossRow,crossCol,kernelCoefficients,lower_left,lower_right] <;> ring

theorem normal_form (P : PathAlgebra k) :
    P = sectionMap k (pathMap k P) + relationCombination k (kernelCoefficients k P) := by
  apply Subtype.ext
  exact normal_form_pair k P

theorem relations_vanish (v : Fin 3 → Fin 4 → k) :
    pathMap k (relationCombination k v)=0 := by
  apply Subtype.ext
  change phi k (relationPair k v)=0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply,Pi.add_apply,compress,Allowed,phi,relationPair,Cross,crossRow,crossCol]

/-- The relation ideal, with an explicit 12-coordinate normal form below. -/
def relationSpace : Submodule k (PathAlgebra k) := (pathMap k).toLinearMap.ker
abbrev Presented := PathAlgebra k ⧸ relationSpace k

theorem kernel_exact (P : PathAlgebra k) :
    pathMap k P=0 ↔ ∃ v, P=relationCombination k v := by
  constructor
  · intro h
    refine ⟨kernelCoefficients k P,?_⟩
    have hn := normal_form k P
    rw [h] at hn
    have hz : sectionMap k 0=0 := by
      apply Subtype.ext; apply Prod.ext <;> ext i j
      all_goals fin_cases i <;> fin_cases j <;> simp [leftIndex,rightIndex,Cross,sectionMap,sectionPair]
    simpa [hz] using hn
  · rintro ⟨v,rfl⟩; exact relations_vanish k v

end N4

namespace N4
variable (k : Type*) [Field k]
section Bridge
variable {R : Type*} [CommRing R] (π : R) (ρ : R →+* k)
variable (hπ4 : π^4=0) (ann : ∀ x : R, π^3*x=0 ↔ ρ x=0)

def homScale {i j : Fin 9} (c : R) (f : HomData π i j) : HomData π i j where
  r := c*f.r
  p := c*f.p
  q := c*f.q
  d := c*f.d
  t := c*f.t
  w := c*f.w
  v := c*f.v
  descent_free := by linear_combination c*f.descent_free
  descent_torsion := by linear_combination c*f.descent_torsion
  source_free := by linear_combination c*f.source_free
  source_torsion := by linear_combination c*f.source_torsion

def homZero (i j : Fin 9) : HomData π i j where
  r := 0; p := 0; q := 0; d := 0; t := 0; w := 0; v := 0
  descent_free := by simp
  descent_torsion := by simp
  source_free := by simp
  source_torsion := by simp

/-- Matrix composition, including all congruence witnesses. -/
def homComp {i j l : Fin 9} (f : HomData π i j) (g : HomData π j l) : HomData π i l where
  r := f.r*g.r+f.p*g.q
  p := f.r*g.p+f.p*g.d
  q := f.q*g.r+f.d*g.q
  d := f.q*g.p+f.d*g.d
  t := f.t*g.t
  w := f.w*g.w
  v := f.v*g.t+f.w*g.v
  descent_free := by
    linear_combination f.r*g.descent_free + f.p*g.descent_torsion + g.w*f.descent_free
  descent_torsion := by
    linear_combination f.q*g.descent_free + f.d*g.descent_torsion + g.w*f.descent_torsion
  source_free := by
    linear_combination f.r*g.source_free + f.p*g.source_torsion + g.t*f.source_free + g.v*f.descent_free
  source_torsion := by
    linear_combination f.q*g.source_free + f.d*g.source_torsion + g.t*f.source_torsion + g.v*f.descent_torsion

include ann in
theorem torsion_coefficient_zero {i j : Fin 9} (f : HomData π i j) : ρ f.p=0 := by
  apply (ann f.p).mp
  have h := f.descent_free
  fin_cases j <;> norm_num [ell] at h
  all_goals first | linear_combination π^3*h | linear_combination π^2*h | linear_combination π*h

include ann in
theorem composition_residue {i j l : Fin 9} (f : HomData π i j) (g : HomData π j l) :
    ρ (homComp π f g).r = ρ f.r*ρ g.r := by
  simp [homComp,torsion_coefficient_zero k π ρ ann f]

/-- On the ambient map R⊕C_ell(j) → R⊕C_ell(i), all torsion
output coordinates are already killed by π³. These are the two free-row tests. -/
def HomEquivalent {i j : Fin 9} (f g : HomData π i j) : Prop :=
  π^3*(f.r-g.r)=0 ∧ π^3*(f.p-g.p)=0
include ann in
theorem hom_quotient_exact {i j : Fin 9} (f g : HomData π i j) :
    HomEquivalent π f g ↔ ρ f.r=ρ g.r := by
  simp only [HomEquivalent,ann,map_sub,sub_eq_zero]
  simp [torsion_coefficient_zero k π ρ ann f,torsion_coefficient_zero k π ρ ann g]

abbrev RawEnd := (i j : Fin 9) → HomData π i j

def reduce (F : RawEnd π) : M9 k := fun i j => ρ (F i j).r
include hπ4 ann in
def reduceEnd (F : RawEnd π) : End k :=
  ⟨reduce k π ρ F,fun i j h => hom_reduces k π ρ hπ4 ann i j (F i j) h⟩

include ann in
theorem reduce_composition (F G : RawEnd π) (i j : Fin 9) :
    (∑ l, ρ (homComp π (F i l) (G l j)).r) =
      (reduce k π ρ F * reduce k π ρ G) i j := by
  simp [composition_residue k π ρ ann,Matrix.mul_apply,reduce]

include hπ4 ann in
theorem reduce_surjective (surj : Function.Surjective ρ) :
    Function.Surjective (reduceEnd k π ρ hπ4 ann) := by
  classical
  intro T
  choose lift hlift using surj
  let F : RawEnd π := fun i j => if h : Allowed i j then
    homScale π (lift (T.val i j)) (homLift π hπ4 i j h) else homZero π i j
  refine ⟨F,?_⟩
  apply Subtype.ext; ext i j
  change ρ (F i j).r=T.val i j
  by_cases h : Allowed i j
  · simp [F,h,homScale,homLift,hlift]
  · simp [F,h,homZero,T.property i j h]

include ann in
theorem quotient_exact (F G : RawEnd π) :
    (∀ i j, HomEquivalent π (F i j) (G i j)) ↔ reduce k π ρ F=reduce k π ρ G := by
  simp only [hom_quotient_exact k π ρ ann]
  constructor
  · intro h; ext i j; exact h i j
  · intro h i j; exact congrFun (congrFun h i) j

end Bridge
end N4

namespace N4
variable (k : Type*) [Field k]
def upperIndex (i : Fin 3) : Fin 8 := ⟨i.val,by omega⟩
def lowerIndex (j : Fin 4) : Fin 8 := ⟨j.val+4,by omega⟩
def relationBasis (i : Fin 3) (j : Fin 4) : PathAlgebra k :=
  relationCombination k (fun a b => if a=i ∧ b=j then 1 else 0)
def diamond : PathAlgebra k := relationBasis k 2 0

theorem relationBasis_val (i : Fin 3) (j : Fin 4) :
    (relationBasis k i j).val =
      (Matrix.single (upperIndex i) (lowerIndex j) 1,
       -(Matrix.single (upperIndex i) (lowerIndex j) 1)) := by
  apply Prod.ext <;> ext a b
  all_goals fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [relationBasis,relationCombination,relationPair,Cross,crossRow,crossCol,upperIndex,lowerIndex,Matrix.single]

def commonPath (i j : Fin 8) (hij : i ≤ j) : PathAlgebra k :=
  ⟨(Matrix.single i j 1,Matrix.single i j 1),by
    have h : Matrix.single i j (1 : k) ∈ Chain.endAlgebra k 8 := by
      intro a b hab
      simp only [Matrix.single_apply]
      split_ifs with he
      · obtain ⟨rfl,rfl⟩ := he
        exact (not_lt_of_ge hij hab).elim
      · rfl
    exact ⟨h,h,by intros; rfl⟩⟩

/-- A branch-specific path. Its coefficient is independent of the other branch. -/
def leftPath (i j : Fin 8) (hij : i ≤ j) (hn : ¬Shared i j) : PathAlgebra k :=
  ⟨(Matrix.single i j 1,0),by
    refine ⟨(commonPath k i j hij).property.1,(Chain.endAlgebra k 8).zero_mem,?_⟩
    intro a b h
    change Matrix.single i j (1 : k) a b=0
    simp only [Matrix.single_apply]
    split_ifs with he
    · obtain ⟨rfl,rfl⟩ := he
      exact (hn h).elim
    · rfl⟩

def rightPath (i j : Fin 8) (hij : i ≤ j) (hn : ¬Shared i j) : PathAlgebra k :=
  ⟨(0,Matrix.single i j 1),by
    refine ⟨(Chain.endAlgebra k 8).zero_mem,(commonPath k i j hij).property.1,?_⟩
    intro a b h
    exact ((leftPath k i j hij hn).property.2.2 a b h).symm⟩

/-- The generating relation is exactly the difference of the two length-two
paths around the diamond (24→12→23) and (24→25→23). -/
theorem diamond_paths : diamond k =
    leftPath k 2 3 (by decide) (by decide) * leftPath k 3 4 (by decide) (by decide) -
    rightPath k 2 3 (by decide) (by decide) * rightPath k 3 4 (by decide) (by decide) := by
  apply Subtype.ext
  change (relationBasis k 2 0).val = _
  rw [relationBasis_val]
  simp [leftPath,rightPath,upperIndex,lowerIndex]

/-- Every kernel basis relation is obtained from the single diamond relation
by composition with a path after it and a path before it. -/
theorem relation_context (i : Fin 3) (j : Fin 4) :
    relationBasis k i j =
      commonPath k (upperIndex i) 2 (by change i.val ≤ 2; omega) * diamond k *
      commonPath k 4 (lowerIndex j) (by change 4 ≤ j.val+4; omega) := by
  apply Subtype.ext
  simp only [Subalgebra.coe_mul,relationBasis_val,diamond,commonPath]
  change (Matrix.single (upperIndex i) (lowerIndex j) (1 : k),
    -Matrix.single (upperIndex i) (lowerIndex j) 1) =
    (Matrix.single (upperIndex i) 2 1,Matrix.single (upperIndex i) 2 1) *
    (Matrix.single 2 4 1,-Matrix.single 2 4 1) *
    (Matrix.single 4 (lowerIndex j) 1,Matrix.single 4 (lowerIndex j) 1)
  simp

def coefficient (right : Bool) (a b : Fin 8) : PathAlgebra k →ₗ[k] k where
  toFun P := if right then P.val.2 a b else P.val.1 a b
  map_add' _ _ := by cases right <;> rfl
  map_smul' _ _ := by cases right <;> rfl

theorem relationCombination_sum (v : Fin 3 → Fin 4 → k) :
    relationCombination k v=∑ i, ∑ j, v i j • relationBasis k i j := by
  apply Subtype.ext
  apply Prod.ext
  · ext a b
    change coefficient k false a b (relationCombination k v) = coefficient k false a b (∑ i, ∑ j, v i j • relationBasis k i j)
    simp only [map_sum,map_smul]
    fin_cases a <;> fin_cases b <;>
      simp [coefficient,relationCombination,relationPair,Cross,crossRow,crossCol,relationBasis,Fin.sum_univ_succ,smul_eq_mul]
  · ext a b
    change coefficient k true a b (relationCombination k v) = coefficient k true a b (∑ i, ∑ j, v i j • relationBasis k i j)
    simp only [map_sum,map_smul]
    fin_cases a <;> fin_cases b <;>
      simp [coefficient,relationCombination,relationPair,Cross,crossRow,crossCol,relationBasis,Fin.sum_univ_succ,smul_eq_mul]

/-- The twelve relation coefficients are independent, in every characteristic. -/
theorem relationCombination_injective : Function.Injective (relationCombination k) := by
  intro v w h
  funext i j
  have he := congrArg (fun P : PathAlgebra k => P.val.1 (upperIndex i) (lowerIndex j)) h
  fin_cases i <;> fin_cases j <;>
    simpa [relationCombination,relationPair,Cross,crossRow,crossCol,upperIndex,lowerIndex] using he

/-- The actual two-sided ideal generated by one commutativity relation. -/
def relations : TwoSidedIdeal (PathAlgebra k) := TwoSidedIdeal.span {diamond k}

theorem relations_eq_kernel : relations k=TwoSidedIdeal.ker (pathMap k) := by
  apply le_antisymm
  · apply TwoSidedIdeal.span_le.mpr
    intro x hx
    have hx' : x=diamond k := Set.mem_singleton_iff.mp hx
    subst x
    apply (TwoSidedIdeal.mem_ker (pathMap k)).mpr
    exact relations_vanish k _
  · intro P hP
    obtain ⟨v,rfl⟩ := (kernel_exact k P).mp ((TwoSidedIdeal.mem_ker (pathMap k)).mp hP)
    rw [relationCombination_sum]
    apply sum_mem
    intro i _
    apply sum_mem
    intro j _
    have hd : diamond k ∈ relations k := TwoSidedIdeal.subset_span (Set.mem_singleton _)
    have hb : relationBasis k i j ∈ relations k := by
      rw [relation_context]
      exact (relations k).mul_mem_right _ _ ((relations k).mul_mem_left _ _ hd)
    rw [Algebra.smul_def]
    exact (relations k).mul_mem_left _ _ hb

theorem relationSpace_matches (P : PathAlgebra k) :
    P ∈ relationSpace k ↔ P ∈ relations k := by
  rw [relations_eq_kernel,TwoSidedIdeal.mem_ker]
  rfl

theorem presented_dimension : Module.finrank k (Presented k)=44 := by
  change Module.finrank k (PathAlgebra k ⧸ (pathMap k).toLinearMap.ker)=44
  rw [((pathMap k).toLinearMap.quotKerEquivOfSurjective (pathMap_surjective k)).finrank_eq]
  exact end_dimension k

theorem C2_certificate :
    Function.Surjective (pathMap k) ∧
    (∀ P ∈ relations k, pathMap k P=0) ∧
    Module.finrank k (Presented k)=Module.finrank k (End k) ∧
    Module.finrank k (End k)=44 := by
  refine ⟨pathMap_surjective k,?_,(presented_dimension k).trans (end_dimension k).symm,end_dimension k⟩
  intro P hP
  rw [relations_eq_kernel] at hP
  exact (TwoSidedIdeal.mem_ker (pathMap k)).mp hP
end N4

namespace N4
/-- C1 data, directly using the supplied formula; the AR interpretation is not formalized. -/
def oldObjects : List DBObject := N3.oldObjects ++ N3.newObjects
def newObjects : List DBObject :=
  [⟨10,[],[4],[]⟩,⟨11,[1],[4],[[some 3]]⟩,⟨12,[2],[4],[[some 2]]⟩,
   ⟨13,[3],[4],[[some 1]]⟩,⟨14,[4],[4],[[some 0]]⟩,
   ⟨22,[2],[4,1],[[some 2,some 0]]⟩,⟨23,[3],[4,1],[[some 1,some 0]]⟩,
   ⟨24,[2],[4,2],[[some 2,some 1]]⟩,⟨25,[3],[4,2],[[some 1,some 0]]⟩]
def escapingTranslateIDs : List (Nat × Nat) :=
  [(1,13),(3,12),(4,23),(6,11),(7,22),(8,25),(21,24)]
def remainingIDs : List Nat := [10,11,12,13,14,22,23,24,25,26].filter
  (fun i => !(newObjects.map DBObject.id).contains i)
theorem remaining_objects : remainingIDs=[26] := by decide
def nextStartingObjects : List DBObject :=
  [⟨26,[3,1],[4,2],[[some 1,some 0],[none,some 1]]⟩]

variable (k : Type*) [Field k]
section Extra
variable {R : Type*} [CommRing R] (π : R) (ρ : R →+* k)
variable (ann : ∀ r : R, π^3*r=0 ↔ ρ r=0)

/-- Endomorphisms of ID26: C₃⊕C₁ → R⊕C₂, columns (π,1),(0,π).
The ambient matrix is [[r,p],[q,d]], with its second row read modulo π².
The witnesses x,y,z,w give the images of the two source generators. -/
structure ExtraEnd where
  r : R
  p : R
  q : R
  d : R
  x : R
  y : R
  z : R
  w : R
  v1 : R
  v2 : R
  descent : π^2*p=0
  first_free : π*r+p=π*x
  first_torsion : π*q+d=x+π*y+π^2*v1
  second_free : π*p=π*z
  second_torsion : π*d=z+π*w+π^2*v2

def extraDiagonal (r : R) : ExtraEnd π where
  r := r; p := 0; q := 0; d := r
  x := r; y := 0; z := 0; w := r; v1 := 0; v2 := 0
  descent := by simp
  first_free := by simp
  first_torsion := by simp
  second_free := by simp
  second_torsion := by simp

include ann in
theorem extra_p_zero (f : ExtraEnd π) : ρ f.p=0 := by
  apply (ann f.p).mp
  linear_combination π*f.descent

include ann in
theorem extra_quotient_exact (f g : ExtraEnd π) :
    (π^3*(f.r-g.r)=0 ∧ π^3*(f.p-g.p)=0) ↔ ρ f.r=ρ g.r := by
  simp only [ann,map_sub,sub_eq_zero]
  simp [extra_p_zero k π ρ ann f,extra_p_zero k π ρ ann g]

include ann in
/-- The free-row coefficient of ambient matrix composition descends to
ordinary multiplication in k. -/
theorem extra_composition (f g : ExtraEnd π) :
    ρ (f.r*g.r+f.p*g.q)=ρ f.r*ρ g.r := by
  simp [extra_p_zero k π ρ ann f]

theorem extra_surjective (surj : Function.Surjective ρ) :
    Function.Surjective (fun f : ExtraEnd π => ρ f.r) := by
  intro a
  obtain ⟨r,hr⟩ := surj a
  exact ⟨extraDiagonal π r,hr⟩

/-- Explicit two-sided inverse in the quotient for f or its complement.
The inverse is represented by extraDiagonal c. -/
theorem C3_local_certificate (surj : Function.Surjective ρ) (f : ExtraEnd π) :
    ∃ c : R,
      (ρ f.r*ρ c=1 ∧ ρ c*ρ f.r=1) ∨
      ((1-ρ f.r)*ρ c=1 ∧ ρ c*(1-ρ f.r)=1) := by
  by_cases h : ρ f.r=0
  · exact ⟨1,Or.inr (by simp [h])⟩
  · obtain ⟨c,hc⟩ := surj ((ρ f.r)⁻¹)
    exact ⟨c,Or.inl (by simp [hc,h])⟩
end Extra
end N4

end UniserialComputations
