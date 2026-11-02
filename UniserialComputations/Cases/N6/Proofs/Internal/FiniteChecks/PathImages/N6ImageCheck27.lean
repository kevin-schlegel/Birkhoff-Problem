import N6ImageData
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
variable (k : Type*) [Field k]
lemma basis_paths_27 : ∀ j : Fin 47, ∀ b : Fin 3,
  ((basisPaths 27 j b).map (fun u => u.1 • normalBlock u.2)).sum=basisBlock ℤ (homKind 27 j) b ∧
  (basisPaths 27 j b).all (fun u => normalTarget u.2 == 27 && normalSource u.2 == j)=true := by decide +kernel
end UniserialComputations.N6.Presentation
