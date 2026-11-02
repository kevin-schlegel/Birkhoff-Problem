import N6CompositionData
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
theorem kind_allowed_15 : ∀ j l, Allowed (homKind 15 j) (homKind j l) (homKind 15 l) := by decide +kernel
end UniserialComputations.N6
