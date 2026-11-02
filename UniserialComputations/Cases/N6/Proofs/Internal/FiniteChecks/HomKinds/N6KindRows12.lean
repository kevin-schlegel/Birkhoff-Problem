import N6CompositionData
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
theorem kind_allowed_12 : ∀ j l, Allowed (homKind 12 j) (homKind j l) (homKind 12 l) := by decide +kernel
end UniserialComputations.N6
