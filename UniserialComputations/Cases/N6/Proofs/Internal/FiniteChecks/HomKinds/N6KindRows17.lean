import N6CompositionData
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
theorem kind_allowed_17 : ∀ j l, Allowed (homKind 17 j) (homKind j l) (homKind 17 l) := by decide +kernel
end UniserialComputations.N6
