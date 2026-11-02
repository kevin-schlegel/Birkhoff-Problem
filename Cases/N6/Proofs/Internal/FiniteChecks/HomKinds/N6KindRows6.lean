import N6CompositionData
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
theorem kind_allowed_6 : ∀ j l, Allowed (homKind 6 j) (homKind j l) (homKind 6 l) := by decide +kernel
end UniserialComputations.N6
