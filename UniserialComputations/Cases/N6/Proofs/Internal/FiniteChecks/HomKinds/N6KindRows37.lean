import N6CompositionData
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
theorem kind_allowed_37 : ∀ j l, Allowed (homKind 37 j) (homKind j l) (homKind 37 l) := by decide +kernel
end UniserialComputations.N6
