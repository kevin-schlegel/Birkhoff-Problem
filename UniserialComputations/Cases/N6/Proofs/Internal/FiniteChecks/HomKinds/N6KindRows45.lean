import N6CompositionData
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
theorem kind_allowed_45 : ∀ j l, Allowed (homKind 45 j) (homKind j l) (homKind 45 l) := by decide +kernel
end UniserialComputations.N6
