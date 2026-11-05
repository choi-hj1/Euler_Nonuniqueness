import EulerNonuniqueness.Section3.ComplexHolderBanach

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

instance explicitComplexHolderSMul : SMul ℂ PeriodicHolderHalf :=
  inferInstanceAs (SMul ℂ complexPeriodicHolderGraph)

instance explicitComplexHolderModule : Module ℂ PeriodicHolderHalf :=
  Submodule.module complexPeriodicHolderGraph

instance explicitComplexC1HolderSMul : SMul ℂ PeriodicC1HolderHalf :=
  inferInstanceAs (SMul ℂ complexPeriodicC1HolderGraph)

instance explicitComplexC1HolderModule : Module ℂ PeriodicC1HolderHalf :=
  Submodule.module complexPeriodicC1HolderGraph

end

end EulerNonuniqueness.Paper
