import EulerNonuniqueness.Section3.MovingCentroidGaugeField

noncomputable section

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

local instance stateProjectionHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance stateProjectionC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

def movingContourStateClockCLM (count : ℕ) : MovingContourState count →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ ((Fin count → ℂ) × (Fin count → PeriodicC1HolderHalf))

def movingContourStateCenterCLM (count : ℕ) (index : Fin count) : MovingContourState count →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj index).comp
    ((ContinuousLinearMap.fst ℝ (Fin count → ℂ) (Fin count → PeriodicC1HolderHalf)).comp
      (ContinuousLinearMap.snd ℝ ℝ ((Fin count → ℂ) × (Fin count → PeriodicC1HolderHalf))))

def movingContourStateShapeCLM (count : ℕ) (index : Fin count) : MovingContourState count →L[ℝ] PeriodicC1HolderHalf :=
  (ContinuousLinearMap.proj index).comp
    ((ContinuousLinearMap.snd ℝ (Fin count → ℂ) (Fin count → PeriodicC1HolderHalf)).comp
      (ContinuousLinearMap.snd ℝ ℝ ((Fin count → ℂ) × (Fin count → PeriodicC1HolderHalf))))

end EulerNonuniqueness.Paper
