import EulerNonuniqueness.Section3.DiskPhysicalCoordinates
import EulerNonuniqueness.Section3.ExponentialStationaryChartInverse
import EulerNonuniqueness.Section3.ExponentialStationaryChartEvaluation
import EulerNonuniqueness.Section3.StationaryRelabelCurve

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance diskStationaryChartRealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph
local instance diskStationaryChartOperatorGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance diskStationaryChartOperatorSpace : NormedSpace ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

def diskStationaryChartGenerator :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  c1ProductCLM.comp ((c1ProductCLM (c1Constant Complex.I)).comp diskNeutralCLM)

theorem diskStationaryChartGenerator_value (increment value : PeriodicC1HolderHalf) (label : ℝ) :
    (diskStationaryChartGenerator increment value).val.1 label =
      (Complex.I * (diskNeutralCLM increment).val.1 label) * value.val.1 label := rfl

def diskStationaryChart (increment : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.exponentialStationaryChart diskStationaryChartGenerator standardCircleBanach increment

theorem diskStationaryChart_zero : diskStationaryChart 0 = standardCircleBanach :=
  EulerNonuniqueness.General.exponentialStationaryChart_zero _ _

theorem diskStationaryChart_analyticAt (point : PeriodicC1HolderHalf) :
    AnalyticAt ℝ diskStationaryChart point :=
  EulerNonuniqueness.General.exponentialStationaryChart_analyticAt _ _ _

theorem diskStationaryChart_hasStrictFDerivAt_zero :
    HasStrictFDerivAt diskStationaryChart (ContinuousLinearMap.id ℝ PeriodicC1HolderHalf) 0 :=
  EulerNonuniqueness.General.exponentialStationaryChart_hasStrictFDerivAt_zero _ _

def diskStationaryChartPartialHomeomorph : PartialHomeomorph PeriodicC1HolderHalf PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.exponentialStationaryChartPartialHomeomorph diskStationaryChartGenerator standardCircleBanach

theorem diskStationaryChart_zero_mem_source : (0 : PeriodicC1HolderHalf) ∈ diskStationaryChartPartialHomeomorph.source :=
  EulerNonuniqueness.General.exponentialStationaryChartPartialHomeomorph_zero_mem_source _ _

theorem diskStationaryChart_value (increment : PeriodicC1HolderHalf) (label : ℝ) :
    (diskStationaryChart increment).val.1 label =
      Complex.exp (Complex.I * (diskNeutralCLM increment).val.1 label) *
        (standardCircle label + increment.val.1 label -
          (Complex.I * (diskNeutralCLM increment).val.1 label) * standardCircle label) := by
  exact EulerNonuniqueness.General.exponentialStationaryChart_evaluation
    diskStationaryChartGenerator standardCircleBanach increment (contourLabelEvaluation label)
    (Complex.I * (diskNeutralCLM increment).val.1 label) (fun _ => rfl)

end

end EulerNonuniqueness.Paper
