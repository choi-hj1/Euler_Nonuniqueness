import EulerNonuniqueness.Section3.ContourGaugeOperatorTaylor
import EulerNonuniqueness.General.LocalSecondFromContDiff

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] centroidGaugeRegularityC1Space centroidGaugeRegularityDerivativeGroup
  centroidGaugeRegularityDerivativeSpace centroidGaugeRegularityOperatorGroup
  centroidGaugeRegularityConstantGroup gaugeOperatorTaylorConstantSpace gaugeOperatorTaylorOperatorSpace

local instance gaugeSecondC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem contourCentroidGaugeProjection_contDiffAt_three :
    ContDiffAt ℝ 3 contourCentroidGaugeProjection standardCircleBanach := by
  have small : ‖standardCircleBanach - standardCircleBanach‖ < (1 / 3 : ℝ) := by simp
  have smooth : ContDiffAt ℝ 4 contourCentroidFunctional standardCircleBanach :=
    (analyticAt_contourCentroidFunctional standardCircleBanach small).contDiffAt
  have derivativeSmooth : ContDiffAt ℝ 3 (fderiv ℝ contourCentroidFunctional) standardCircleBanach :=
    smooth.fderiv_right (by norm_num)
  have constantSmooth : ContDiffAt ℝ 3 (fun _ : PeriodicC1HolderHalf => c1ConstantCLM)
      standardCircleBanach := contDiffAt_const
  have composition : ContDiffAt ℝ 3
      (fun data : PeriodicC1HolderHalf => c1ConstantCLM.comp (fderiv ℝ contourCentroidFunctional data))
      standardCircleBanach := by
    with_reducible_and_instances
      exact ContDiffAt.clm_comp (𝕜 := ℝ) (X := PeriodicC1HolderHalf)
        (E := PeriodicC1HolderHalf) (F := ℂ) (G := PeriodicC1HolderHalf)
        constantSmooth derivativeSmooth
  have identitySmooth : ContDiffAt ℝ 3
      (fun _ : PeriodicC1HolderHalf => ContinuousLinearMap.id ℝ PeriodicC1HolderHalf)
      standardCircleBanach := contDiffAt_const
  unfold contourCentroidGaugeProjection
  with_reducible_and_instances exact identitySmooth.sub composition

theorem circleBasedCentroidProjection_contDiffAt_three :
    ContDiffAt ℝ 3 circleBasedCentroidProjection (0 : PeriodicC1HolderHalf) := by
  have outer : ContDiffAt ℝ 3 contourCentroidGaugeProjection
      (standardCircleBanach + (0 : PeriodicC1HolderHalf)) := by
    simpa only [add_zero] using contourCentroidGaugeProjection_contDiffAt_three
  exact outer.comp 0 (contDiffAt_const.add contDiffAt_id)

theorem circleBasedCentroidProjection_hasLipschitzSecondDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      circleBasedCentroidProjection (0 : PeriodicC1HolderHalf) := by
  exact EulerNonuniqueness.General.localSecondDerivativeNear_of_contDiffAt_three
    circleBasedCentroidProjection_contDiffAt_three

end EulerNonuniqueness.Paper
