import EulerNonuniqueness.Section3.ContourCentroidGaugeRegularity
import EulerNonuniqueness.General.LocalUniformQuadraticRemainder

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] centroidGaugeRegularityC1Space centroidGaugeRegularityDerivativeGroup
  centroidGaugeRegularityDerivativeSpace centroidGaugeRegularityOperatorGroup
  centroidGaugeRegularityConstantGroup

local instance gaugeOperatorTaylorConstantSpace : NormedSpace ℝ (ℂ →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := ℂ) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

local instance gaugeOperatorTaylorOperatorSpace : NormedSpace ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

theorem contourCentroidGaugeProjection_contDiffAt_two :
    ContDiffAt ℝ 2 contourCentroidGaugeProjection standardCircleBanach := by
  have small : ‖standardCircleBanach - standardCircleBanach‖ < (1 / 3 : ℝ) := by simp
  have smooth : ContDiffAt ℝ 3 contourCentroidFunctional standardCircleBanach :=
    (analyticAt_contourCentroidFunctional standardCircleBanach small).contDiffAt
  have derivativeSmooth : ContDiffAt ℝ 2 (fderiv ℝ contourCentroidFunctional) standardCircleBanach :=
    smooth.fderiv_right (by norm_num)
  have constantSmooth : ContDiffAt ℝ 2 (fun _ : PeriodicC1HolderHalf => c1ConstantCLM) standardCircleBanach :=
    contDiffAt_const
  have composition : ContDiffAt ℝ 2
      (fun data : PeriodicC1HolderHalf => c1ConstantCLM.comp (fderiv ℝ contourCentroidFunctional data))
      standardCircleBanach := by
    with_reducible_and_instances
      exact ContDiffAt.clm_comp (𝕜 := ℝ) (X := PeriodicC1HolderHalf)
        (E := PeriodicC1HolderHalf) (F := ℂ) (G := PeriodicC1HolderHalf)
        constantSmooth derivativeSmooth
  have identitySmooth : ContDiffAt ℝ 2
      (fun _ : PeriodicC1HolderHalf => ContinuousLinearMap.id ℝ PeriodicC1HolderHalf) standardCircleBanach :=
    contDiffAt_const
  unfold contourCentroidGaugeProjection
  with_reducible_and_instances
    exact identitySmooth.sub composition

def circleBasedCentroidProjection (increment : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  contourCentroidGaugeProjection (standardCircleBanach + increment)

theorem circleBasedCentroidProjection_contDiffAt_two :
    ContDiffAt ℝ 2 circleBasedCentroidProjection (0 : PeriodicC1HolderHalf) := by
  have outer : ContDiffAt ℝ 2 contourCentroidGaugeProjection
      (standardCircleBanach + (0 : PeriodicC1HolderHalf)) := by
    simpa only [add_zero] using contourCentroidGaugeProjection_contDiffAt_two
  exact outer.comp 0 (contDiffAt_const.add contDiffAt_id)

theorem circleBasedCentroidProjection_exists_uniform_quadratic_remainder :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ base increment : PeriodicC1HolderHalf,
      ‖base‖ + ‖increment‖ ≤ radius →
      ‖circleBasedCentroidProjection (base + increment) - circleBasedCentroidProjection base -
        fderiv ℝ circleBasedCentroidProjection base increment‖ ≤ constant * ‖increment‖ ^ 2 := by
  exact EulerNonuniqueness.General.HasLipschitzDerivativeNear.exists_uniform_quadratic_remainder
    circleBasedCentroidProjection
    (EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_contDiffAt_two
      circleBasedCentroidProjection_contDiffAt_two)

end EulerNonuniqueness.Paper
