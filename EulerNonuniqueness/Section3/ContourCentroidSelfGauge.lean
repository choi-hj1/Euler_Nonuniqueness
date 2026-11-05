import EulerNonuniqueness.Section3.ContourCentroidSelfInvariance
import EulerNonuniqueness.Section3.ContourCentroidGauge

noncomputable section

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance centroidSelfGaugeHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph

local instance centroidSelfGaugeC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

private theorem real_linear_rotating_combination {space : Type*} [NormedAddCommGroup space]
    [NormedSpace ℝ space] (linear : space →L[ℝ] ℂ) (self rotation : space) (centroid : ℂ) (density : ℝ)
    (selfZero : linear self = 0) (rotationIdentity : linear rotation = Complex.I * centroid) :
    linear (density • self - (density / 2) • rotation) = -(density / 2) • (Complex.I * centroid) := by
  rw [map_sub, map_smul, map_smul, selfZero, rotationIdentity, smul_zero, zero_sub, neg_smul]

theorem contourCentroidFunctional_derivative_rotating_self (data : PeriodicC1HolderHalf) (density : ℝ)
    (small : ‖data - standardCircleBanach‖ < min (1 / 3) (2 / (3 * Real.pi))) :
    (fderiv ℝ contourCentroidFunctional data)
      (density • extendedContourVelocity data - (density / 2) • (Complex.I • data)) =
      -(density / 2) • (Complex.I * contourCentroidFunctional data) := by
  exact real_linear_rotating_combination (fderiv ℝ contourCentroidFunctional data)
    (extendedContourVelocity data) (Complex.I • data) (contourCentroidFunctional data) density
    (contourCentroidFunctional_derivative_self data small)
    (contourCentroidFunctional_derivative_rotation data (small.trans_le (min_le_left _ _)))

theorem contourCentroidGaugeProjection_rotating_self (data : PeriodicC1HolderHalf) (density : ℝ)
    (small : ‖data - standardCircleBanach‖ < min (1 / 3) (2 / (3 * Real.pi)))
    (centered : contourCentroidFunctional data = 0) :
    contourCentroidGaugeProjection data
      (density • extendedContourVelocity data - (density / 2) • (Complex.I • data)) =
      density • extendedContourVelocity data - (density / 2) • (Complex.I • data) := by
  rw [contourCentroidGaugeProjection_apply, contourCentroidFunctional_derivative_rotating_self data density small,
    centered, mul_zero, smul_zero]
  change (density • extendedContourVelocity data - (density / 2) • (Complex.I • data)) - c1ConstantCLM 0 = _
  rw [map_zero]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change ((density • extendedContourVelocity data - (density / 2) • (Complex.I • data)).val.1 label) - 0 = _
  exact sub_zero _

theorem contourCentroidGaugeProjection_self_and_external (data external : PeriodicC1HolderHalf) (density : ℝ)
    (small : ‖data - standardCircleBanach‖ < min (1 / 3) (2 / (3 * Real.pi)))
    (centered : contourCentroidFunctional data = 0) :
    contourCentroidGaugeProjection data
      ((density • extendedContourVelocity data - (density / 2) • (Complex.I • data)) + external) =
      (density • extendedContourVelocity data - (density / 2) • (Complex.I • data)) +
        contourCentroidGaugeProjection data external := by
  rw [map_add, contourCentroidGaugeProjection_rotating_self data density small centered]

end EulerNonuniqueness.Paper
