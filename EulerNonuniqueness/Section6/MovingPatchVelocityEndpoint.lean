import EulerNonuniqueness.Section6.InverseRemainderEndpointDifference
import EulerNonuniqueness.Section6.MovingPatchVelocityShapeDifference
import EulerNonuniqueness.Section6.MovingPatchSourceComparison
import EulerNonuniqueness.Section6.MovingPatchVelocityCorrectionRelative

noncomputable section

open Set Metric MeasureTheory

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem MovingMaterialPatch.sourceVelocityCentroidCorrection_endpoint_difference_norm_le
    (path : MovingMaterialPatch) (density : ℝ) (first second : ℂ) (time : ℝ)
    {distance : ℝ} (positive : 0 < distance)
    (centered : path.center time = path.centroid time)
    (area : volume.real (path.domain time) = Real.pi * path.radius ^ 2)
    (firstSeparated : 2 * path.radius + distance ≤ ‖first - path.center time‖)
    (secondSeparated : 2 * path.radius + distance ≤ ‖second - path.center time‖) :
    ‖path.sourceVelocityCentroidCorrection density first time -
      path.sourceVelocityCentroidCorrection density second time‖ ≤
        6 * |density| * path.radius ^ 4 * distance⁻¹ ^ 4 * ‖first - second‖ := by
  have radiusPositive := path.radius_positive
  have bounded (source : ℂ) (member : source ∈ path.domain time) :
      ‖source - path.center time‖ ≤ 2 * path.radius :=
    (Metric.mem_ball.mp (path.domain_subset_ball time member)).le
  have actual := Section6.centeredDomainInverseCorrection_endpoint_difference_norm_le
    (path.domain_isOpen time).measurableSet (path.domain_isBounded time).measure_lt_top
    (path.center time) first second (by positivity) positive bounded firstSeparated secondSeparated
    (path.domain_centered_integral_zero_of_true_centroid time centered)
  rw [area] at actual
  unfold MovingMaterialPatch.sourceVelocityCentroidCorrection
  rw [← mul_sub, ← smul_sub, norm_mul, norm_smul, Real.norm_eq_abs]
  have prefactorNorm : ‖Complex.I / ((2 * Real.pi : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
    simp only [norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  rw [prefactorNorm]
  apply (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left actual (abs_nonneg density))
    (by positivity : 0 ≤ 1 / (2 * Real.pi))).trans_eq
  field_simp
  <;> ring

namespace MovingPatchSourceComparison

theorem velocityCentroidCorrection_endpoint_exists_centered_relative_bound :
    ∃ radius > (0 : ℝ), ∃ parameterRadius > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ comparison : MovingPatchSourceComparison,
      comparison.initial ∈ ball 0 radius → comparison.final ∈ ball 0 radius →
      contourCentroidFunctional (comparison.first.shape comparison.time) = 0 →
      contourCentroidFunctional (comparison.second.shape comparison.time) = 0 →
      comparison.first.center comparison.time = comparison.first.centroid comparison.time →
      ∀ distance : ℝ, 0 < distance →
      2 * comparison.first.radius + distance ≤
        ‖comparison.firstReceiver - comparison.first.center comparison.time‖ →
      2 * comparison.first.radius + distance ≤
        ‖comparison.secondReceiver - comparison.second.center comparison.time‖ →
      comparison.first.radius / ‖comparison.secondReceiver - comparison.second.center comparison.time‖ ≤ parameterRadius →
      ‖comparison.velocityCentroidCorrectionDifference‖ ≤
        comparison.velocityCentroidCorrectionCenterEnvelope distance +
          comparison.velocityCentroidCorrectionShapeEnvelope constant := by
  obtain ⟨radius, radiusPositive, parameterRadius, parameterPositive, constant, nonnegative, bound⟩ :=
    MovingMaterialPatch.sourceVelocityCentroidCorrection_exists_spectral_shape_bound
  refine ⟨radius, radiusPositive, parameterRadius, parameterPositive, constant, nonnegative, ?_⟩
  intro comparison initialInside finalInside firstCentered secondCentered trueCenter distance positive
    firstSeparated secondSeparated small
  have actualShape := bound comparison.first comparison.second comparison.density comparison.hybridReceiver
    comparison.secondReceiver comparison.time comparison.initial comparison.final initialInside finalInside
    comparison.firstShape comparison.secondShape comparison.radiusEqual comparison.phaseEqual
    comparison.hybridReceiver_displacement comparison.firstArea comparison.secondArea firstCentered secondCentered
    distance positive (by simpa only [comparison.hybridReceiver_displacement] using secondSeparated)
    (by simpa only [comparison.hybridReceiver_displacement] using small)
  have actualCenter := comparison.first.sourceVelocityCentroidCorrection_endpoint_difference_norm_le
    comparison.density comparison.firstReceiver comparison.hybridReceiver comparison.time positive trueCenter
    comparison.firstArea firstSeparated
    (by simpa only [comparison.hybridReceiver_displacement] using secondSeparated)
  have centerBound : ‖comparison.first.sourceVelocityCentroidCorrection comparison.density comparison.firstReceiver comparison.time -
      comparison.first.sourceVelocityCentroidCorrection comparison.density comparison.hybridReceiver comparison.time‖ ≤
      comparison.velocityCentroidCorrectionCenterEnvelope distance := by
    apply actualCenter.trans
    rw [comparison.firstReceiver_sub_hybridReceiver]
    unfold velocityCentroidCorrectionCenterEnvelope
    have baseNonnegative : 0 ≤ |comparison.density| * comparison.first.radius ^ 4 * distance⁻¹ ^ 4 *
        ‖comparison.displacementDifference‖ := by positivity
    nlinarith
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (comparison.first.sourceVelocityCentroidCorrection comparison.density comparison.firstReceiver comparison.time)
    (comparison.first.sourceVelocityCentroidCorrection comparison.density comparison.hybridReceiver comparison.time)
    (comparison.second.sourceVelocityCentroidCorrection comparison.density comparison.secondReceiver comparison.time)
  apply triangle.trans
  exact (add_le_add centerBound actualShape).trans_eq (by
    simp only [velocityCentroidCorrectionShapeEnvelope, spectralDifferenceBudget,
      comparison.hybridReceiver_displacement])

end MovingPatchSourceComparison

end EulerNonuniqueness.Paper
