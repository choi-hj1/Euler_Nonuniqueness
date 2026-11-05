import EulerNonuniqueness.Section3.DiskNormalizedSpectralEvolution
import EulerNonuniqueness.General.AffineResidualRelativeRemainder

noncomputable section

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

local instance normalizedRelativeErrorC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskPhysicalSpectralInverseDerivative_exists_uniform_pair_bounds :
    ∃ radius > 0, ∃ constant ≥ 1,
      (∀ data : PeriodicC1HolderHalf, ‖data - standardCircleBanach‖ ≤ radius →
        ‖diskPhysicalSpectralInverseDerivative data‖ ≤ constant) ∧
      ∀ first final : PeriodicC1HolderHalf,
      ‖first - standardCircleBanach‖ ≤ radius → ‖final - standardCircleBanach‖ ≤ radius →
      ‖diskPhysicalSpectralInverseDerivative first - diskPhysicalSpectralInverseDerivative final‖ ≤
        constant * ‖first - final‖ := by
  obtain ⟨inverseRadius, inversePositive, inverseConstant, inverseOne, inverseBounds, coordinateDifference, _⟩ :=
    diskPhysicalSpectralCoordinate_exists_uniform_inverse_bounds
  obtain ⟨chartRadius, chartPositive, chartConstant, chartOne, _, chartDifference⟩ :=
    diskPhysicalSpectralChart_exists_uniform_firstOrder_bounds
  have coordinateSmall : ∀ᶠ data in 𝓝 standardCircleBanach,
      ‖diskPhysicalSpectralCoordinate data‖ < chartRadius := by
    have convergence : Tendsto diskPhysicalSpectralCoordinate (𝓝 standardCircleBanach)
        (𝓝 (0 : PeriodicC1HolderHalf)) := by
      simpa only [diskPhysicalSpectralCoordinate_circle] using diskPhysicalSpectralCoordinate_continuousAt_circle.tendsto
    simpa only [mem_ball, dist_zero_right] using convergence.eventually (ball_mem_nhds _ chartPositive)
  obtain ⟨outerRadius, outerPositive, contained⟩ := Metric.eventually_nhds_iff.mp
    (coordinateSmall.and diskPhysicalSpectralCoordinate_eventually_inverse_derivative)
  let radius := min inverseRadius (outerRadius / 2)
  let constant := inverseConstant + chartConstant * inverseConstant
  have inverseLe : inverseConstant ≤ constant := by dsimp [constant]; nlinarith
  have productLe : chartConstant * inverseConstant ≤ constant := by dsimp [constant]; linarith
  have constantOne : 1 ≤ constant := inverseOne.trans inverseLe
  have actual (data : PeriodicC1HolderHalf) (nearby : ‖data - standardCircleBanach‖ ≤ radius) :=
    contained (show dist data standardCircleBanach < outerRadius by
      rw [dist_eq_norm]
      exact (nearby.trans (min_le_right _ _)).trans_lt (by linarith))
  refine ⟨radius, by dsimp [radius]; positivity, constant, constantOne, ?_, ?_⟩
  · intro data nearby
    exact ((inverseBounds data (nearby.trans (min_le_left _ _))).2).trans inverseLe
  · intro first final firstNearby finalNearby
    have firstActual := actual first firstNearby
    have finalActual := actual final finalNearby
    have inverseDifference := (chartDifference (diskPhysicalSpectralCoordinate first)
      (diskPhysicalSpectralCoordinate final) firstActual.1.le finalActual.1.le).2
    change ‖diskPhysicalSpectralInverseDerivative
        (diskStationaryChart (diskSpectralTubularChart (diskPhysicalSpectralCoordinate first))) -
      diskPhysicalSpectralInverseDerivative
        (diskStationaryChart (diskSpectralTubularChart (diskPhysicalSpectralCoordinate final)))‖ ≤ _ at inverseDifference
    rw [firstActual.2.1, finalActual.2.1] at inverseDifference
    have coordinate := coordinateDifference first final (firstNearby.trans (min_le_left _ _))
      (finalNearby.trans (min_le_left _ _))
    exact (inverseDifference.trans (mul_le_mul_of_nonneg_left coordinate (by linarith))).trans
      (by convert mul_le_mul_of_nonneg_right productLe (norm_nonneg (first - final)) using 1 <;> ring)

theorem diskNormalizedSpectralError_exists_relative_ball :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ first final firstError finalError : PeriodicC1HolderHalf,
      ‖first - standardCircleBanach‖ ≤ radius → ‖final - standardCircleBanach‖ ≤ radius →
      ‖diskNormalizedSpectralError first firstError - diskNormalizedSpectralError final finalError‖ ≤
        constant * (‖firstError - finalError‖ + ‖first - final‖ * ‖finalError‖) := by
  obtain ⟨inverseRadius, inversePositive, inverseConstant, inverseOne, inverseBound, inverseDifference⟩ :=
    diskPhysicalSpectralInverseDerivative_exists_uniform_pair_bounds
  obtain ⟨normalRadius, normalPositive, normalConstant, normalOne, normalBound, normalDifference, normalDerivativeDifference⟩ :=
    contourAreaCentroidNormalization_exists_uniform_bounds
  have near : ∀ᶠ data in 𝓝 standardCircleBanach,
      ‖contourAreaCentroidNormalization data - standardCircleBanach‖ < inverseRadius := by
    have actual : ContinuousAt contourAreaCentroidNormalization standardCircleBanach :=
      (contourAreaCentroidNormalization_differentiableAt standardCircleBanach (by simp)).continuousAt
    have convergence : Tendsto (fun data => ‖contourAreaCentroidNormalization data - standardCircleBanach‖)
        (𝓝 standardCircleBanach) (𝓝 (0 : ℝ)) := by
      simpa only [contourAreaCentroidNormalization_circle, sub_self, norm_zero] using
        (actual.sub (show ContinuousAt (fun _ : PeriodicC1HolderHalf => standardCircleBanach)
          standardCircleBanach from continuousAt_const)).norm.tendsto
    exact convergence.eventually (eventually_lt_nhds inversePositive)
  obtain ⟨outerRadius, outerPositive, contained⟩ := Metric.eventually_nhds_iff.mp near
  let radius := min normalRadius (outerRadius / 2)
  let constant := inverseConstant * normalConstant * (1 + normalConstant)
  have inverseNonnegative : 0 ≤ inverseConstant := le_trans (by norm_num) inverseOne
  have normalNonnegative : 0 ≤ normalConstant := le_trans (by norm_num) normalOne
  have productNonnegative : 0 ≤ inverseConstant * normalConstant := mul_nonneg inverseNonnegative normalNonnegative
  have productOne : 1 ≤ inverseConstant * normalConstant := by nlinarith
  have constantOne : 1 ≤ constant := by
    dsimp [constant]
    nlinarith [mul_nonneg productNonnegative normalNonnegative]
  have productLe : inverseConstant * normalConstant ≤ constant := by
    dsimp [constant]
    nlinarith [mul_nonneg productNonnegative normalNonnegative]
  have actual (data : PeriodicC1HolderHalf) (nearby : ‖data - standardCircleBanach‖ ≤ radius) :
      ‖contourAreaCentroidNormalization data - standardCircleBanach‖ ≤ inverseRadius := by
    apply le_of_lt
    apply contained
    rw [dist_eq_norm]
    exact (nearby.trans (min_le_right _ _)).trans_lt (by linarith)
  refine ⟨radius, by dsimp [radius]; positivity, constant, constantOne, ?_⟩
  intro first final firstError finalError firstNearby finalNearby
  have firstNormal := firstNearby.trans (min_le_left _ _)
  have finalNormal := finalNearby.trans (min_le_left _ _)
  have firstInverse := inverseBound _ (actual first firstNearby)
  have finalInverse := inverseBound _ (actual final finalNearby)
  have inversePair := (inverseDifference _ _ (actual first firstNearby) (actual final finalNearby)).trans
    (mul_le_mul_of_nonneg_left (normalDifference first final firstNormal finalNormal) inverseNonnegative)
  let firstOperator := (diskPhysicalSpectralInverseDerivative (contourAreaCentroidNormalization first)).comp
    (fderiv ℝ contourAreaCentroidNormalization first)
  let finalOperator := (diskPhysicalSpectralInverseDerivative (contourAreaCentroidNormalization final)).comp
    (fderiv ℝ contourAreaCentroidNormalization final)
  have operatorNorm : ‖firstOperator‖ ≤ inverseConstant * normalConstant := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul firstInverse (normalBound first firstNormal) (norm_nonneg _) inverseNonnegative)
  have operatorIdentity : firstOperator - finalOperator =
      (diskPhysicalSpectralInverseDerivative (contourAreaCentroidNormalization first)).comp
        (fderiv ℝ contourAreaCentroidNormalization first - fderiv ℝ contourAreaCentroidNormalization final) +
      (diskPhysicalSpectralInverseDerivative (contourAreaCentroidNormalization first) -
        diskPhysicalSpectralInverseDerivative (contourAreaCentroidNormalization final)).comp
        (fderiv ℝ contourAreaCentroidNormalization final) := by
    apply ContinuousLinearMap.ext
    intro direction
    simp only [firstOperator, finalOperator, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, map_sub]
    abel
  have operatorPair : ‖firstOperator - finalOperator‖ ≤ constant * ‖first - final‖ := by
    rw [operatorIdentity]
    apply (norm_add_le _ _).trans
    have initial := (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul firstInverse (normalDerivativeDifference first final firstNormal finalNormal)
        (norm_nonneg _) inverseNonnegative)
    have other := (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul inversePair (normalBound final finalNormal) (norm_nonneg _) (by positivity))
    exact (add_le_add initial other).trans_eq (by dsimp only [constant]; ring)
  have vector : ‖firstOperator firstError - finalOperator finalError‖ ≤
      ‖firstOperator‖ * ‖firstError - finalError‖ + ‖firstOperator - finalOperator‖ * ‖finalError‖ := by
    with_reducible_and_instances
      exact EulerNonuniqueness.General.norm_operator_apply_difference_le firstOperator finalOperator firstError finalError
  have scalar := add_le_add
    (mul_le_mul_of_nonneg_right (operatorNorm.trans productLe) (norm_nonneg (firstError - finalError)))
    (mul_le_mul_of_nonneg_right operatorPair (norm_nonneg finalError))
  change ‖firstOperator firstError - finalOperator finalError‖ ≤ _
  with_reducible_and_instances
    exact (vector.trans scalar).trans_eq (by ring)

end EulerNonuniqueness.Paper
