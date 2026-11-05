import EulerNonuniqueness.Section3.MovingStrainAffineSpectralAbsolute
import EulerNonuniqueness.Section3.DiskPhysicalSpectralFirstOrderBounds
import EulerNonuniqueness.Section3.DiskSpectralRelativeStateBound
import EulerNonuniqueness.Section3.DiskNeutralIdentification
import EulerNonuniqueness.General.AffineInversePullbackBudget

noncomputable section

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

def movingStrainAffineSpectralPullback (state : PeriodicC1HolderHalf) (coefficient : ℂ) : PeriodicC1HolderHalf :=
  diskPhysicalSpectralInverseDerivative (diskPhysicalSpectralChart state)
    (movingStrainAffineResidual (diskStationaryChart (diskRelabelNeutralCLM state)) coefficient
      (diskPhysicalSpectralChart state))

theorem movingStrainAffineSpectralPullback_exists_relative_ball :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : PeriodicC1HolderHalf,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      initial ∈ contourContinuousVectorSubmodule → final ∈ contourContinuousVectorSubmodule →
      diskPhysicalSpectralChart initial ∈ contourContinuousVectorSubmodule →
      diskPhysicalSpectralChart final ∈ contourContinuousVectorSubmodule →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      contourCentroidFunctional (diskPhysicalSpectralChart initial) = 0 →
      contourCentroidFunctional (diskPhysicalSpectralChart final) = 0 →
      ∀ firstCoefficient finalCoefficient : ℂ,
      ‖movingStrainAffineSpectralPullback initial firstCoefficient -
        movingStrainAffineSpectralPullback final finalCoefficient‖ ≤ constant *
        ((‖firstCoefficient‖ + ‖finalCoefficient‖) *
          ((‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
              ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
            (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) ^ 2 *
              ‖diskNeutralCLM initial - diskNeutralCLM final‖) +
          ‖firstCoefficient - finalCoefficient‖ * ‖diskPhysicalTransverseProjection final‖ ^ 2) := by
  obtain ⟨relativeRadius, relativePositive, relativeConstant, relativeNonnegative, relativeBound⟩ :=
    movingStrainAffineResidual_exists_spectral_relative_ball
  obtain ⟨absoluteRadius, absolutePositive, absoluteConstant, absoluteNonnegative, absoluteBound⟩ :=
    movingStrainAffineResidual_exists_spectral_absolute_ball
  obtain ⟨inverseRadius, inversePositive, inverseConstant, inverseOne, inverseAbsolute, inverseDifference⟩ :=
    diskPhysicalSpectralChart_exists_uniform_firstOrder_bounds
  obtain ⟨stateRadius, statePositive, stateConstant, stateNonnegative, stateDifference⟩ :=
    diskSpectralTubularArea_exists_relative_state_bound
  have projectionNear : ∀ᶠ state in 𝓝 (0 : PeriodicC1HolderHalf),
      ‖diskPhysicalTransverseProjection state‖ < 1 / 2 := by
    have actual : ContinuousAt (fun state => diskPhysicalTransverseProjection state)
        (0 : PeriodicC1HolderHalf) := diskPhysicalTransverseProjection.continuous.continuousAt
    have convergence : Tendsto (fun state => ‖diskPhysicalTransverseProjection state‖)
        (𝓝 (0 : PeriodicC1HolderHalf)) (𝓝 (0 : ℝ)) := by
      simpa only [map_zero, norm_zero] using actual.norm.tendsto
    exact convergence.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨projectionRadius, projectionPositive, projectionContained⟩ := Metric.eventually_nhds_iff.mp projectionNear
  let radius := min relativeRadius (min absoluteRadius (min inverseRadius (min stateRadius projectionRadius)))
  let baseConstant := inverseConstant * (relativeConstant + stateConstant * absoluteConstant)
  let embeddingConstant := 1 + ‖diskMaterialNeutralEmbeddingCLM‖
  have inverseNonnegative : 0 ≤ inverseConstant := le_trans (by norm_num) inverseOne
  have baseNonnegative : 0 ≤ baseConstant := by dsimp [baseConstant]; positivity
  have embeddingOne : 1 ≤ embeddingConstant := by
    dsimp [embeddingConstant]
    linarith [norm_nonneg diskMaterialNeutralEmbeddingCLM]
  refine ⟨radius, by dsimp [radius]; positivity,
    baseConstant * embeddingConstant, mul_nonneg baseNonnegative (le_trans (by norm_num) embeddingOne), ?_⟩
  intro initial final initialInside finalInside initialMember finalMember firstPhysical finalPhysical
    initialArea finalArea firstCentered finalCentered firstCoefficient finalCoefficient
  have restrict {state : PeriodicC1HolderHalf} (inside : state ∈ ball 0 radius)
      {outer : ℝ} (bound : radius ≤ outer) : state ∈ ball 0 outer := ball_subset_ball bound inside
  have relativeLe : radius ≤ relativeRadius := min_le_left _ _
  have absoluteLe : radius ≤ absoluteRadius := (min_le_right _ _).trans (min_le_left _ _)
  have inverseLe : radius ≤ inverseRadius :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have stateLe : radius ≤ stateRadius :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have projectionLe : radius ≤ projectionRadius :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have firstInverseInside : ‖initial‖ ≤ inverseRadius :=
    (show ‖initial‖ < inverseRadius by simpa only [mem_ball, dist_zero_right] using restrict initialInside inverseLe).le
  have finalInverseInside : ‖final‖ ≤ inverseRadius :=
    (show ‖final‖ < inverseRadius by simpa only [mem_ball, dist_zero_right] using restrict finalInside inverseLe).le
  have rawRelative := relativeBound initial final (restrict initialInside relativeLe) (restrict finalInside relativeLe)
    initialMember finalMember firstPhysical finalPhysical initialArea finalArea firstCentered finalCentered
    firstCoefficient finalCoefficient
  have rawAbsolute := absoluteBound final (restrict finalInside absoluteLe) finalMember finalPhysical finalArea
    finalCentered finalCoefficient
  have inverseNorm := (inverseAbsolute initial firstInverseInside).2
  have inverseDiff := (inverseDifference initial final firstInverseInside finalInverseInside).2
  have states := stateDifference initial final (restrict initialInside stateLe) (restrict finalInside stateLe)
    initialArea finalArea
  have inverseRelative := inverseDiff.trans (mul_le_mul_of_nonneg_left states inverseNonnegative)
  have firstSize := projectionContained (by simpa only [mem_ball] using restrict initialInside projectionLe)
  have finalSize := projectionContained (by simpa only [mem_ball] using restrict finalInside projectionLe)
  have small : ‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖ ≤ 1 := by linarith
  let firstRaw := movingStrainAffineResidual (diskStationaryChart (diskRelabelNeutralCLM initial)) firstCoefficient
    (diskPhysicalSpectralChart initial)
  let finalRaw := movingStrainAffineResidual (diskStationaryChart (diskRelabelNeutralCLM final)) finalCoefficient
    (diskPhysicalSpectralChart final)
  let firstInverse := diskPhysicalSpectralInverseDerivative (diskPhysicalSpectralChart initial)
  let finalInverse := diskPhysicalSpectralInverseDerivative (diskPhysicalSpectralChart final)
  have vector : ‖firstInverse firstRaw - finalInverse finalRaw‖ ≤
      ‖firstInverse‖ * ‖firstRaw - finalRaw‖ + ‖firstInverse - finalInverse‖ * ‖finalRaw‖ := by
    with_reducible_and_instances
      exact EulerNonuniqueness.General.norm_operator_apply_difference_le firstInverse finalInverse firstRaw finalRaw
  have rawEstimate := add_le_add
    (mul_le_mul inverseNorm rawRelative (norm_nonneg _) inverseNonnegative)
    (mul_le_mul inverseRelative rawAbsolute (norm_nonneg _) (by positivity))
  have budget := EulerNonuniqueness.General.affine_inverse_pullback_relative_budget
    ‖diskPhysicalTransverseProjection initial‖ ‖diskPhysicalTransverseProjection final‖
    ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖
    ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖
    ‖firstCoefficient‖ ‖finalCoefficient‖ ‖firstCoefficient - finalCoefficient‖
    inverseConstant stateConstant relativeConstant absoluteConstant (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    inverseNonnegative stateNonnegative relativeNonnegative absoluteNonnegative small
  have embedding := diskRelabelNeutralCLM_difference_norm_le initial final
  have neutralBudget :
      (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
          ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
        (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) ^ 2 *
          ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖ ≤ embeddingConstant *
      ((‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
          ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
        (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) ^ 2 *
          ‖diskNeutralCLM initial - diskNeutralCLM final‖) := by
    have weighted := mul_le_mul_of_nonneg_left embedding
      (sq_nonneg (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖))
    dsimp only [embeddingConstant]
    nlinarith [mul_nonneg (norm_nonneg diskMaterialNeutralEmbeddingCLM)
      (mul_nonneg (add_nonneg (norm_nonneg (diskPhysicalTransverseProjection initial))
        (norm_nonneg (diskPhysicalTransverseProjection final))) (norm_nonneg
        (diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final))),
      mul_nonneg (sq_nonneg (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖))
        (norm_nonneg (diskNeutralCLM initial - diskNeutralCLM final))]
  have coefficientSquare : ‖firstCoefficient - finalCoefficient‖ * ‖diskPhysicalTransverseProjection final‖ ^ 2 ≤
      embeddingConstant * (‖firstCoefficient - finalCoefficient‖ * ‖diskPhysicalTransverseProjection final‖ ^ 2) :=
    le_mul_of_one_le_left (by positivity) embeddingOne
  have finalScalar := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left neutralBudget
      (show 0 ≤ ‖firstCoefficient‖ + ‖finalCoefficient‖ by positivity)) coefficientSquare) baseNonnegative
  have estimate : ‖movingStrainAffineSpectralPullback initial firstCoefficient -
      movingStrainAffineSpectralPullback final finalCoefficient‖ ≤
    baseConstant * embeddingConstant *
      ((‖firstCoefficient‖ + ‖finalCoefficient‖) *
        ((‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
            ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
          (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) ^ 2 *
            ‖diskNeutralCLM initial - diskNeutralCLM final‖) +
        ‖firstCoefficient - finalCoefficient‖ * ‖diskPhysicalTransverseProjection final‖ ^ 2) := by
    change ‖firstInverse firstRaw - finalInverse finalRaw‖ ≤ _
    with_reducible_and_instances
      apply (le_trans vector (le_trans rawEstimate (le_trans budget finalScalar))).trans_eq
      ring
  exact estimate

end EulerNonuniqueness.Paper
