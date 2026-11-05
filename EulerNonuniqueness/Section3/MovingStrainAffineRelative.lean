import EulerNonuniqueness.Section3.MovingStrainAffineCentroidRelative
import EulerNonuniqueness.Section3.MovingStrainAffineTaylorRelative
import EulerNonuniqueness.General.RelativeRemainderRecombination
import EulerNonuniqueness.Section3.MovingStrainAffineValueDifference

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group independentRealificationOutputGroup
  independentRealificationInputGroup forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityBilinearGroup secondIdentityBilinearModule
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

theorem movingStrainAffineResidual_exists_relative_quadratic_ball :
    ∃ radius > 0, ∃ constant ≥ 0,
      ∀ initialAngular finalAngular : PeriodicC1HolderHalf,
      ∀ (initialSmall : ‖initialAngular‖ < 1 / 2) (finalSmall : ‖finalAngular‖ < 1 / 2),
      initialAngular ∈ contourContinuousVectorSubmodule → finalAngular ∈ contourContinuousVectorSubmodule →
      let initialBase := fixedRelabelEquivalence initialAngular initialSmall standardCircleBanach
      let finalBase := fixedRelabelEquivalence finalAngular finalSmall standardCircleBanach
      ‖initialBase - standardCircleBanach‖ < min (1 / 3) (min 1 (2 / (3 * Real.pi))) →
      ‖finalBase - standardCircleBanach‖ < min (1 / 3) (min 1 (2 / (3 * Real.pi))) →
      ∀ initialIncrement finalIncrement : PeriodicC1HolderHalf,
      initialIncrement ∈ contourContinuousVectorSubmodule → finalIncrement ∈ contourContinuousVectorSubmodule →
      ‖initialBase - standardCircleBanach‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖finalBase - standardCircleBanach‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      contourCentroidFunctional (initialBase + initialIncrement) = contourCentroidFunctional initialBase →
      contourCentroidFunctional (finalBase + finalIncrement) = contourCentroidFunctional finalBase →
      ∀ coefficient : ℂ,
      ‖movingStrainAffineResidual initialBase coefficient (initialBase + initialIncrement) -
        movingStrainAffineResidual finalBase coefficient (finalBase + finalIncrement)‖ ≤
      constant * ‖coefficient‖ *
        ((‖initialIncrement‖ + ‖finalIncrement‖) * ‖initialIncrement - finalIncrement‖ +
          ‖initialBase - finalBase‖ * (‖initialIncrement‖ + ‖finalIncrement‖) ^ 2) := by
  obtain ⟨linearRadius, linearPositive, linearConstant, linearNonnegative, linearBound⟩ :=
    movingStrainAffineLinearResidualCLM_exists_relative_constraint_ball
  obtain ⟨taylorRadius, taylorPositive, taylorConstant, taylorNonnegative, taylorBound⟩ :=
    movingStrainAffineTaylorRemainder_exists_relative_quadratic_ball
  refine ⟨min linearRadius taylorRadius, lt_min linearPositive taylorPositive,
    linearConstant + taylorConstant, add_nonneg linearNonnegative taylorNonnegative, ?_⟩
  intro initialAngular finalAngular initialSmall finalSmall initialMember finalMember initialBase finalBase
    initialNearby finalNearby initialIncrement finalIncrement initialIncrementMember finalIncrementMember
    initialInside finalInside initialCentroid finalCentroid coefficient
  have linear := linearBound initialAngular finalAngular initialSmall finalSmall initialMember finalMember
    initialNearby finalNearby initialIncrement finalIncrement initialIncrementMember finalIncrementMember
    (initialInside.trans (min_le_left _ _)) (finalInside.trans (min_le_left _ _)) initialCentroid finalCentroid coefficient
  have taylor := taylorBound initialBase finalBase initialIncrement finalIncrement
    (initialInside.trans (min_le_right _ _)) (finalInside.trans (min_le_right _ _)) initialCentroid finalCentroid coefficient
  have vector := movingStrainAffineResidual_pair_norm_le initialAngular finalAngular
    initialSmall finalSmall initialNearby finalNearby coefficient initialIncrement finalIncrement
  have merge (firstConstant secondConstant amplitude budget : ℝ) :
      firstConstant * amplitude * budget + secondConstant * amplitude * budget =
        (firstConstant + secondConstant) * amplitude * budget := by ring
  have scalar := merge linearConstant taylorConstant ‖coefficient‖
    ((‖initialIncrement‖ + ‖finalIncrement‖) * ‖initialIncrement - finalIncrement‖ +
      ‖initialBase - finalBase‖ * (‖initialIncrement‖ + ‖finalIncrement‖) ^ 2)
  have sum := add_le_add linear taylor
  have result :
      ‖movingStrainAffineResidual initialBase coefficient (initialBase + initialIncrement) -
        movingStrainAffineResidual finalBase coefficient (finalBase + finalIncrement)‖ ≤
      linearConstant * ‖coefficient‖ *
        ((‖initialIncrement‖ + ‖finalIncrement‖) * ‖initialIncrement - finalIncrement‖ +
          ‖initialBase - finalBase‖ * (‖initialIncrement‖ + ‖finalIncrement‖) ^ 2) +
      taylorConstant * ‖coefficient‖ *
        ((‖initialIncrement‖ + ‖finalIncrement‖) * ‖initialIncrement - finalIncrement‖ +
          ‖initialBase - finalBase‖ * (‖initialIncrement‖ + ‖finalIncrement‖) ^ 2) := by
    with_reducible_and_instances
      exact le_trans vector sum
  with_reducible_and_instances
    exact result.trans_eq scalar

end EulerNonuniqueness.Paper
