import EulerNonuniqueness.Section3.MovingStrainAffineAbsolute
import EulerNonuniqueness.Section3.MovingStrainAffineCoefficientLinearity

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem movingStrainAffineResidual_exists_amplitude_relative_quadratic_ball :
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
      ∀ firstCoefficient finalCoefficient : ℂ,
      ‖movingStrainAffineResidual initialBase firstCoefficient (initialBase + initialIncrement) -
        movingStrainAffineResidual finalBase finalCoefficient (finalBase + finalIncrement)‖ ≤ constant *
        (‖firstCoefficient‖ *
          ((‖initialIncrement‖ + ‖finalIncrement‖) * ‖initialIncrement - finalIncrement‖ +
            ‖initialBase - finalBase‖ * (‖initialIncrement‖ + ‖finalIncrement‖) ^ 2) +
          ‖firstCoefficient - finalCoefficient‖ * ‖finalIncrement‖ ^ 2) := by
  obtain ⟨relativeRadius, relativePositive, relativeConstant, relativeNonnegative, relativeBound⟩ :=
    movingStrainAffineResidual_exists_relative_quadratic_ball
  obtain ⟨absoluteRadius, absolutePositive, absoluteConstant, absoluteNonnegative, absoluteBound⟩ :=
    movingStrainAffineResidual_exists_absolute_quadratic_ball
  refine ⟨min relativeRadius absoluteRadius, lt_min relativePositive absolutePositive,
    relativeConstant + absoluteConstant, add_nonneg relativeNonnegative absoluteNonnegative, ?_⟩
  intro initialAngular finalAngular initialSmall finalSmall initialMember finalMember initialBase finalBase
    initialNearby finalNearby initialIncrement finalIncrement initialIncrementMember finalIncrementMember
    initialInside finalInside initialCentroid finalCentroid firstCoefficient finalCoefficient
  have relative := relativeBound initialAngular finalAngular initialSmall finalSmall initialMember finalMember
    initialNearby finalNearby initialIncrement finalIncrement initialIncrementMember finalIncrementMember
    (initialInside.trans (min_le_left _ _)) (finalInside.trans (min_le_left _ _)) initialCentroid finalCentroid firstCoefficient
  have finalSingle : ‖finalBase - standardCircleBanach‖ + ‖finalIncrement‖ ≤ absoluteRadius := by
    have bound := finalInside.trans (min_le_right relativeRadius absoluteRadius)
    linarith [norm_nonneg initialIncrement]
  have absolute := absoluteBound finalAngular finalSmall finalMember finalNearby finalIncrement finalIncrementMember
    finalSingle finalCentroid (firstCoefficient - finalCoefficient)
  have coefficientIdentity := movingStrainAffineResidual_sub_coefficient finalBase (finalBase + finalIncrement)
    firstCoefficient finalCoefficient
  have finalDifference : ‖movingStrainAffineResidual finalBase firstCoefficient (finalBase + finalIncrement) -
      movingStrainAffineResidual finalBase finalCoefficient (finalBase + finalIncrement)‖ ≤
      absoluteConstant * ‖firstCoefficient - finalCoefficient‖ * ‖finalIncrement‖ ^ 2 := by
    rw [coefficientIdentity]
    with_reducible_and_instances
      exact absolute
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (movingStrainAffineResidual initialBase firstCoefficient (initialBase + initialIncrement))
    (movingStrainAffineResidual finalBase firstCoefficient (finalBase + finalIncrement))
    (movingStrainAffineResidual finalBase finalCoefficient (finalBase + finalIncrement))
  have total :
      ‖movingStrainAffineResidual initialBase firstCoefficient (initialBase + initialIncrement) -
        movingStrainAffineResidual finalBase finalCoefficient (finalBase + finalIncrement)‖ ≤
      relativeConstant * ‖firstCoefficient‖ *
        ((‖initialIncrement‖ + ‖finalIncrement‖) * ‖initialIncrement - finalIncrement‖ +
          ‖initialBase - finalBase‖ * (‖initialIncrement‖ + ‖finalIncrement‖) ^ 2) +
      absoluteConstant * ‖firstCoefficient - finalCoefficient‖ * ‖finalIncrement‖ ^ 2 := by
    with_reducible_and_instances
      exact le_trans triangle (add_le_add relative finalDifference)
  apply total.trans
  calc
    _ = relativeConstant * (‖firstCoefficient‖ *
          ((‖initialIncrement‖ + ‖finalIncrement‖) * ‖initialIncrement - finalIncrement‖ +
            ‖initialBase - finalBase‖ * (‖initialIncrement‖ + ‖finalIncrement‖) ^ 2)) +
        absoluteConstant * (‖firstCoefficient - finalCoefficient‖ * ‖finalIncrement‖ ^ 2) := by ring
    _ ≤ (relativeConstant + absoluteConstant) * (‖firstCoefficient‖ *
          ((‖initialIncrement‖ + ‖finalIncrement‖) * ‖initialIncrement - finalIncrement‖ +
            ‖initialBase - finalBase‖ * (‖initialIncrement‖ + ‖finalIncrement‖) ^ 2)) +
        (relativeConstant + absoluteConstant) * (‖firstCoefficient - finalCoefficient‖ * ‖finalIncrement‖ ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right absoluteNonnegative) (by positivity))
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left relativeNonnegative) (by positivity))
    _ = _ := by ring

end EulerNonuniqueness.Paper
