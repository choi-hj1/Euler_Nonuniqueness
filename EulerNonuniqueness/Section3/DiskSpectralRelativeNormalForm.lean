import EulerNonuniqueness.Section3.DiskSpectralMovingSelfDecomposition
import EulerNonuniqueness.Section3.DiskSpectralMovingTransverseCubic
import EulerNonuniqueness.Section3.DiskSpectralMovingNeutralCubic
import EulerNonuniqueness.General.FrozenQuadraticValueDecomposition
import EulerNonuniqueness.Section3.DiskSpectralMovingSelfValueIdentities
import EulerNonuniqueness.General.MovingQuadraticRemainderValue

namespace EulerNonuniqueness.Paper

noncomputable section

open Metric

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete
  chartedThirdBilinearGroup chartedThirdBilinearSpace chartedThirdBilinearComplete

local instance relativeNormalFormC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskSpectralMovingSelfRemainder_eq_three_terms (state : PeriodicC1HolderHalf) :
    diskSpectralMovingSelfRemainder state =
      diskPhysicalTransverseProjection (diskSpectralTubularPhysicalCubicRemainder state) -
        diskSpectralMovingTransverseCorrection state - diskSpectralMovingNeutralCorrection state := by
  let differential : PeriodicC1HolderHalf →L[ℝ]
      EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf :=
    fderiv ℝ diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM state)
  have velocity := diskSpectralTransverseNonlinearField_eq_projectedQuadratic state
  have neutral := diskSpectralNeutralField_eq_quadratic_add_remainder state
  dsimp only at neutral
  have neutralEquation := neutral.trans (congrArg
    (fun value : PeriodicC1HolderHalf => diskRelabelNeutralCLM
      (diskSpectralFiberQuadraticBilinear state value value) +
        diskRelabelNeutralCLM (diskSpectralTubularPhysicalCubicRemainder state))
    (diskSpectralPhysicalTransverse_eq_projection state))
  unfold diskSpectralMovingSelfRemainder diskSpectralMovingTransverseCorrection
    diskSpectralMovingNeutralCorrection
  with_reducible_and_instances
    exact EulerNonuniqueness.General.movingQuadraticSelfRemainder_eq_three_values
      diskPhysicalTransverseProjection diskRelabelNeutralCLM diskSpectralProjectedQuadratic
      diskSpectralMovingQuadraticCorrection diskSpectralFiberQuadraticBilinear differential state
      (diskSpectralTubularPhysicalCubicRemainder state) (diskSpectralTransverseNonlinearField state)
      (diskRelabelNeutralCLM (diskSpectralTubularEulerField state)) velocity neutralEquation
      (diskSpectralMovingQuadraticCorrection_neutral_parameter state)

theorem diskSpectralMovingSelfRemainder_exists_relative_cubic_ball :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : PeriodicC1HolderHalf,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      ‖diskSpectralMovingSelfRemainder initial - diskSpectralMovingSelfRemainder final‖ ≤ constant *
        ((‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) ^ 2 *
          ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
          (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) ^ 3 *
            ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖) := by
  have raw := diskSpectralTubularPhysicalCubicRemainder_exists_relative_physical_ball
  simp only [diskSpectralPhysicalTransverse_eq_projection] at raw
  obtain ⟨rawRadius, rawPositive, rawConstant, rawNonnegative, rawBound⟩ := raw
  obtain ⟨transverseRadius, transversePositive, transverseConstant, transverseNonnegative, transverseBound⟩ :=
    diskSpectralMovingTransverseCorrection_exists_relative_cubic_ball
  obtain ⟨neutralRadius, neutralPositive, neutralConstant, neutralNonnegative, neutralBound⟩ :=
    diskSpectralMovingNeutralCorrection_exists_relative_cubic_ball
  refine ⟨min rawRadius (min transverseRadius neutralRadius), lt_min rawPositive (lt_min transversePositive neutralPositive),
    ‖diskPhysicalTransverseProjection‖ * rawConstant + transverseConstant + neutralConstant, by positivity, ?_⟩
  intro initial final initialInside finalInside initialArea finalArea
  have initialRaw := ball_subset_ball (min_le_left _ _) initialInside
  have finalRaw := ball_subset_ball (min_le_left _ _) finalInside
  have initialOther := ball_subset_ball (min_le_right _ _) initialInside
  have finalOther := ball_subset_ball (min_le_right _ _) finalInside
  have first := rawBound initial final initialRaw finalRaw initialArea finalArea
  have second := transverseBound initial final (ball_subset_ball (min_le_left _ _) initialOther)
    (ball_subset_ball (min_le_left _ _) finalOther) initialArea finalArea
  have third := neutralBound initial final (ball_subset_ball (min_le_right _ _) initialOther)
    (ball_subset_ball (min_le_right _ _) finalOther) initialArea finalArea
  rw [diskSpectralMovingSelfRemainder_eq_three_terms initial, diskSpectralMovingSelfRemainder_eq_three_terms final]
  have identity (firstInitial secondInitial thirdInitial firstFinal secondFinal thirdFinal : PeriodicC1HolderHalf) :
      (diskPhysicalTransverseProjection firstInitial - secondInitial - thirdInitial) -
        (diskPhysicalTransverseProjection firstFinal - secondFinal - thirdFinal) =
      diskPhysicalTransverseProjection (firstInitial - firstFinal) -
        (secondInitial - secondFinal) - (thirdInitial - thirdFinal) := by
    rw [map_sub]
    abel
  rw [identity (diskSpectralTubularPhysicalCubicRemainder initial)
    (diskSpectralMovingTransverseCorrection initial) (diskSpectralMovingNeutralCorrection initial)
    (diskSpectralTubularPhysicalCubicRemainder final)
    (diskSpectralMovingTransverseCorrection final) (diskSpectralMovingNeutralCorrection final)]
  have estimate : ‖diskPhysicalTransverseProjection
        (diskSpectralTubularPhysicalCubicRemainder initial - diskSpectralTubularPhysicalCubicRemainder final) -
        (diskSpectralMovingTransverseCorrection initial - diskSpectralMovingTransverseCorrection final) -
        (diskSpectralMovingNeutralCorrection initial - diskSpectralMovingNeutralCorrection final)‖ ≤
      ‖diskPhysicalTransverseProjection‖ *
        ‖diskSpectralTubularPhysicalCubicRemainder initial - diskSpectralTubularPhysicalCubicRemainder final‖ +
        ‖diskSpectralMovingTransverseCorrection initial - diskSpectralMovingTransverseCorrection final‖ +
        ‖diskSpectralMovingNeutralCorrection initial - diskSpectralMovingNeutralCorrection final‖ :=
    (norm_sub_le _ _).trans (add_le_add_right
      ((norm_sub_le _ _).trans (add_le_add_right (diskPhysicalTransverseProjection.le_opNorm _) _)) _)
  exact estimate.trans ((add_le_add (add_le_add (mul_le_mul_of_nonneg_left first (norm_nonneg _)) second) third).trans_eq (by ring))

end

end EulerNonuniqueness.Paper
