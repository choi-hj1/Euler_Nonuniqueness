import EulerNonuniqueness.Section3.DiskSpectralQuadraticObservableC11
import EulerNonuniqueness.Section3.DiskNeutralIdentification
import EulerNonuniqueness.General.BilinearDiagonalDifference
import EulerNonuniqueness.General.LocalLipschitzBallBounds

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete
  chartedThirdBilinearGroup chartedThirdBilinearSpace chartedThirdBilinearComplete

local instance spectralQuadraticWeightedInverseC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskSpectralQuadraticObservable_exists_weighted_inverse_ball :
    ∃ radius > 0, ∃ constant ≥ 1, ∀ initial final : PeriodicC1HolderHalf,
      ‖diskRelabelNeutralCLM initial‖ ≤ radius → ‖diskRelabelNeutralCLM final‖ ≤ radius →
      ∀ {weight : ℝ}, 0 ≤ weight →
      ‖diskPhysicalTransverseProjection initial‖ ≤ weight → ‖diskPhysicalTransverseProjection final‖ ≤ weight →
      constant * weight ≤ 1 / 2 →
      ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
        weight * ‖diskNeutralCLM initial - diskNeutralCLM final‖ ≤
      2 * (‖diskSpectralQuadraticObservable initial - diskSpectralQuadraticObservable final‖ +
        weight * ‖diskNeutralCLM initial - diskNeutralCLM final‖) := by
  obtain ⟨radius, positive, coefficientConstant, coefficientOne, absolute, relative⟩ :=
    diskSpectralMovingQuadraticCorrection_lipschitzNear.exists_closedBall_bounds
  let constant := 2 * coefficientConstant * (1 + ‖diskMaterialNeutralEmbeddingCLM‖) + 1
  have coefficientNonnegative : 0 ≤ coefficientConstant := by linarith
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ 2 * coefficientConstant * (1 + ‖diskMaterialNeutralEmbeddingCLM‖) := by positivity
    dsimp only [constant]
    linarith
  refine ⟨radius, positive, constant, constantOne, ?_⟩
  intro initial final initialInside finalInside weight weightNonnegative firstBound finalBound small
  let firstCoefficient := diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM initial)
  let finalCoefficient := diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM final)
  have coefficientBound := absolute (diskRelabelNeutralCLM initial) initialInside
  have coefficientPair := (relative (diskRelabelNeutralCLM initial) (diskRelabelNeutralCLM final) initialInside finalInside).trans
    (mul_le_mul_of_nonneg_left (diskRelabelNeutralCLM_difference_norm_le initial final) coefficientNonnegative)
  have diagonal := EulerNonuniqueness.General.norm_bilinear_diagonal_difference_le firstCoefficient finalCoefficient
    (diskPhysicalTransverseProjection initial) (diskPhysicalTransverseProjection final)
  have pointSum : ‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖ ≤ 2 * weight := by linarith
  have diagonalBound := diagonal.trans (add_le_add
    (mul_le_mul_of_nonneg_right
      (mul_le_mul coefficientBound pointSum (by positivity) (by positivity)) (norm_nonneg _))
    (mul_le_mul coefficientPair (pow_le_pow_left₀ (norm_nonneg _) finalBound 2)
      (by positivity) (by positivity)))
  have deviationIdentity :
      (diskSpectralQuadraticObservable initial - diskPhysicalTransverseProjection initial) -
        (diskSpectralQuadraticObservable final - diskPhysicalTransverseProjection final) =
      -(firstCoefficient (diskPhysicalTransverseProjection initial) (diskPhysicalTransverseProjection initial) -
        finalCoefficient (diskPhysicalTransverseProjection final) (diskPhysicalTransverseProjection final)) := by
    simp only [diskSpectralQuadraticObservable, EulerNonuniqueness.General.quadraticCoordinate, div_one, one_smul,
      firstCoefficient, finalCoefficient]
    abel
  have deviation : ‖(diskSpectralQuadraticObservable initial - diskPhysicalTransverseProjection initial) -
      (diskSpectralQuadraticObservable final - diskPhysicalTransverseProjection final)‖ ≤
      constant * weight * (‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
        weight * ‖diskNeutralCLM initial - diskNeutralCLM final‖) := by
    rw [deviationIdentity, norm_neg]
    apply diagonalBound.trans
    dsimp only [constant]
    have nonnegative : 0 ≤
      (2 * coefficientConstant * ‖diskMaterialNeutralEmbeddingCLM‖ + 1) * weight *
        ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
      (2 * coefficientConstant + coefficientConstant * ‖diskMaterialNeutralEmbeddingCLM‖ + 1) * weight ^ 2 *
        ‖diskNeutralCLM initial - diskNeutralCLM final‖ := by positivity
    nlinarith only [nonnegative]
  have identity : diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final =
      (diskSpectralQuadraticObservable initial - diskSpectralQuadraticObservable final) -
        ((diskSpectralQuadraticObservable initial - diskPhysicalTransverseProjection initial) -
          (diskSpectralQuadraticObservable final - diskPhysicalTransverseProjection final)) := by abel
  have triangle : ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ ≤
      ‖diskSpectralQuadraticObservable initial - diskSpectralQuadraticObservable final‖ +
        constant * weight * (‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
          weight * ‖diskNeutralCLM initial - diskNeutralCLM final‖) := by
    calc
      _ = ‖(diskSpectralQuadraticObservable initial - diskSpectralQuadraticObservable final) -
          ((diskSpectralQuadraticObservable initial - diskPhysicalTransverseProjection initial) -
            (diskSpectralQuadraticObservable final - diskPhysicalTransverseProjection final))‖ := congrArg norm identity
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add_left deviation _)
  have absorbed := mul_le_mul_of_nonneg_right small (by positivity : 0 ≤
    ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
      weight * ‖diskNeutralCLM initial - diskNeutralCLM final‖)
  have halfTriangle := triangle.trans (add_le_add_left absorbed
    ‖diskSpectralQuadraticObservable initial - diskSpectralQuadraticObservable final‖)
  have absorb (first final neutral : ℝ) (bound : first ≤ final + 1 / 2 * (first + neutral)) :
      first + neutral ≤ 2 * (final + neutral) := by linarith
  exact absorb _ _ _ halfTriangle

end EulerNonuniqueness.Paper
