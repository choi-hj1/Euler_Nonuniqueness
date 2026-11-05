import EulerNonuniqueness.Section3.DiskNormalizedQuadraticObservable
import EulerNonuniqueness.Section3.DiskSpectralMovingQuadraticRegularity
import EulerNonuniqueness.General.QuadraticObservableC11
import EulerNonuniqueness.General.LocalC1LipschitzBounds

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

local instance spectralQuadraticObservableC11Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskSpectralQuadraticObservable_hasLipschitzDerivativeNear_zero :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear diskSpectralQuadraticObservable
      (0 : PeriodicC1HolderHalf) := by
  have neutralRegular := EulerNonuniqueness.General.hasLipschitzDerivativeNear_continuousLinearMap
    diskRelabelNeutralCLM (0 : PeriodicC1HolderHalf)
  have transverseRegular := EulerNonuniqueness.General.hasLipschitzDerivativeNear_continuousLinearMap
    diskPhysicalTransverseProjection (0 : PeriodicC1HolderHalf)
  have coefficientRegular : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fun state => diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM state)) (0 : PeriodicC1HolderHalf) := by
    apply EulerNonuniqueness.General.HasLipschitzDerivativeNear.comp
      (outer := diskSpectralMovingQuadraticCorrection) (inner := diskRelabelNeutralCLM)
    · simpa only [map_zero] using diskSpectralMovingQuadraticCorrection_hasLipschitzDerivativeNear
    · exact neutralRegular
  have actual := EulerNonuniqueness.General.hasLipschitzDerivativeNear_quadraticCoordinate coefficientRegular transverseRegular
  with_reducible_and_instances
    convert (config := { transparency := .all }) actual using 1
    all_goals first
      | (change (_ : TopologicalSpace PeriodicC1HolderHalf) = _; with_unfolding_all rfl)
      | (funext state; simp only [diskSpectralQuadraticObservable, EulerNonuniqueness.General.quadraticCoordinate,
          div_one, one_smul])
      | rfl

theorem diskSpectralQuadraticObservable_exists_uniform_derivative_ball :
    ∃ radius > 0, ∃ constant ≥ 1,
      (∀ state : PeriodicC1HolderHalf, ‖state‖ ≤ radius →
        HasFDerivAt diskSpectralQuadraticObservable (fderiv ℝ diskSpectralQuadraticObservable state) state ∧
          ‖fderiv ℝ diskSpectralQuadraticObservable state‖ ≤ constant) ∧
      ∀ first final : PeriodicC1HolderHalf, ‖first‖ ≤ radius → ‖final‖ ≤ radius →
        ‖fderiv ℝ diskSpectralQuadraticObservable first - fderiv ℝ diskSpectralQuadraticObservable final‖ ≤
          constant * ‖first - final‖ := by
  obtain ⟨radius, positive, constant, one, differentiable, absolute, relative⟩ :=
    diskSpectralQuadraticObservable_hasLipschitzDerivativeNear_zero.exists_uniform_derivative_ball
  refine ⟨radius, positive, constant, one, ?_, ?_⟩
  · intro state nearby
    have inside : ‖state - 0‖ ≤ radius := by simpa only [sub_zero] using nearby
    exact ⟨(differentiable state inside).hasFDerivAt, absolute state inside⟩
  · intro first final firstInside finalInside
    exact relative first final (by simpa only [sub_zero] using firstInside) (by simpa only [sub_zero] using finalInside)

end EulerNonuniqueness.Paper
