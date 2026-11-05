import EulerNonuniqueness.Section3.MovingPaperSpectralBoundaryControl
import EulerNonuniqueness.Section3.DiskNormalizedTransverseRecovery

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

attribute [local instance] spectralBoundaryControlC1Group chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

theorem exists_boundaryCloseToCircle_of_corrected_normalized_observable :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
        (time : ℝ) (index : Fin count) (patch : Fin 4),
      (family.patch (finProdFinEquiv (index, patch))).radius = scales.radius (index.val + 1) →
      (family.patch (finProdFinEquiv (index, patch))).center time =
        Paper.patchCentroid family.patchMotion time index patch →
      (family.patch (finProdFinEquiv (index, patch))).phase time =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4 * time / 2 →
      ∀ corrected : PeriodicC1HolderHalf,
      ‖(family.patch (finProdFinEquiv (index, patch))).shape time - standardCircleBanach‖ +
        ‖(family.patch (finProdFinEquiv (index, patch))).shape time - corrected‖ ≤ radius →
      contourAreaFunctional ((family.patch (finProdFinEquiv (index, patch))).shape time) = Real.pi →
      contourCentroidFunctional ((family.patch (finProdFinEquiv (index, patch))).shape time) = 0 →
      ∀ bound : ℝ,
      constant * (‖diskSpectralQuadraticObservable (diskPhysicalSpectralCoordinate
        (contourAreaCentroidNormalization corrected))‖ +
        ‖(family.patch (finProdFinEquiv (index, patch))).shape time - corrected‖) ≤ bound →
      BoundaryCloseToCircle scales family.patchMotion time index patch bound := by
  obtain ⟨boundaryRadius, boundaryPositive, boundaryConstant, boundaryOne, boundaryControl⟩ :=
    exists_boundaryCloseToCircle_of_area_spectral_coordinate
  obtain ⟨recoveryRadius, recoveryPositive, recoveryConstant, recoveryOne, recovery⟩ :=
    diskNormalizedQuadraticObservable_exists_uniform_transverse_recovery
  let radius := min recoveryRadius (boundaryRadius / 2)
  let constant := boundaryConstant * recoveryConstant
  refine ⟨radius, by dsimp only [radius]; positivity, constant, by dsimp only [constant]; nlinarith, ?_⟩
  intro count family scales time index patch radiusIdentity centerIdentity phaseIdentity corrected small area centered bound observed
  let data := (family.patch (finProdFinEquiv (index, patch))).shape time
  have near : ‖data - standardCircleBanach‖ < boundaryRadius := by
    have actual := small.trans (min_le_right _ _)
    linarith [norm_nonneg (data - corrected)]
  have recovered := recovery data corrected (small.trans (min_le_left _ _)) area centered
  have boundaryAt := boundaryControl family scales time index patch radiusIdentity centerIdentity phaseIdentity near area bound
  generalize originalEq : diskPhysicalTransverseProjection (diskPhysicalSpectralCoordinate data) = originalProjection
    at recovered boundaryAt
  generalize observableEq : diskSpectralQuadraticObservable
    (diskPhysicalSpectralCoordinate (contourAreaCentroidNormalization corrected)) = observable at recovered observed
  apply boundaryAt
  have actual := mul_le_mul_of_nonneg_left recovered (by linarith : 0 ≤ boundaryConstant)
  have scalar : boundaryConstant * (recoveryConstant *
      (‖observable‖ +
        ‖data - corrected‖)) ≤ bound := by
    rw [← mul_assoc]
    exact observed
  exact actual.trans scalar

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
