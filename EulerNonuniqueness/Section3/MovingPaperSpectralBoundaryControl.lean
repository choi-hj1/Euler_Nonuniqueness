import EulerNonuniqueness.Section3.DiskPhysicalSpectralRelabelDefect
import EulerNonuniqueness.Section3.MovingPaperRelabeledBoundaryControl

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

local instance spectralBoundaryControlC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd

theorem exists_boundaryCloseToCircle_of_area_spectral_coordinate :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
        (time : ℝ) (index : Fin count) (patch : Fin 4),
      (family.patch (finProdFinEquiv (index, patch))).radius = scales.radius (index.val + 1) →
      (family.patch (finProdFinEquiv (index, patch))).center time =
        Paper.patchCentroid family.patchMotion time index patch →
      (family.patch (finProdFinEquiv (index, patch))).phase time =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4 * time / 2 →
      ‖(family.patch (finProdFinEquiv (index, patch))).shape time - standardCircleBanach‖ < radius →
      contourAreaFunctional ((family.patch (finProdFinEquiv (index, patch))).shape time) = Real.pi →
      ∀ bound : ℝ,
      constant * ‖diskPhysicalTransverseProjection (diskPhysicalSpectralCoordinate
        ((family.patch (finProdFinEquiv (index, patch))).shape time))‖ ≤ bound →
      BoundaryCloseToCircle scales family.patchMotion time index patch bound := by
  obtain ⟨defectRadius, defectPositive, defectConstant, defectOne, defect⟩ :=
    diskPhysicalSpectralCoordinate_exists_uniform_relabel_defect
  let angularNorm := ‖diskNeutralCLM‖
  have angularNonnegative : 0 ≤ angularNorm := norm_nonneg _
  let tubeRadius := 1 / (24 * (angularNorm + 1))
  have tubePositive : 0 < tubeRadius := by dsimp only [tubeRadius]; positivity
  obtain ⟨coordinateRadius, coordinatePositive, coordinates⟩ := diskPhysicalSpectralCoordinate_exists_radius tubePositive
  refine ⟨min defectRadius coordinateRadius, lt_min defectPositive coordinatePositive,
    3 * defectConstant, by linarith, ?_⟩
  intro count family scales time index patch radiusIdentity centerIdentity phaseIdentity nearby area bound projected
  let data := (family.patch (finProdFinEquiv (index, patch))).shape time
  have dataNear : ‖data - standardCircleBanach‖ < coordinateRadius := nearby.trans_le (min_le_right _ _)
  have tube := (coordinates data dataNear).2.2.1
  have neutralSmall : ‖diskRelabelNeutralCLM (diskPhysicalSpectralCoordinate data)‖ ≤ tubeRadius := by
    linarith [norm_nonneg (diskPhysicalSpectralCoordinate data - diskRelabelNeutralCLM (diskPhysicalSpectralCoordinate data))]
  have angularBound := diskNeutralCLM_norm_le_relabelNeutral (diskPhysicalSpectralCoordinate data)
  have angularSmall : 3 * ‖diskNeutralCLM (diskPhysicalSpectralCoordinate data)‖ ≤ 1 / 8 := by
    have product := mul_le_mul_of_nonneg_left neutralSmall angularNonnegative
    have denominatorPositive : 0 < 24 * (angularNorm + 1) := by positivity
    have ratioBound : angularNorm * tubeRadius ≤ 1 / 24 := by
      dsimp only [tubeRadius]
      rw [mul_one_div]
      apply (div_le_iff₀ denominatorPositive).mpr
      linarith
    have scalar : ‖diskNeutralCLM (diskPhysicalSpectralCoordinate data)‖ ≤ 1 / 24 :=
      angularBound.trans (product.trans ratioBound)
    linarith
  apply family.boundaryCloseToCircle_of_relabel_defect scales time index patch radiusIdentity centerIdentity
    phaseIdentity (diskNeutralCLM (diskPhysicalSpectralCoordinate data))
    (diskNeutralCLM_real _) angularSmall
  have actualDefect := defect data (nearby.trans_le (min_le_left _ _)) area
  exact (mul_le_mul_of_nonneg_left actualDefect (by norm_num : (0 : ℝ) ≤ 3)).trans
    (by convert projected using 1 <;> ring)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
