import EulerNonuniqueness.Section3.MovingPaperRelabeledBoundaryControl
import EulerNonuniqueness.Section3.DiskStationaryRelabelDefect

noncomputable section

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance projectedPaperHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance projectedPaperC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance projectedPaperOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

namespace FiniteMovingPatchFamily

theorem exists_boundaryCloseToCircle_of_area_projected_chart :
    ∃ chartRadius > 0, ∀ {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
      (time : ℝ) (index : Fin count) (patch : Fin 4),
      (family.patch (finProdFinEquiv (index, patch))).radius = scales.radius (index.val + 1) →
      (family.patch (finProdFinEquiv (index, patch))).center time =
        Paper.patchCentroid family.patchMotion time index patch →
      (family.patch (finProdFinEquiv (index, patch))).phase time =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4 * time / 2 →
      ∀ increment : PeriodicC1HolderHalf,
      (family.patch (finProdFinEquiv (index, patch))).shape time = diskStationaryChart increment →
      ‖diskRelabelNeutralCLM increment‖ + ‖increment - diskRelabelNeutralCLM increment‖ ≤ chartRadius →
      diskStationaryArea increment = Real.pi →
      ∀ bound : ℝ, 12 * ‖diskPhysicalTransverseProjection increment‖ ≤ bound →
      BoundaryCloseToCircle scales family.patchMotion time index patch bound := by
  obtain ⟨radius, positive, estimate⟩ := diskStationaryArea_exists_projected_relabel_defect_bound
  let neutralNorm : ℝ := ‖diskNeutralCLM‖
  have neutralNormNonnegative : 0 ≤ neutralNorm := norm_nonneg _
  refine ⟨min radius (1 / (24 * (neutralNorm + 1))),
    lt_min positive (by positivity), ?_⟩
  intro count family scales time index patch radiusIdentity centerIdentity phaseIdentity increment shape inside area bound projected
  have reconstruction : diskRelabelNeutralCLM increment + (increment - diskRelabelNeutralCLM increment) = increment := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change (diskRelabelNeutralCLM increment).val.1 label +
      (increment.val.1 label - (diskRelabelNeutralCLM increment).val.1 label) = increment.val.1 label
    ring
  have incrementNorm : ‖increment‖ ≤ ‖diskRelabelNeutralCLM increment‖ +
      ‖increment - diskRelabelNeutralCLM increment‖ := by
    nth_rw 1 [← reconstruction]
    with_reducible
      exact norm_add_le (diskRelabelNeutralCLM increment) (increment - diskRelabelNeutralCLM increment)
  have angularBound : ‖diskNeutralCLM increment‖ ≤ neutralNorm * ‖increment‖ := by
    with_reducible
      exact ContinuousLinearMap.le_opNorm (𝕜 := ℝ) (𝕜₂ := ℝ) (σ₁₂ := RingHom.id ℝ)
        (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) diskNeutralCLM increment
  have sizeBound := (le_div_iff₀ (by positivity : 0 < 24 * (neutralNorm + 1))).mp
    (incrementNorm.trans (inside.trans (min_le_right _ _)))
  have angularSmall : 3 * ‖diskNeutralCLM increment‖ ≤ 1 / 8 := by
    nlinarith [norm_nonneg increment]
  apply family.boundaryCloseToCircle_of_relabel_defect scales time index patch radiusIdentity
    centerIdentity phaseIdentity (diskNeutralCLM increment) (diskNeutralCLM_real increment) angularSmall
  rw [shape]
  have actual := estimate increment (inside.trans (min_le_left _ _)) area
  nlinarith

end FiniteMovingPatchFamily

end EulerNonuniqueness.Paper
