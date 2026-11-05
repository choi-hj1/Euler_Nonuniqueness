import EulerNonuniqueness.Section3.ContourLabelShift
import EulerNonuniqueness.Section3.ContourRotation
import EulerNonuniqueness.Section3.ContourVelocityFrechet
import EulerNonuniqueness.Section3.PointContourReparametrization

namespace EulerNonuniqueness.Paper

noncomputable section

open MeasureTheory

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance normalizedShiftVelocityC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph
local instance normalizedShiftVelocityC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem pointContourVelocity_label_translation (data : PeriodicC1HolderHalf) (offset : ℝ) (point : ℂ) :
    pointContourVelocity (fun source => data.val.1 (source + offset))
      (fun source => data.val.2.val.1 (source + offset)) point (-Real.pi) Real.pi =
      pointContourVelocity data.val.1 data.val.2.val.1 point (-Real.pi) Real.pi := by
  let integrand := fun source => Real.log ‖data.val.1 source - point‖ • data.val.2.val.1 source
  have periodic : Function.Periodic integrand (2 * Real.pi) := by
    intro source
    dsimp only [integrand]
    rw [PeriodicC1HolderHalf.periodic data source, PeriodicHolderHalf.periodic data.val.2 source]
  have window := periodic.intervalIntegral_add_eq (-Real.pi) (-Real.pi + offset)
  have firstEndpoint : -Real.pi + 2 * Real.pi = Real.pi := by ring
  have secondEndpoint : -Real.pi + offset + 2 * Real.pi = Real.pi + offset := by ring
  rw [firstEndpoint, secondEndpoint] at window
  unfold pointContourVelocity
  change (-(1 / (2 * Real.pi)) : ℝ) • (∫ source in (-Real.pi)..Real.pi, integrand (source + offset)) =
    (-(1 / (2 * Real.pi)) : ℝ) • (∫ source in (-Real.pi)..Real.pi, integrand source)
  rw [intervalIntegral.integral_comp_add_right, ← window]

theorem pointContourVelocity_normalized_shift (data : PeriodicC1HolderHalf) (offset : ℝ) (point : ℂ) :
    pointContourVelocity (normalizedContourShift offset data).val.1
      (normalizedContourShift offset data).val.2.val.1 ((standardCircle offset)⁻¹ * point) (-Real.pi) Real.pi =
      (standardCircle offset)⁻¹ * pointContourVelocity data.val.1 data.val.2.val.1 point (-Real.pi) Real.pi := by
  have rotation := pointContourVelocity_unit_rotation
    (fun source => data.val.1 (source + offset)) (fun source => data.val.2.val.1 (source + offset))
    point (standardCircle offset)⁻¹ 0 (by simp [norm_inv, standardCircle_norm]) (-Real.pi) Real.pi
  simp only [add_zero] at rotation
  change pointContourVelocity (fun source => (standardCircle offset)⁻¹ * data.val.1 (source + offset))
    (fun source => (standardCircle offset)⁻¹ * data.val.2.val.1 (source + offset))
    ((standardCircle offset)⁻¹ * point) (-Real.pi) Real.pi = _
  rw [rotation, pointContourVelocity_label_translation]

theorem extendedContourVelocity_normalized_shift (data : PeriodicC1HolderHalf) (offset : ℝ)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    extendedContourVelocity (normalizedContourShift offset data) =
      normalizedContourShift offset (extendedContourVelocity data) := by
  have shiftedSmall : ‖normalizedContourShift offset data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
    rw [normalizedContourShift_distance_circle]
    exact small
  rw [extendedContourVelocity_eq _ shiftedSmall, extendedContourVelocity_eq _ small]
  apply PeriodicC1HolderHalf.ext_value
  intro target
  rw [contourVelocityBanach_value, normalizedContourShift_value, contourVelocityBanach_value]
  rw [← pointContourVelocity_on_curve _ _ target (-Real.pi) Real.pi,
    ← pointContourVelocity_on_curve _ _ (target + offset) (-Real.pi) Real.pi,
    normalizedContourShift_value]
  exact pointContourVelocity_normalized_shift data offset (data.val.1 (target + offset))

def normalizedContourShiftCLM (offset : ℝ) : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  LinearMap.mkContinuous
    { toFun := normalizedContourShift offset
      map_add' := by
        intro first second
        apply PeriodicC1HolderHalf.ext_value
        intro label
        change (standardCircle offset)⁻¹ * (first.val.1 (label + offset) + second.val.1 (label + offset)) =
          (standardCircle offset)⁻¹ * first.val.1 (label + offset) +
            (standardCircle offset)⁻¹ * second.val.1 (label + offset)
        ring
      map_smul' := by
        intro scalar data
        apply PeriodicC1HolderHalf.ext_value
        intro label
        change (standardCircle offset)⁻¹ * (scalar • data.val.1 (label + offset)) =
          scalar • ((standardCircle offset)⁻¹ * data.val.1 (label + offset))
        exact mul_smul_comm _ _ _ }
    1 (fun data => by simpa only [one_mul] using (normalizedContourShift_norm offset data).le)

theorem normalizedContourShiftCLM_apply (offset : ℝ) (data : PeriodicC1HolderHalf) :
    normalizedContourShiftCLM offset data = normalizedContourShift offset data := rfl

end

end EulerNonuniqueness.Paper
