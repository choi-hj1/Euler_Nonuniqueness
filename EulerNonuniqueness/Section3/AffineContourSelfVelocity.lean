import EulerNonuniqueness.Section3.AffineContourModel
import EulerNonuniqueness.Section3.ContourScaling

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

theorem pointContourVelocity_on_curve (curve tangent : ℝ → ℂ) (target lower upper : ℝ) :
    pointContourVelocity curve tangent (curve target) lower upper = contourVelocity curve tangent target lower upper := by
  unfold pointContourVelocity contourVelocity
  congr 1
  apply intervalIntegral.integral_congr
  intro source source_mem
  dsimp only
  rw [norm_sub_rev]

theorem periodicContourVelocity_centered (data : PeriodicC1HolderHalf) (target : ℝ) :
    contourVelocity data.val.1 data.val.2.val.1 target (-Real.pi) Real.pi =
      contourVelocity data.val.1 data.val.2.val.1 target (target - Real.pi) (target + Real.pi) := by
  have identity := contourVelocity_periodic_source_window (PeriodicC1HolderHalf.periodic data)
    (PeriodicHolderHalf.periodic data.val.2) target (-Real.pi) (target - Real.pi)
  convert identity using 1 <;> congr 1 <;> ring

set_option maxHeartbeats 1000000 in
theorem c1AffineContour_self_velocity (center : ℂ) {radius : ℝ} (radius_pos : 0 < radius)
    (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (target : ℝ) :
    pointContourVelocity (c1AffineContour center radius data).val.1
      (c1AffineContour center radius data).val.2.val.1
      ((c1AffineContour center radius data).val.1 target) (-Real.pi) Real.pi =
      radius • contourVelocity data.val.1 data.val.2.val.1 target (-Real.pi) Real.pi := by
  have ordered : target - Real.pi ≤ target + Real.pi := by linarith [Real.pi_pos]
  let chord := 2 / (3 * Real.pi) - ‖data - standardCircleBanach‖
  have chord_pos : 0 < chord := sub_pos.mpr (small.trans_le (min_le_right _ _))
  have chord_bound : ∀ source ∈ Icc (target - Real.pi) (target + Real.pi),
      chord * |source - target| ≤ ‖data.val.1 source - data.val.1 target‖ := by
    intro source source_mem
    have nearby : |source - target| ≤ 3 * Real.pi / 2 := by
      rw [abs_le]
      constructor <;> linarith [source_mem.1, source_mem.2, Real.pi_pos]
    have estimate := PeriodicC1HolderHalf.chord_bound_extended data nearby
    rwa [norm_sub_rev] at estimate
  have tangent_integrable : IntervalIntegrable data.val.2.val.1 volume (target - Real.pi) (target + Real.pi) :=
    data.val.2.val.1.continuous.intervalIntegrable _ _
  have log_integrable := contour_log_integrable_interval ordered
    (show target ∈ Icc (target - Real.pi) (target + Real.pi) by constructor <;> linarith [Real.pi_pos])
    (show 0 < ‖data‖ + 1 by positivity) chord_pos data.val.1.continuous data.val.2.val.1.continuous
    (fun source _ => PeriodicC1HolderHalf.hasDerivAt data source)
    (fun source _ => (PeriodicC1HolderHalf.speed_bound data source).trans (by linarith)) chord_bound
  have distinct_ae : ∀ᵐ source : ℝ ∂volume, source ≠ target := by
    rw [ae_iff]
    simp
  have separated : ∀ᵐ source ∂volume, source ∈ uIoc (target - Real.pi) (target + Real.pi) →
      data.val.1 source - data.val.1 target ≠ 0 := by
    filter_upwards [distinct_ae] with source distinct source_mem
    rw [uIoc_of_le ordered] at source_mem
    apply norm_pos_iff.mp
    exact (mul_pos chord_pos (abs_pos.mpr (sub_ne_zero.mpr distinct))).trans_le
      (chord_bound source ⟨source_mem.1.le, source_mem.2⟩)
  have tangent_zero : (∫ source in (target - Real.pi)..(target + Real.pi), data.val.2.val.1 source) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun source _ => PeriodicC1HolderHalf.hasDerivAt data source) tangent_integrable]
    have periodic := PeriodicC1HolderHalf.periodic data (target - Real.pi)
    rw [show target - Real.pi + 2 * Real.pi = target + Real.pi by ring] at periodic
    rw [periodic, sub_self]
  rw [pointContourVelocity_on_curve, periodicContourVelocity_centered,
    periodicContourVelocity_centered data]
  rw [← pointContourVelocity_on_curve, ← pointContourVelocity_on_curve]
  convert pointContourVelocity_scaling data.val.1 data.val.2.val.1 (data.val.1 target) center
    radius_pos tangent_integrable log_integrable separated tangent_zero using 1
  congr 1
  funext source
  exact c1AffineContour_tangent center radius data source

end

end EulerNonuniqueness.Paper
