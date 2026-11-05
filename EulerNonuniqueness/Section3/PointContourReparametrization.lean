import EulerNonuniqueness.Section3.PeriodicLabelSubstitution
import EulerNonuniqueness.Section3.NearCircleBoundaryBiotSavart

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

theorem pointContourVelocity_reparametrization (labels : PeriodicC1LabelMap)
    (positive : ∀ label, 0 < labels.slope label) (curve tangent : ℝ → ℂ) (point : ℂ)
    (curvePeriodic : Function.Periodic curve (2 * Real.pi))
    (tangentPeriodic : Function.Periodic tangent (2 * Real.pi))
    (logIntegrable : IntervalIntegrable (fun source => Real.log ‖curve source - point‖ • tangent source)
      volume (-Real.pi) Real.pi) :
    IntervalIntegrable (fun source => Real.log ‖curve (labels.map source) - point‖ •
      (labels.slope source • tangent (labels.map source))) volume (-Real.pi) Real.pi ∧
      pointContourVelocity (fun source => curve (labels.map source))
        (fun source => labels.slope source • tangent (labels.map source)) point (-Real.pi) Real.pi =
      pointContourVelocity curve tangent point (-Real.pi) Real.pi := by
  let integrand := fun source => Real.log ‖curve source - point‖ • tangent source
  have periodic : Function.Periodic integrand (2 * Real.pi) := by
    intro source
    dsimp only [integrand]
    rw [curvePeriodic, tangentPeriodic]
  have basePeriod : IntervalIntegrable integrand volume (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    convert logIntegrable using 1 <;> congr 1 <;> ring
  have shifted := periodic.intervalIntegrable (by positivity : 0 < 2 * Real.pi) basePeriod
    (labels.map (-Real.pi)) (labels.map Real.pi)
  have substitution := labels.intervalIntegral_substitution positive (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)
    integrand shifted
  have identity : (fun source => Real.log ‖curve (labels.map source) - point‖ •
      (labels.slope source • tangent (labels.map source))) =
      fun source => labels.slope source • integrand (labels.map source) := by
    funext source
    exact smul_comm _ _ _
  have upperIdentity : labels.map Real.pi = labels.map (-Real.pi) + 2 * Real.pi := by
    convert labels.add_period (-Real.pi) using 1 <;> congr 1 <;> ring
  have window : (∫ source in (labels.map (-Real.pi))..(labels.map Real.pi), integrand source) =
      ∫ source in (-Real.pi)..Real.pi, integrand source := by
    rw [upperIdentity]
    convert periodic.intervalIntegral_add_eq (labels.map (-Real.pi)) (-Real.pi) using 1 <;> congr 1 <;> ring
  refine ⟨by rw [identity]; exact substitution.1, ?_⟩
  unfold pointContourVelocity
  rw [identity, substitution.2, window]

theorem nearCircle_point_contour_log_integrable (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi)) (point : ℂ) (lower upper : ℝ) :
    IntervalIntegrable (fun source => Real.log ‖data.val.1 source - point‖ • data.val.2.val.1 source)
      volume lower upper := by
  by_cases boundary : point ∈ range (data.val.1 : ℝ → ℂ)
  · obtain ⟨target, rfl⟩ := boundary
    let chord := 2 / (3 * Real.pi) - ‖data - standardCircleBanach‖
    have chordPositive : 0 < chord := sub_pos.mpr small
    have chordBound : ∀ source ∈ Icc (target - Real.pi) (target + Real.pi),
        chord * |source - target| ≤ ‖data.val.1 source - data.val.1 target‖ := by
      intro source member
      have nearby : |source - target| ≤ 3 * Real.pi / 2 := by
        rw [abs_le]
        constructor <;> linarith [member.1, member.2, Real.pi_pos]
      have estimate := PeriodicC1HolderHalf.chord_bound_extended data nearby
      rwa [norm_sub_rev] at estimate
    have centered := contour_log_integrable_interval (by linarith [Real.pi_pos] : target - Real.pi ≤ target + Real.pi)
      (show target ∈ Icc (target - Real.pi) (target + Real.pi) by constructor <;> linarith [Real.pi_pos])
      (show 0 < ‖data‖ + 1 by positivity) chordPositive data.val.1.continuous data.val.2.val.1.continuous
      (fun source _ => PeriodicC1HolderHalf.hasDerivAt data source)
      (fun source _ => (PeriodicC1HolderHalf.speed_bound data source).trans (by linarith)) chordBound
    have periodic : Function.Periodic
        (fun source => Real.log ‖data.val.1 source - data.val.1 target‖ • data.val.2.val.1 source) (2 * Real.pi) := by
      intro source
      dsimp only
      rw [PeriodicC1HolderHalf.periodic data, PeriodicHolderHalf.periodic data.val.2]
    have basePeriod : IntervalIntegrable
        (fun source => Real.log ‖data.val.1 source - data.val.1 target‖ • data.val.2.val.1 source)
        volume (target - Real.pi) (target - Real.pi + 2 * Real.pi) := by
      simpa only [show target - Real.pi + 2 * Real.pi = target + Real.pi by ring] using centered
    exact periodic.intervalIntegrable (by positivity : 0 < 2 * Real.pi) basePeriod lower upper
  · have nonzero (source : ℝ) : ‖data.val.1 source - point‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (sub_ne_zero.mpr (fun equality => boundary ⟨source, equality⟩))
    have logarithm := ((data.val.1.continuous.sub continuous_const).norm).log nonzero
    exact (logarithm.smul data.val.2.val.1.continuous).intervalIntegrable lower upper

theorem PeriodicC1LabelMap.pointContourVelocity_compose (labels : PeriodicC1LabelMap)
    (positive : ∀ label, 0 < labels.slope label) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi)) (point : ℂ) :
    IntervalIntegrable (fun source => Real.log ‖(labels.compose data).val.1 source - point‖ •
      (labels.compose data).val.2.val.1 source) volume (-Real.pi) Real.pi ∧
      pointContourVelocity (labels.compose data).val.1 (labels.compose data).val.2.val.1 point (-Real.pi) Real.pi =
        pointContourVelocity data.val.1 data.val.2.val.1 point (-Real.pi) Real.pi := by
  have result := pointContourVelocity_reparametrization labels positive data.val.1 data.val.2.val.1 point
    (PeriodicC1HolderHalf.periodic data) (PeriodicHolderHalf.periodic data.val.2)
    (nearCircle_point_contour_log_integrable data small point (-Real.pi) Real.pi)
  simpa only [PeriodicC1LabelMap.compose_value, PeriodicC1LabelMap.compose_tangent, Complex.real_smul] using result

end EulerNonuniqueness.Paper
