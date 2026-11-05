import EulerNonuniqueness.Section3.HolderBanachModel
import EulerNonuniqueness.Section4.ReferenceStatement

noncomputable section

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

theorem HasC1HalfBound.mono {range : Type*} [NormedAddCommGroup range] [NormedSpace ℝ range]
    {curve : ℝ → range} {bound larger : ℝ} (control : HasC1HalfBound curve bound) (ordered : bound ≤ larger) :
    HasC1HalfBound curve larger := by
  obtain ⟨smooth, valueBound, derivativeBound, holderBound, valueNonnegative, derivativeNonnegative,
    holderNonnegative, total, values, derivatives, holder⟩ := control
  exact ⟨smooth, valueBound, derivativeBound, holderBound, valueNonnegative, derivativeNonnegative,
    holderNonnegative, total.trans ordered, values, derivatives, holder⟩

theorem hasC1HalfBound_zero {range : Type*} [NormedAddCommGroup range] [NormedSpace ℝ range] :
    HasC1HalfBound (fun _ : ℝ => (0 : range)) 0 := by
  refine ⟨contDiff_const, 0, 0, 0, le_rfl, le_rfl, le_rfl, by norm_num, ?_, ?_, ?_⟩
  · intro angle
    simp
  · intro angle
    simp
  · intro angle other
    simp

theorem PeriodicC1HolderHalf.contDiff_one (data : PeriodicC1HolderHalf) : ContDiff ℝ 1 (data.val.1 : ℝ → ℂ) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun angle => (PeriodicC1HolderHalf.hasDerivAt data angle).differentiableAt, ?_⟩
  exact data.val.2.val.1.continuous.congr fun angle => (PeriodicC1HolderHalf.hasDerivAt data angle).deriv.symm

theorem PeriodicC1HolderHalf.hasC1HalfBound (data : PeriodicC1HolderHalf) :
    HasC1HalfBound (data.val.1 : ℝ → ℂ) (3 * ‖data‖) := by
  refine ⟨PeriodicC1HolderHalf.contDiff_one data, ‖data‖, ‖data‖, ‖data‖, norm_nonneg _, norm_nonneg _, norm_nonneg _, by linarith, ?_, ?_, ?_⟩
  · exact PeriodicC1HolderHalf.value_bound data
  · intro angle
    rw [(PeriodicC1HolderHalf.hasDerivAt data angle).deriv]
    exact PeriodicC1HolderHalf.speed_bound data angle
  · intro angle other
    rw [(PeriodicC1HolderHalf.hasDerivAt data angle).deriv, (PeriodicC1HolderHalf.hasDerivAt data other).deriv]
    exact PeriodicC1HolderHalf.derivative_holder_bound data angle other

end EulerNonuniqueness.Paper
