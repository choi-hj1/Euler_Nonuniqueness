import EulerNonuniqueness.Section3.HolderPaperBoundaryBound
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

theorem PeriodicC1HolderHalf.real_hasC1HalfBound (data : PeriodicC1HolderHalf) :
    HasC1HalfBound (fun angle => (data.val.1 angle).re) (3 * ‖data‖) := by
  have derivative (angle : ℝ) : HasDerivAt (fun label => (data.val.1 label).re) (data.val.2.val.1 angle).re angle :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt angle (PeriodicC1HolderHalf.hasDerivAt data angle)
  refine ⟨Complex.reCLM.contDiff.comp (PeriodicC1HolderHalf.contDiff_one data),
    ‖data‖, ‖data‖, ‖data‖, norm_nonneg _, norm_nonneg _, norm_nonneg _, by linarith, ?_, ?_, ?_⟩
  · intro angle
    exact (Complex.abs_re_le_norm _).trans (PeriodicC1HolderHalf.value_bound data angle)
  · intro angle
    rw [(derivative angle).deriv]
    exact (Complex.abs_re_le_norm _).trans (PeriodicC1HolderHalf.speed_bound data angle)
  · intro angle other
    rw [(derivative angle).deriv, (derivative other).deriv]
    change |(data.val.2.val.1 angle).re - (data.val.2.val.1 other).re| ≤ _
    rw [← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans (PeriodicC1HolderHalf.derivative_holder_bound data angle other)

end EulerNonuniqueness.Paper
