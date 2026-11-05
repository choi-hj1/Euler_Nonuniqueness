import EulerNonuniqueness.Section3.FixedRelabelEquivalence
import EulerNonuniqueness.Section3.PeriodicLabelSubstitution
import EulerNonuniqueness.Section3.ContourAnalyticArea

namespace EulerNonuniqueness.Paper

noncomputable section

open MeasureTheory

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance fixedAreaC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

theorem contourAreaFunctional_fixedRelabel (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2) (data : PeriodicC1HolderHalf) :
    contourAreaFunctional (fixedRelabelEquivalence angular small data) = contourAreaFunctional data := by
  let labels := periodicForwardLabelMap angular small
  let integrand := fun label => star (data.val.1 label) * data.val.2.val.1 label
  have continuous : Continuous integrand := data.val.1.continuous.star.mul data.val.2.val.1.continuous
  have periodic : Function.Periodic integrand (2 * Real.pi) := by
    intro label
    dsimp only [integrand]
    rw [PeriodicC1HolderHalf.periodic data, PeriodicHolderHalf.periodic data.val.2]
  have positive (label : ℝ) : 0 < labels.slope label := by
    have lower := periodicLabelSlope_lower angular label
    change 0 < periodicLabelSlope angular label
    linarith
  have substitution := labels.intervalIntegral_substitution positive
    (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi) integrand (continuous.intervalIntegrable _ _)
  have upperIdentity : labels.map Real.pi = labels.map (-Real.pi) + 2 * Real.pi := by
    convert labels.add_period (-Real.pi) using 1 <;> congr 1 <;> ring
  have window : (∫ label in labels.map (-Real.pi)..labels.map Real.pi, integrand label) =
      ∫ label in (-Real.pi)..Real.pi, integrand label := by
    rw [upperIdentity]
    convert periodic.intervalIntegral_add_eq (labels.map (-Real.pi)) (-Real.pi) using 1 <;> congr 1 <;> ring
  have pullback :
      (fun label => star ((fixedRelabelEquivalence angular small data).val.1 label) *
        (fixedRelabelEquivalence angular small data).val.2.val.1 label) =
      fun label => labels.slope label • integrand (labels.map label) := by
    funext label
    rw [fixedRelabelEquivalence_value, fixedRelabelEquivalence_tangent]
    change star (data.val.1 (periodicLabelShift angular label)) *
      ((periodicLabelSlope angular label : ℂ) * data.val.2.val.1 (periodicLabelShift angular label)) =
      periodicLabelSlope angular label •
        (star (data.val.1 (periodicLabelShift angular label)) * data.val.2.val.1 (periodicLabelShift angular label))
    simp only [Complex.real_smul]
    ring
  unfold contourAreaFunctional
  rw [contourPolynomialMoment_eq_integral, contourPolynomialMoment_eq_integral]
  simp only [pow_zero, one_mul]
  rw [pullback, substitution.2, window]

end

end EulerNonuniqueness.Paper
