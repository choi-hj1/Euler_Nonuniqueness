import EulerNonuniqueness.Section3.FixedRelabelArea
import EulerNonuniqueness.Section3.CenteredAntiholomorphicAnalytic

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper

local instance centeredFixedRelabelC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem contourPolynomialMoment_fixedRelabel (degree : ℕ) (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2) (data : PeriodicC1HolderHalf) :
    contourPolynomialMoment degree (fixedRelabelEquivalence angular small data) =
      contourPolynomialMoment degree data := by
  let labels := periodicForwardLabelMap angular small
  let integrand := fun label => data.val.1 label ^ degree * star (data.val.1 label) * data.val.2.val.1 label
  have continuous : Continuous integrand := (data.val.1.continuous.pow degree).mul
    data.val.1.continuous.star |>.mul data.val.2.val.1.continuous
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
      (fun label => (fixedRelabelEquivalence angular small data).val.1 label ^ degree *
        star ((fixedRelabelEquivalence angular small data).val.1 label) *
        (fixedRelabelEquivalence angular small data).val.2.val.1 label) =
      fun label => labels.slope label • integrand (labels.map label) := by
    funext label
    rw [fixedRelabelEquivalence_value, fixedRelabelEquivalence_tangent]
    change data.val.1 (periodicLabelShift angular label) ^ degree *
      star (data.val.1 (periodicLabelShift angular label)) *
        ((periodicLabelSlope angular label : ℂ) * data.val.2.val.1 (periodicLabelShift angular label)) = _
    change data.val.1 (periodicLabelShift angular label) ^ degree *
      star (data.val.1 (periodicLabelShift angular label)) *
        ((periodicLabelSlope angular label : ℂ) * data.val.2.val.1 (periodicLabelShift angular label)) =
      periodicLabelSlope angular label • (data.val.1 (periodicLabelShift angular label) ^ degree *
        star (data.val.1 (periodicLabelShift angular label)) * data.val.2.val.1 (periodicLabelShift angular label))
    simp only [Complex.real_smul]
    ring
  rw [contourPolynomialMoment_eq_integral, contourPolynomialMoment_eq_integral,
    pullback, substitution.2, window]

theorem centeredAntiholomorphicForcing_fixedRelabel (degree : ℕ) (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2) (data : PeriodicC1HolderHalf) :
    centeredAntiholomorphicForcing degree (fixedRelabelEquivalence angular small data) =
      fixedRelabelEquivalence angular small (centeredAntiholomorphicForcing degree data) := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [fixedRelabelEquivalence_value, centeredAntiholomorphicForcing_value,
    centeredAntiholomorphicForcing_value, fixedRelabelEquivalence_value,
    contourPolynomialMoment_fixedRelabel]

end EulerNonuniqueness.Paper
