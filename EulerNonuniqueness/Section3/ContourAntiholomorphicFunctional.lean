import EulerNonuniqueness.Section3.ContourInversePowerGreen
import EulerNonuniqueness.Section3.FixedRelabelArea

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

def contourAntiholomorphicFunctional (kernel : ℂ → ℂ) (data : PeriodicC1HolderHalf) : ℂ :=
  (Complex.I / 2) * ∫ label in (-Real.pi)..Real.pi,
    data.val.1 label * kernel (data.val.1 label) * star (data.val.2.val.1 label)

theorem contourAntiholomorphicFunctional_fixedRelabel_of_continuous_comp (kernel : ℂ → ℂ)
    (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2) (data : PeriodicC1HolderHalf)
    (kernelContinuous : Continuous (fun label => kernel (data.val.1 label))) :
    contourAntiholomorphicFunctional kernel (fixedRelabelEquivalence angular small data) =
      contourAntiholomorphicFunctional kernel data := by
  let labels := periodicForwardLabelMap angular small
  let integrand := fun label => data.val.1 label * kernel (data.val.1 label) * star (data.val.2.val.1 label)
  have integrandContinuous : Continuous integrand :=
    (data.val.1.continuous.mul kernelContinuous).mul
      data.val.2.val.1.continuous.star
  have periodic : Function.Periodic integrand (2 * Real.pi) := by
    intro label
    dsimp only [integrand]
    rw [PeriodicC1HolderHalf.periodic data, PeriodicHolderHalf.periodic data.val.2]
  have positive (label : ℝ) : 0 < labels.slope label := by
    have lower := periodicLabelSlope_lower angular label
    change 0 < periodicLabelSlope angular label
    linarith
  have substitution := labels.intervalIntegral_substitution positive
    (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi) integrand
    (integrandContinuous.intervalIntegrable _ _)
  have upperIdentity : labels.map Real.pi = labels.map (-Real.pi) + 2 * Real.pi := by
    convert labels.add_period (-Real.pi) using 1 <;> congr 1 <;> ring
  have window : (∫ label in labels.map (-Real.pi)..labels.map Real.pi, integrand label) =
      ∫ label in (-Real.pi)..Real.pi, integrand label := by
    rw [upperIdentity]
    convert periodic.intervalIntegral_add_eq (labels.map (-Real.pi)) (-Real.pi) using 1 <;> congr 1 <;> ring
  have pullback :
      (fun label => (fixedRelabelEquivalence angular small data).val.1 label *
        kernel ((fixedRelabelEquivalence angular small data).val.1 label) *
        star ((fixedRelabelEquivalence angular small data).val.2.val.1 label)) =
      fun label => labels.slope label • integrand (labels.map label) := by
    funext label
    rw [fixedRelabelEquivalence_value, fixedRelabelEquivalence_tangent]
    change data.val.1 (periodicLabelShift angular label) *
      kernel (data.val.1 (periodicLabelShift angular label)) *
        star ((periodicLabelSlope angular label : ℂ) * data.val.2.val.1 (periodicLabelShift angular label)) =
      periodicLabelSlope angular label • (data.val.1 (periodicLabelShift angular label) *
        kernel (data.val.1 (periodicLabelShift angular label)) *
          star (data.val.2.val.1 (periodicLabelShift angular label)))
    simp only [Complex.real_smul, star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  unfold contourAntiholomorphicFunctional
  rw [pullback, substitution.2, window]

theorem contourAntiholomorphicFunctional_fixedRelabel (kernel : ℂ → ℂ)
    (kernelContinuous : Continuous kernel) (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2) (data : PeriodicC1HolderHalf) :
    contourAntiholomorphicFunctional kernel (fixedRelabelEquivalence angular small data) =
      contourAntiholomorphicFunctional kernel data :=
  contourAntiholomorphicFunctional_fixedRelabel_of_continuous_comp kernel angular small data
    (kernelContinuous.comp data.val.1.continuous)

theorem integral_nearCircleInterior_conjugate_inverse_power_eq_functional
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (displacement scale : ℂ) {distance : ℝ} (positive : 0 < distance) (power : ℕ)
    (interiorSeparated : ∀ position ∈ nearCircleInterior data small,
      distance ≤ ‖displacement - scale * position‖)
    (boundarySeparated : ∀ label,
      distance ≤ ‖displacement - scale * data.val.1 label‖) :
    (∫ position in nearCircleInterior data small,
      (star (displacement - scale * position))⁻¹ ^ (power + 1)) =
      contourAntiholomorphicFunctional
        (fun position => (star (displacement - scale * position))⁻¹ ^ (power + 1)) data :=
  integral_nearCircleInterior_conjugate_inverse_power data small displacement scale positive power
    interiorSeparated boundarySeparated

end EulerNonuniqueness.Paper
