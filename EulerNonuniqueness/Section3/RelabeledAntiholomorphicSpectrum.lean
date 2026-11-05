import EulerNonuniqueness.Section3.RelabeledForcingValueEquation
import EulerNonuniqueness.Section3.RelabeledDiskForcingPrimitive

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] relabeledForcingValueC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

theorem diskEulerRotatingField_relabel_forcing_mode (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (nearby : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (degree : ℕ) (coefficient : ℂ) :
    fderiv ℝ diskEulerRotatingField (diskRelabelCurve angular 1)
      (coefficient • relabeledDiskForcingMode angular degree) =
      (-Complex.I / 2 * coefficient) • relabeledDiskForcingMode angular degree := by
  have circleSmall : ‖standardCircleBanach - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
    rw [sub_self, norm_zero]
    positivity
  have conjugacy := diskEulerRotatingField_derivative_fixedRelabel angular small standardCircleBanach circleSmall
    (by simpa only [fixedRelabelEquivalence_circle angular small realValues] using nearby)
  have equation := congrArg (fun operator : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf =>
    operator (coefficient • c1Conjugate (diskCircleMode (degree + 1)))) conjugacy
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    fixedRelabelEquivalence_complex_smul, fixedRelabelEquivalence_forcingMode angular small realValues,
    fixedRelabelEquivalence_circle angular small realValues,
    diskEulerRotatingField_hasFDerivAt_circle.fderiv, diskRotatingDerivative_forcing_mode] at equation
  exact equation

theorem diskEulerRotatingField_relabel_forcing_mode_range (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (nearby : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (degree : ℕ) (coefficient : ℂ) :
    fderiv ℝ diskEulerRotatingField (diskRelabelCurve angular 1)
      ((2 * Complex.I * coefficient) • relabeledDiskForcingMode angular degree) =
      coefficient • relabeledDiskForcingMode angular degree := by
  rw [diskEulerRotatingField_relabel_forcing_mode angular small realValues nearby degree]
  congr 1
  ring_nf
  simp

end EulerNonuniqueness.Paper
