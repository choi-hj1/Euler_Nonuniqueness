import EulerNonuniqueness.Section3.RelabeledAntiholomorphicSpectrum
import EulerNonuniqueness.Section3.MovingStrainPrimitiveFormula
import EulerNonuniqueness.Section3.ExteriorSeriesLeadingMode

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

theorem movingStrainRealPrimitiveValue_relabel_generator_range (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (nearby : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (coefficient : ℂ) :
    fderiv ℝ diskEulerRotatingField (diskRelabelCurve angular 1)
      ((-4 * coefficient) • c1Conjugate (diskRelabelCurve angular 1)) =
      movingStrainRealPrimitiveValue (diskRelabelCurve angular 1) coefficient := by
  have actual := diskEulerRotatingField_relabel_forcing_mode_range angular small realValues nearby 0 (2 * Complex.I * coefficient)
  have mode : relabeledDiskForcingMode angular 0 = c1Conjugate (diskRelabelCurve angular 1) := by
    unfold relabeledDiskForcingMode
    rw [c1NaturalPower_one]
  have scalar : 2 * Complex.I * (2 * Complex.I * coefficient) = -4 * coefficient := by
    ring_nf
    simp
  rw [mode, scalar] at actual
  rw [movingStrainRealPrimitiveValue_formula]
  exact actual

end EulerNonuniqueness.Paper
