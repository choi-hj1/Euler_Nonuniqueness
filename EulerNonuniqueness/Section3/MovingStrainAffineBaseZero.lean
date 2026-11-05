import EulerNonuniqueness.Section3.MovingStrainAffineResidual
import EulerNonuniqueness.Section3.FixedRelabelVelocityEquivariance

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

theorem movingStrainAffineResidual_relabel_base_zero
    (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (nearby : ‖fixedRelabelEquivalence angular small standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi)))) (coefficient : ℂ) :
    movingStrainAffineResidual (fixedRelabelEquivalence angular small standardCircleBanach) coefficient
      (fixedRelabelEquivalence angular small standardCircleBanach) = 0 := by
  let base := fixedRelabelEquivalence angular small standardCircleBanach
  have selfZero : diskEulerRotatingField base = 0 := by
    rw [diskEulerRotatingField_fixedRelabel angular small standardCircleBanach
      (by rw [sub_self, norm_zero]; positivity) (lt_min_iff.mp nearby).2,
      diskEulerRotatingField_circle, map_zero]
  have actual := movingStrainRealPrimitiveValue_actual_equation angular small coefficient nearby
  have partner : movingStrainRealPrimitiveValue base (-Complex.I * coefficient) =
      contourCentroidGaugeProjection base (coefficient • c1Conjugate base) +
        fderiv ℝ diskEulerRotatingField base (movingStrainRealPrimitiveValue base coefficient) :=
    sub_eq_iff_eq_add.mp actual
  change movingStrainAffineResidual base coefficient base = 0
  unfold movingStrainAffineResidual
  simp only [sub_self, map_zero, add_zero, sub_zero, selfZero]
  rw [partner]
  abel

end EulerNonuniqueness.Paper
