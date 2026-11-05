import EulerNonuniqueness.Section3.ContourPhaseSource

open MeasureTheory Set

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

def contourVelocityDerivativeHolder (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) : PeriodicHolderHalf :=
  holderComplexMul (-((1 / (4 * Real.pi) : ℝ) : ℂ))
    (holderProduct (holderConjugate data.val.2)
      (holderConjugate (contourCauchyOperator data small (contourTangentQuotient data small) +
        holderComplexMul ((Real.pi : ℂ) * Complex.I) (contourTangentQuotient data small))))

theorem contourVelocityDerivativeHolder_value (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (target : ℝ) :
    (contourVelocityDerivativeHolder data small).val.1 target =
      -((1 / (4 * Real.pi) : ℝ) : ℂ) * star (data.val.2.val.1 target) *
        star (∫ source in (target - Real.pi)..(target + Real.pi),
          contourCauchyDensityRemainder data.val.1 data.val.2.val.1
            (contourTangentQuotient data small).val.1 target source) := by
  unfold contourVelocityDerivativeHolder
  rw [holderComplexMul_value, holderProduct_value, holderConjugate_value, holderConjugate_value]
  change -((1 / (4 * Real.pi) : ℝ) : ℂ) * (star (data.val.2.val.1 target) *
    star ((contourCauchyOperator data small (contourTangentQuotient data small)).val.1 target +
      (holderComplexMul ((Real.pi : ℂ) * Complex.I) (contourTangentQuotient data small)).val.1 target)) = _
  rw [contourCauchyOperator_value, holderComplexMul_value]
  unfold contourCauchyTransform
  rw [sub_add_cancel]
  ring

set_option maxHeartbeats 1000000 in
theorem banachContourVelocity_hasDerivAt_holder (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (target : ℝ) :
    HasDerivAt (banachContourVelocity data) ((contourVelocityDerivativeHolder data small).val.1 target) target := by
  have actual := banachContourVelocity_hasDerivAt data small target
  convert actual using 1
  rw [contourVelocityDerivativeHolder_value, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : target - Real.pi ≤ target + Real.pi),
    banachContourPhaseDerivative_integral_cauchy data small target]
  simp only [Complex.real_smul]
  ring

def contourVelocityBanach (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) : PeriodicC1HolderHalf :=
  PeriodicC1HolderHalf.ofFunctions (banachContourVelocity data) (contourVelocityDerivativeHolder data small).val.1
    (banachContourVelocity_differentiable data small).continuous
    (contourVelocityDerivativeHolder data small).val.1.continuous
    ((‖data‖ + 1) / 2) ‖contourVelocityDerivativeHolder data small‖ ‖contourVelocityDerivativeHolder data small‖
    (banachContourVelocity_norm_bound data small)
    (PeriodicHolderHalf.value_bound (contourVelocityDerivativeHolder data small))
    (PeriodicHolderHalf.holder_bound (contourVelocityDerivativeHolder data small))
    (banachContourVelocity_hasDerivAt_holder data small) (banachContourVelocity_periodic data)
    (PeriodicHolderHalf.periodic (contourVelocityDerivativeHolder data small))

theorem contourVelocityBanach_value (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (target : ℝ) :
    (contourVelocityBanach data small).val.1 target =
      contourVelocity data.val.1 data.val.2.val.1 target (-Real.pi) Real.pi := rfl

theorem contourVelocityBanach_tangent (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (target : ℝ) :
    (contourVelocityBanach data small).val.2.val.1 target =
      (contourVelocityDerivativeHolder data small).val.1 target := rfl

theorem contourVelocityBanach_norm_bound (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    ‖contourVelocityBanach data small‖ ≤ max ((‖data‖ + 1) / 2) ‖contourVelocityDerivativeHolder data small‖ := by
  unfold contourVelocityBanach
  have bound := PeriodicC1HolderHalf.ofFunctions_norm_bound
    (banachContourVelocity data) (contourVelocityDerivativeHolder data small).val.1
    (banachContourVelocity_differentiable data small).continuous
    (contourVelocityDerivativeHolder data small).val.1.continuous
    (by positivity : 0 ≤ (‖data‖ + 1) / 2) (norm_nonneg _) (norm_nonneg _)
    (banachContourVelocity_norm_bound data small)
    (PeriodicHolderHalf.value_bound (contourVelocityDerivativeHolder data small))
    (PeriodicHolderHalf.holder_bound (contourVelocityDerivativeHolder data small))
    (banachContourVelocity_hasDerivAt_holder data small) (banachContourVelocity_periodic data)
    (PeriodicHolderHalf.periodic (contourVelocityDerivativeHolder data small))
  simpa only [max_self] using bound

end

end EulerNonuniqueness.Paper
