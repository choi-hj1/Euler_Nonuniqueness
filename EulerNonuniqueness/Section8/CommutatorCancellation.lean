import EulerNonuniqueness.Section8.WeakGradient

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem fderiv_reflected_test {test : Plane → ℝ} (smooth : ContDiff ℝ ∞ test)
    (center position : Plane) :
    fderiv ℝ (fun point => test (center - point)) position = -fderiv ℝ test (center - position) := by
  change fderiv ℝ (test ∘ fun point : Plane => center - id point) position = _
  rw [fderiv_comp position (smooth.differentiable (by simp) _)
    ((differentiableAt_const center).sub differentiableAt_id), fderiv_const_sub, fderiv_id]
  simp

theorem integral_biotSavart_kernel_difference {vorticity : Vorticity}
    (integrable : Integrable vorticity) {radius : ℝ}
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {test : Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) (center : Plane) :
    Integrable (fun offset => fderiv ℝ test offset
      (biotSavart vorticity center - biotSavart vorticity (center - offset))) ∧
      (∫ offset, fderiv ℝ test offset
        (biotSavart vorticity center - biotSavart vorticity (center - offset))) = 0 := by
  have reflectedSmooth : ContDiff ℝ ∞ (fun point => test (center - point)) :=
    smooth.comp (contDiff_const.sub contDiff_id)
  have reflectedCompact : HasCompactSupport (fun point => test (center - point)) :=
    compact.comp_homeomorph (Homeomorph.subLeft center)
  have reflected := divergenceFree_biotSavart_of_integrable_support
    integrable supportBound (reflectedSmooth.of_le (by simp)) reflectedCompact
  have reflectedIntegrable : Integrable
      (fun point => fderiv ℝ test (center - point) (biotSavart vorticity point)) := by
    have negative := reflected.1.neg
    change Integrable (fun point => -(fderiv ℝ (fun point => test (center - point)) point
      (biotSavart vorticity point))) at negative
    simpa only [fderiv_reflected_test smooth, ContinuousLinearMap.neg_apply, neg_neg] using negative
  have reflectedZero :
      (∫ point, fderiv ℝ test (center - point) (biotSavart vorticity point)) = 0 := by
    have equality := reflected.2
    simp only [fderiv_reflected_test smooth, ContinuousLinearMap.neg_apply, integral_neg, neg_eq_zero] at equality
    exact equality
  have shiftedIntegrable : Integrable
      (fun offset => fderiv ℝ test offset (biotSavart vorticity (center - offset))) := by
    simpa only [sub_sub_cancel] using reflectedIntegrable.comp_sub_left center
  have shiftedZero : (∫ offset, fderiv ℝ test offset (biotSavart vorticity (center - offset))) = 0 := by
    have equality := integral_sub_left_eq_self
      (fun point => fderiv ℝ test (center - point) (biotSavart vorticity point)) volume center
    simpa only [sub_sub_cancel, reflectedZero] using equality
  have fixedIntegrable : Integrable (fun offset => fderiv ℝ test offset (biotSavart vorticity center)) :=
    ((smooth.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (compact.fderiv_apply ℝ (biotSavart vorticity center))
  refine ⟨by simpa only [map_sub] using fixedIntegrable.sub shiftedIntegrable, ?_⟩
  simp_rw [map_sub]
  rw [integral_sub fixedIntegrable shiftedIntegrable,
    integral_directionalDerivative_eq_zero smooth compact, shiftedZero, sub_self]

def transportCommutator (kernel : Plane → ℝ) (velocity : Velocity) (vorticity : Vorticity) (position : Plane) : ℝ :=
  ∫ offset, vorticity (position - offset) * fderiv ℝ kernel offset (velocity position - velocity (position - offset))

theorem transportCommutator_eq_centered {vorticity : Vorticity} {radius : ℝ}
    (integrable : Integrable vorticity) (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume)
    (radiusNonnegative : 0 ≤ radius)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {kernel : Plane → ℝ} (smooth : ContDiff ℝ ∞ kernel) (compact : HasCompactSupport kernel) (position : Plane) :
    transportCommutator kernel (biotSavart vorticity) vorticity position =
      ∫ offset, (vorticity (position - offset) - vorticity position) * fderiv ℝ kernel offset
        (biotSavart vorticity position - biotSavart vorticity (position - offset)) := by
  let coefficient := fun offset => fderiv ℝ kernel offset
    (biotSavart vorticity position - biotSavart vorticity (position - offset))
  have velocityContinuous := continuous_biotSavart_of_memLp_support holderConjugate_four_fourThirds
    membership (by norm_num) radiusNonnegative supportBound
  have coefficientContinuous : Continuous coefficient :=
    (smooth.continuous_fderiv (by simp)).clm_apply
      (continuous_const.sub (velocityContinuous.comp (continuous_const.sub continuous_id)))
  have coefficientCompact : HasCompactSupport coefficient := by
    apply (compact.fderiv (𝕜 := ℝ)).mono
    intro offset nonzero
    apply Function.mem_support.mpr
    intro zero
    exact nonzero (by simp [coefficient, zero])
  have coefficientTop := coefficientContinuous.memLp_top_of_hasCompactSupport coefficientCompact volume
  have productIntegrable : Integrable (fun offset => vorticity (position - offset) * coefficient offset) :=
    (integrable.comp_sub_left position).mul_of_top_left coefficientTop
  have cancellation := integral_biotSavart_kernel_difference integrable supportBound smooth compact position
  change (∫ offset, vorticity (position - offset) * coefficient offset) =
    ∫ offset, (vorticity (position - offset) - vorticity position) * coefficient offset
  simp_rw [sub_mul]
  rw [integral_sub productIntegrable (cancellation.1.const_mul _), integral_const_mul, cancellation.2, mul_zero, sub_zero]

end EulerNonuniqueness
