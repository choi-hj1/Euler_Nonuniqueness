import EulerNonuniqueness.Section8.TransportAnalyticInitialTrace

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff Convolution

namespace EulerNonuniqueness

theorem norm_scalar_convolution_le {source kernel : Plane → ℝ} {bound : ℝ}
    (integrable : Integrable source) (kernelContinuous : Continuous kernel)
    (bounded : ∀ position, ‖kernel position‖ ≤ bound) (position : Plane) :
    ‖(kernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] source) position‖ ≤
      bound * ∫ sourcePosition, ‖source sourcePosition‖ := by
  have shifted := integrable.comp_sub_left position
  have productIntegrable := shifted.bdd_mul kernelContinuous.aestronglyMeasurable ⟨bound, bounded⟩
  change ‖∫ offset, kernel offset * source (position - offset)‖ ≤ _
  calc
    _ ≤ ∫ offset, ‖kernel offset * source (position - offset)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ offset, bound * ‖source (position - offset)‖ :=
      integral_mono productIntegrable.norm (shifted.norm.const_mul bound) fun offset => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (bounded offset) (norm_nonneg _)
    _ = _ := by
      rw [integral_const_mul]
      exact congrArg (fun value : ℝ => bound * value)
        (integral_sub_left_eq_self (fun point : Plane => ‖source point‖) volume position)

theorem norm_fderiv_scalar_convolution_le {source kernel : Plane → ℝ} {bound : ℝ}
    (integrable : Integrable source) (smooth : ContDiff ℝ ∞ kernel)
    (compact : HasCompactSupport kernel) (bounded : ∀ position, ‖fderiv ℝ kernel position‖ ≤ bound)
    (position direction : Plane) :
    ‖fderiv ℝ (kernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] source) position direction‖ ≤
      bound * ‖direction‖ * ∫ sourcePosition, ‖source sourcePosition‖ := by
  rw [fderiv_scalarConvolution_apply integrable smooth compact]
  have estimate := norm_scalar_convolution_le integrable
    ((smooth.continuous_fderiv (by simp)).clm_apply (continuous_const : Continuous fun _ : Plane => direction))
    (fun offset => ((fderiv ℝ kernel offset).le_opNorm direction).trans
      (mul_le_mul_of_nonneg_right (bounded offset) (norm_nonneg _))) position
  simpa only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_comm] using estimate

theorem TransportAnalyticHypotheses.uniform_mollification_bound
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (index : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ time ∈ Icc 0 horizon, ∀ position,
      ‖mollification (omega time) index position‖ ≤ bound ∧
      ∀ direction, ‖fderiv ℝ (mollification (omega time) index) position direction‖ ≤ bound * ‖direction‖ := by
  let kernel := (mollifierBump (Space := Plane) index).normed (volume : Measure Plane)
  have smooth : ContDiff ℝ ∞ kernel := (mollifierBump index).contDiff_normed
  have compact : HasCompactSupport kernel := (mollifierBump index).hasCompactSupport_normed
  obtain ⟨valueBound, valueBounded⟩ := compact.exists_bound_of_continuous smooth.continuous
  obtain ⟨derivativeBound, derivativeBounded⟩ := (compact.fderiv ℝ).exists_bound_of_continuous
    (smooth.continuous_fderiv (by simp))
  let coefficient := max (max valueBound derivativeBound) 0
  have coefficientNonnegative : 0 ≤ coefficient := le_max_right _ _
  have valueBounded' (position : Plane) : ‖kernel position‖ ≤ coefficient :=
    (valueBounded position).trans ((le_max_left _ _).trans (le_max_left _ _))
  have derivativeBounded' (position : Plane) : ‖fderiv ℝ kernel position‖ ≤ coefficient :=
    (derivativeBounded position).trans ((le_max_right _ _).trans (le_max_left _ _))
  obtain ⟨massBound, finite, bounded⟩ := hypotheses.uniformBounds 1 le_rfl
  refine ⟨coefficient * massBound.toReal, by positivity, ?_⟩
  intro time inside position
  have integrable := hypotheses.integrable inside
  have massEstimate : (∫ source, ‖omega time source‖) ≤ massBound.toReal := by
    have estimate := ENNReal.toReal_mono finite.ne (bounded time inside)
    simpa only [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm,
      ← integral_norm_eq_lintegral_enorm integrable.aestronglyMeasurable] using estimate
  constructor
  · exact (norm_scalar_convolution_le integrable smooth.continuous valueBounded' position).trans
      (mul_le_mul_of_nonneg_left massEstimate coefficientNonnegative)
  · intro direction
    apply (norm_fderiv_scalar_convolution_le integrable smooth compact derivativeBounded' position direction).trans
    calc
      _ ≤ coefficient * ‖direction‖ * massBound.toReal :=
        mul_le_mul_of_nonneg_left massEstimate (by positivity)
      _ = _ := by ring

end EulerNonuniqueness
