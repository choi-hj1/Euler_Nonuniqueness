import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic

noncomputable section

open MeasureTheory Filter Metric
open scoped Topology NNReal

namespace EulerNonuniqueness.General

theorem hasFDerivAt_integral_translate_of_lipschitz
    {density : ℂ → ℝ} (densityIntegrable : Integrable density)
    {test : ℂ → ℂ} (smooth : ContDiff ℝ 1 test) {constant : ℝ≥0}
    (lipschitz : LipschitzWith constant test) (center : ℂ)
    (baseIntegrable : Integrable (fun position => density position • test (center - position))) :
    HasFDerivAt (fun current => ∫ position, density position • test (current - position))
      (∫ position, density position • fderiv ℝ test (center - position)) center := by
  have derivativeMeasurable : AEStronglyMeasurable
      (fun position => density position • fderiv ℝ test (center - position)) :=
    densityIntegrable.aestronglyMeasurable.smul
      (((smooth.continuous_fderiv le_rfl).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  have kernelMeasurable (current : ℂ) : AEStronglyMeasurable
      (fun position => density position • test (current - position)) :=
    densityIntegrable.aestronglyMeasurable.smul
      ((smooth.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  have pointwiseLipschitz (position : ℂ) :
      LipschitzWith (Real.nnabs (‖density position‖ * constant))
        (fun current : ℂ => density position • test (current - position)) := by
    apply LipschitzWith.of_dist_le_mul
    intro current other
    simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.coe_nnabs,
      abs_of_nonneg (mul_nonneg (norm_nonneg _) constant.coe_nonneg)]
    have bound := lipschitz.norm_sub_le (current - position) (other - position)
    have difference : (current - position) - (other - position) = current - other := by abel
    rw [difference] at bound
    exact (mul_le_mul_of_nonneg_left bound (norm_nonneg _)).trans_eq (by ring)
  have derivative (position : ℂ) : HasFDerivAt
      (fun current : ℂ => density position • test (current - position))
      (density position • fderiv ℝ test (center - position)) center := by
    have translated := ((smooth.differentiable le_rfl (center - position)).hasFDerivAt).comp center
      ((hasFDerivAt_id center).sub (hasFDerivAt_const position center))
    simpa only [sub_zero, ContinuousLinearMap.comp_id] using translated.const_smul (density position)
  exact (hasFDerivAt_integral_of_dominated_loc_of_lip (ε := 1) (by norm_num)
    (Eventually.of_forall kernelMeasurable) baseIntegrable derivativeMeasurable
    (Eventually.of_forall fun position => (pointwiseLipschitz position).lipschitzOnWith)
    (densityIntegrable.norm.mul_const (constant : ℝ)) (Eventually.of_forall derivative)).2

end EulerNonuniqueness.General
