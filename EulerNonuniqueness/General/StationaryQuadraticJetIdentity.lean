import EulerNonuniqueness.General.LinearExponentialSlopes
import EulerNonuniqueness.General.BilinearOperatorCalculus

namespace EulerNonuniqueness.General

noncomputable section

open Filter
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem stationary_quadratic_second_jet_identity
    (linear : Space →L[ℝ] Space) (quadratic : BilinearEnd Space)
    (increment : ℝ → Space) (tangent curvature : Space) (remainderBound : ℝ)
    (tangentZero : linear tangent = 0)
    (firstSlope : Tendsto (fun time : ℝ => time⁻¹ • increment time) (𝓝[≠] (0 : ℝ)) (𝓝 tangent))
    (secondSlope : Tendsto (fun time : ℝ => (time ^ 2)⁻¹ • (increment time - time • tangent))
      (𝓝[≠] (0 : ℝ)) (𝓝 curvature))
    (stationaryRemainder : ∀ᶠ time in 𝓝[≠] (0 : ℝ),
      ‖linear (increment time) + quadratic (increment time) (increment time)‖ ≤
        remainderBound * ‖increment time‖ ^ 3) :
    linear curvature + quadratic tangent tangent = 0 := by
  let combined := fun time : ℝ =>
    linear ((time ^ 2)⁻¹ • (increment time - time • tangent)) +
      quadratic (time⁻¹ • increment time) (time⁻¹ • increment time)
  have quadraticContinuous : Continuous (fun pair : Space × Space => quadratic pair.1 pair.2) :=
    (quadratic.continuous.comp continuous_fst).clm_apply continuous_snd
  have combinedLimit : Tendsto combined (𝓝[≠] (0 : ℝ)) (𝓝 (linear curvature + quadratic tangent tangent)) :=
    (linear.continuous.continuousAt.tendsto.comp secondSlope).add
      (quadraticContinuous.continuousAt.tendsto.comp (firstSlope.prodMk_nhds firstSlope))
  have combinedIdentity (time : ℝ) : combined time =
      (time ^ 2)⁻¹ • (linear (increment time) + quadratic (increment time) (increment time)) := by
    dsimp only [combined]
    simp only [map_smul, map_sub, tangentZero, smul_zero, sub_zero,
      ContinuousLinearMap.smul_apply, smul_smul, smul_add, inv_pow, pow_two, mul_inv_rev]
  have bound : ∀ᶠ time in 𝓝[≠] (0 : ℝ), ‖combined time‖ ≤
      remainderBound * |time| * ‖time⁻¹ • increment time‖ ^ 3 := by
    filter_upwards [stationaryRemainder, self_mem_nhdsWithin] with time remainder outside
    have nonzero : time ≠ 0 := by simpa using outside
    have rescaled : increment time = time • (time⁻¹ • increment time) := by
      rw [smul_smul, mul_inv_cancel₀ nonzero, one_smul]
    have normRescaled : ‖increment time‖ = |time| * ‖time⁻¹ • increment time‖ := by
      conv_lhs => rw [rescaled]
      rw [norm_smul, Real.norm_eq_abs]
    have scalarIdentity : |(time ^ 2)⁻¹| * |time| ^ 3 = |time| := by
      rw [abs_inv, abs_pow, pow_succ |time| 2, ← mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero 2 (abs_ne_zero.mpr nonzero)), one_mul]
    rw [combinedIdentity, norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ |(time ^ 2)⁻¹| * (remainderBound * ‖increment time‖ ^ 3) :=
        mul_le_mul_of_nonneg_left remainder (abs_nonneg _)
      _ = remainderBound * (|(time ^ 2)⁻¹| * |time| ^ 3) * ‖time⁻¹ • increment time‖ ^ 3 := by
        rw [normRescaled, mul_pow]
        ring
      _ = _ := by rw [scalarIdentity]
  have timeLimit : Tendsto (fun time : ℝ => |time|) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [abs_zero] using (tendsto_id.mono_left nhdsWithin_le_nhds :
      Tendsto (fun time : ℝ => time) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ))).abs
  have upperLimit := ((tendsto_const_nhds (x := remainderBound)).mul timeLimit).mul (firstSlope.norm.pow 3)
  simp only [mul_zero, zero_mul] at upperLimit
  have normZero : Tendsto (fun time => ‖combined time‖) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds upperLimit
      (Eventually.of_forall fun _ => norm_nonneg _) bound
  exact norm_eq_zero.mp (tendsto_nhds_unique combinedLimit.norm normZero)

end

end EulerNonuniqueness.General
