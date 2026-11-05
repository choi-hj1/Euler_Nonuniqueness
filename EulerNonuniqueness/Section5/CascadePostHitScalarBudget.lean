import EulerNonuniqueness.Section5.CascadeExtentScalarBudget
import EulerNonuniqueness.Section1.UniformScaleBounds

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_cascade_posthit_scalar_budgets (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {factor scaleRoot boundaryConstant tolerance : ℝ}
    (factorPositive : 0 < factor) (rootPositive : 0 < scaleRoot)
    (boundaryNonnegative : 0 ≤ boundaryConstant) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop,
      let changed := {scales with frequency := frequency}
      (2 / Real.pi) * (24 / factor) ^ 2 * changed.strain ≤ tolerance ∧
      ∀ count : ℕ, ∀ index : Fin count,
        let deformation := boundaryConstant / (scaleRoot ^ 2 * changed.omega (index.val + 1) ^ 2)
        deformation ≤ 1 / 16 ∧
        3456 * changed.circulation (index.val + 1) * changed.radius (index.val + 1) ^ 2 * deformation /
          (Real.pi * (factor * changed.length (index.val + 1)) ^ 3) +
          (4096 * changed.radius (index.val + 1) ^ 2 * deformation / Real.pi) *
            (∑ source ∈ Finset.univ.erase index, changed.circulation (source.val + 1) /
              cascadeForeignDistance changed factor index source ^ 3) ≤
          tolerance * changed.length (index.val + 1) := by
  let constant := boundaryConstant / (scales.amplitude * scaleRoot ^ 2) *
    (13824 / factor ^ 3 + (8192 / Real.pi) * (24 / factor) ^ 3)
  have constantNonnegative : 0 ≤ constant := by dsimp only [constant]; positivity
  have strainLimit := ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul
    ((2 / Real.pi) * (24 / factor) ^ 2))
  simp only [mul_zero] at strainLimit
  have fourthLimit : Tendsto (fun frequency : ℝ => constant / frequency ^ 4) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, Function.comp_apply, mul_zero] using
      ((tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : 4 ≠ 0))).const_mul constant)
  have secondLimit : Tendsto (fun frequency : ℝ => boundaryConstant / (scaleRoot ^ 2 * frequency ^ 2))
      atTop (𝓝 0) := by
    have actual := ((tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : 2 ≠ 0))).const_mul
      (boundaryConstant / scaleRoot ^ 2))
    simpa only [Function.comp_apply, mul_zero, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using actual
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    strainLimit.eventually (eventually_lt_nhds tolerancePositive),
    fourthLimit.eventually (eventually_lt_nhds tolerancePositive),
    secondLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency frequencyOne strainSmall fourthSmall secondSmall hessianSmall
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  refine ⟨by simpa only [mul_zero] using strainSmall.le, ?_⟩
  intro count index
  have omegaBound := changed.omega_ge_frequency frequencyPositive (by linarith) (index.val + 1)
  have omegaOne : 1 ≤ changed.omega (index.val + 1) := frequencyOne.trans omegaBound
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have lengthPositive := changed.length_pos (index.val + 1)
  have lengthOne := changed.length_le_one frequencyPositive ratioPositive (index.val + 1)
  have third := changed.sum_cascadeForeignMoment_le frequencyOne ratioBound alphaPositive factorPositive index 3
  change _ ≤ (24 / factor) ^ 3 * changed.hessian at third
  have thirdBound := third.trans (mul_le_mul_of_nonneg_left hessianSmall.le
    (by positivity : 0 ≤ (24 / factor) ^ 3))
  simp only [mul_one] at thirdBound
  have lengthRatio : changed.length (index.val + 1) / changed.omega (index.val + 1) ≤ 1 :=
    (div_le_one omegaPositive).mpr (lengthOne.trans omegaOne)
  constructor
  · exact (div_le_div_of_nonneg_left boundaryNonnegative (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ frequencyPositive.le omegaBound 2)
        (sq_nonneg scaleRoot))).trans secondSmall.le
  · have identity :
        3456 * changed.circulation (index.val + 1) * changed.radius (index.val + 1) ^ 2 *
            (boundaryConstant / (scaleRoot ^ 2 * changed.omega (index.val + 1) ^ 2)) /
            (Real.pi * (factor * changed.length (index.val + 1)) ^ 3) +
          (4096 * changed.radius (index.val + 1) ^ 2 *
            (boundaryConstant / (scaleRoot ^ 2 * changed.omega (index.val + 1) ^ 2)) / Real.pi) *
            (∑ source ∈ Finset.univ.erase index, changed.circulation (source.val + 1) /
              cascadeForeignDistance changed factor index source ^ 3) =
        changed.length (index.val + 1) *
          (boundaryConstant / (changed.amplitude * scaleRoot ^ 2 * changed.omega (index.val + 1) ^ 4)) *
          (13824 / factor ^ 3 + (8192 / Real.pi) *
            (changed.length (index.val + 1) / changed.omega (index.val + 1)) *
            (∑ source ∈ Finset.univ.erase index, changed.circulation (source.val + 1) /
              cascadeForeignDistance changed factor index source ^ 3)) := by
      rw [changed.radius_sq amplitudePositive frequencyPositive ratioPositive]
      unfold Scales.circulation
      field_simp [amplitudePositive.ne', rootPositive.ne', omegaPositive.ne', factorPositive.ne',
        lengthPositive.ne', Real.pi_ne_zero]
      <;> ring
    rw [identity]
    have bracket :
        13824 / factor ^ 3 + (8192 / Real.pi) *
          (changed.length (index.val + 1) / changed.omega (index.val + 1)) *
          (∑ source ∈ Finset.univ.erase index, changed.circulation (source.val + 1) /
            cascadeForeignDistance changed factor index source ^ 3) ≤
        13824 / factor ^ 3 + (8192 / Real.pi) * (24 / factor) ^ 3 := by
      apply add_le_add_left _ _
      have sumNonnegative : 0 ≤ ∑ source ∈ Finset.univ.erase index,
          changed.circulation (source.val + 1) / cascadeForeignDistance changed factor index source ^ 3 := by
        apply Finset.sum_nonneg
        intro source member
        have different := (Finset.mem_erase.mp member).1
        have distancePositive : 0 < cascadeForeignDistance changed factor index source := by
          unfold cascadeForeignDistance
          have locationDifferent := changed.location_distance_pos
            (show index.val + 1 ≠ source.val + 1 from fun equal => different (Fin.ext (by omega)))
          positivity
        exact div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (by positivity)
      calc
        _ ≤ (8192 / Real.pi) * 1 *
            (∑ source ∈ Finset.univ.erase index, changed.circulation (source.val + 1) /
              cascadeForeignDistance changed factor index source ^ 3) := by gcongr
        _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left thirdBound (by positivity : 0 ≤ 8192 / Real.pi)
    have firstBound := mul_le_mul_of_nonneg_left bracket
      (show 0 ≤ changed.length (index.val + 1) *
        (boundaryConstant / (changed.amplitude * scaleRoot ^ 2 * changed.omega (index.val + 1) ^ 4)) by positivity)
    have constantBound : constant / changed.omega (index.val + 1) ^ 4 ≤ tolerance :=
      (div_le_div_of_nonneg_left constantNonnegative (pow_pos frequencyPositive 4)
        (pow_le_pow_left₀ frequencyPositive.le omegaBound 4)).trans fourthSmall.le
    apply firstBound.trans
    have scaled := mul_le_mul_of_nonneg_right constantBound lengthPositive.le
    convert scaled using 1 <;> dsimp only [constant, changed] <;> ring

end EulerNonuniqueness.Paper
