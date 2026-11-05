import EulerNonuniqueness.Section1.ForeignInteractionWeight
import EulerNonuniqueness.Section1.UniformScaleBounds

noncomputable section

namespace EulerNonuniqueness.Paper

open scoped BigOperators

theorem Scales.reference_internal_deformation_cost_eq (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : ℕ) (deformation : ℝ) :
    (30 / scales.length index) *
        (3456 * scales.circulation index * scales.radius index ^ 2 * deformation /
          (Real.pi * (scales.length index / 100) ^ 3)) =
      (414720000000 / scales.amplitude) * (deformation / scales.omega index ^ 2) := by
  rw [scales.radius_sq amplitudePositive frequencyPositive ratioPositive, Scales.circulation]
  have lengthNonzero := (scales.length_pos index).ne'
  have omegaNonzero := (scales.omega_pos frequencyPositive ratioPositive index).ne'
  field_simp
  <;> ring

theorem Scales.reference_internal_deformation_cost_le (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : ℕ) {deformation bound : ℝ}
    (deformationBound : deformation ≤ bound / scales.omega index ^ 2) :
    (30 / scales.length index) *
        (3456 * scales.circulation index * scales.radius index ^ 2 * deformation /
          (Real.pi * (scales.length index / 100) ^ 3)) ≤
      (414720000000 * bound / scales.amplitude) / scales.omega index ^ 4 := by
  rw [scales.reference_internal_deformation_cost_eq amplitudePositive frequencyPositive ratioPositive]
  calc
    _ ≤ (414720000000 / scales.amplitude) *
        ((bound / scales.omega index ^ 2) / scales.omega index ^ 2) := by gcongr
    _ = _ := by ring

theorem Scales.reference_external_deformation_cost_le {count : ℕ} (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (index : Fin count) {deformation : ℝ} (deformationNonnegative : 0 ≤ deformation) :
    (30 / scales.length (index.val + 1)) *
        ((4096 * scales.radius (index.val + 1) ^ 2 * deformation / Real.pi) *
          ∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1) /
            (|scales.location (index.val + 1) - scales.location (source.val + 1)| / 8) ^ 3) ≤
      (3397386240 / (Real.pi * scales.amplitude)) *
        (scales.length (index.val + 1) * deformation * scales.hessian / scales.omega (index.val + 1) ^ 3) := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have lengthPositive := scales.length_pos (index.val + 1)
  have weightBound := scales.sum_foreignInteractionWeight_le frequencyBound ratioBound alphaPositive index 3
  change (∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1) /
      (|scales.location (index.val + 1) - scales.location (source.val + 1)| / 8) ^ 3) ≤
    24 ^ 3 * scales.hessian at weightBound
  apply (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left weightBound (by positivity :
      0 ≤ 4096 * scales.radius (index.val + 1) ^ 2 * deformation / Real.pi))
    (by positivity : 0 ≤ 30 / scales.length (index.val + 1))).trans_eq
  rw [scales.radius_sq amplitudePositive frequencyPositive ratioPositive]
  have lengthNonzero := (scales.length_pos (index.val + 1)).ne'
  have omegaNonzero := (scales.omega_pos frequencyPositive ratioPositive (index.val + 1)).ne'
  field_simp
  <;> ring

theorem Scales.reference_external_deformation_cost_fourth_le {count : ℕ} (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (index : Fin count) {deformation bound : ℝ} (deformationNonnegative : 0 ≤ deformation)
    (boundNonnegative : 0 ≤ bound) (deformationBound : deformation ≤ bound / scales.omega (index.val + 1) ^ 2)
    (lengthBound : scales.length (index.val + 1) ≤ 1) (hessianBound : scales.hessian ≤ 1) :
    (30 / scales.length (index.val + 1)) *
        ((4096 * scales.radius (index.val + 1) ^ 2 * deformation / Real.pi) *
          ∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1) /
            (|scales.location (index.val + 1) - scales.location (source.val + 1)| / 8) ^ 3) ≤
      (3397386240 * bound / (Real.pi * scales.amplitude)) / scales.omega (index.val + 1) ^ 4 := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have lengthPositive := scales.length_pos (index.val + 1)
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have omegaBound : 1 ≤ scales.omega (index.val + 1) := frequencyBound.trans
    (scales.omega_ge_frequency frequencyPositive (by linarith) (index.val + 1))
  have hessianNonnegative : 0 ≤ scales.hessian := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (scales.location_pos _).le _)
  have productBound : scales.length (index.val + 1) * deformation * scales.hessian ≤
      bound / scales.omega (index.val + 1) ^ 2 := by
    calc
      _ ≤ 1 * (bound / scales.omega (index.val + 1) ^ 2) * 1 := by gcongr
      _ = _ := by ring
  have powerBound : scales.omega (index.val + 1) ^ 2 ≤ scales.omega (index.val + 1) ^ 3 := by
    exact pow_le_pow_right₀ omegaBound (by norm_num)
  apply (scales.reference_external_deformation_cost_le amplitudePositive frequencyBound ratioBound alphaPositive
    index deformationNonnegative).trans
  calc
    _ ≤ (3397386240 / (Real.pi * scales.amplitude)) *
        ((bound / scales.omega (index.val + 1) ^ 2) / scales.omega (index.val + 1) ^ 2) := by gcongr
    _ = _ := by ring

end EulerNonuniqueness.Paper
