import EulerNonuniqueness.Section6.ExteriorBiotSavartSeries
import EulerNonuniqueness.Section6.FourPointMomentControl

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace EulerNonuniqueness.Section6

def fourPointSignedAverageCLM : FourPointConfiguration →L[ℂ] ℂ :=
  (1 / 4 : ℂ) • ∑ patch : Fin 4, (fourPointSign patch : ℂ) • ContinuousLinearMap.proj patch

theorem fourPointSignedAverageCLM_apply (positions : FourPointConfiguration) :
    fourPointSignedAverageCLM positions = fourPointSignedMoment positions / 4 := by
  simp only [fourPointSignedAverageCLM, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, fourPointSignedMoment]
  ring

theorem fourPointSignedAverageCLM_norm_le (positions : FourPointConfiguration) :
    ‖fourPointSignedAverageCLM positions‖ ≤ ‖positions‖ := by
  rw [fourPointSignedAverageCLM_apply, norm_div, Complex.norm_ofNat]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr (by simpa only [mul_comm] using fourPointSignedMoment_norm_le positions)

theorem fourPointSignedAverageCLM_constant (value : ℂ) :
    fourPointSignedAverageCLM (fun _ => value) = 0 := by
  rw [fourPointSignedAverageCLM_apply]
  norm_num [fourPointSignedMoment, fourPointSign, Fin.sum_univ_succ]

def signedExteriorMoment (positions : FourPointConfiguration) (power : ℕ) : ℂ :=
  fourPointSignedAverageCLM (fun patch => (star (positions patch)) ^ (power + 1))

theorem signedExteriorMoment_zero (positions : FourPointConfiguration) :
    signedExteriorMoment positions 0 = star (fourPointSignedAverageCLM positions) := by
  simp [signedExteriorMoment, fourPointSignedAverageCLM_apply, fourPointSignedMoment,
    Complex.star_def, map_sum, map_mul, mul_comm]

theorem signedExteriorMoment_norm_le (positions : FourPointConfiguration) (power : ℕ)
    {radius : ℝ} (nonnegative : 0 ≤ radius) (bounded : ∀ patch, ‖positions patch‖ ≤ radius) :
    ‖signedExteriorMoment positions power‖ ≤ radius ^ (power + 1) := by
  apply (fourPointSignedAverageCLM_norm_le _).trans
  apply (pi_norm_le_iff_of_nonneg (pow_nonneg nonnegative _)).mpr
  intro patch
  simpa only [norm_pow, norm_star] using pow_le_pow_left₀ (norm_nonneg _) (bounded patch) (power + 1)

theorem exterior_biotSavart_signed_series_hasSum {vorticity : Vorticity}
    (integrable : Integrable vorticity) (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume)
    (center : ℂ) (positions : FourPointConfiguration) {radius distance : ℝ}
    (radiusPositive : 0 < radius) (distancePositive : 0 < distance)
    (separated : ∀ source ∈ Function.support vorticity, distance ≤ ‖center - source‖)
    (small : ∀ patch, radius * ‖positions patch‖ / distance < 1) :
    HasSum (fun power : ℕ => exteriorVorticityCoefficient vorticity center radius power *
        signedExteriorMoment positions power)
      ((radius : ℂ)⁻¹ * fourPointSignedAverageCLM
        (fun patch => biotSavart vorticity (center + (radius : ℂ) * positions patch))) := by
  have pointwise (patch : Fin 4) := exterior_biotSavart_series_hasSum integrable membership center
    (positions patch) radiusPositive distancePositive separated (small patch)
  have series : HasSum (fun power : ℕ => fun patch : Fin 4 =>
      exteriorVorticityCoefficient vorticity center radius power * (star (positions patch)) ^ (power + 1))
      (fun patch => (radius : ℂ)⁻¹ *
        (biotSavart vorticity (center + (radius : ℂ) * positions patch) - biotSavart vorticity center)) :=
    Pi.hasSum.mpr pointwise
  have averaged := fourPointSignedAverageCLM.hasSum series
  have terms (power : ℕ) : fourPointSignedAverageCLM
      (fun patch => exteriorVorticityCoefficient vorticity center radius power * (star (positions patch)) ^ (power + 1)) =
      exteriorVorticityCoefficient vorticity center radius power * signedExteriorMoment positions power := by
    exact map_smul fourPointSignedAverageCLM _ _
  have value : fourPointSignedAverageCLM
      (fun patch => (radius : ℂ)⁻¹ * (biotSavart vorticity (center + (radius : ℂ) * positions patch) -
        biotSavart vorticity center)) =
      (radius : ℂ)⁻¹ * fourPointSignedAverageCLM
        (fun patch => biotSavart vorticity (center + (radius : ℂ) * positions patch)) := by
    rw [show (fun patch => (radius : ℂ)⁻¹ * (biotSavart vorticity (center + (radius : ℂ) * positions patch) -
        biotSavart vorticity center)) = (radius : ℂ)⁻¹ •
        ((fun patch => biotSavart vorticity (center + (radius : ℂ) * positions patch)) -
          (fun _ => biotSavart vorticity center)) from rfl,
      map_smul, map_sub, fourPointSignedAverageCLM_constant, sub_zero]
    rfl
  simpa only [terms, value] using averaged

end EulerNonuniqueness.Section6
