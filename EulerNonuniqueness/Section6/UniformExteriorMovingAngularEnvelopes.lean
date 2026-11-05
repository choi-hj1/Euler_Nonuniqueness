import EulerNonuniqueness.Section6.UniformExteriorCoefficientEnvelopes

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000

theorem temporalCoefficientEnvelope_scaled_radius_le {radius distance weight mass : ℝ}
    (radiusNonnegative : 0 ≤ radius) (distanceNonnegative : 0 ≤ distance)
    (power : ℕ) :
    (24 : ℝ) ^ power * temporalCoefficientEnvelope radius distance weight mass power ≤
      temporalCoefficientEnvelope (24 * radius) distance weight mass power := by
  have nonnegative : 0 ≤ (((power + 2 : ℕ) : ℝ) * ((24 : ℝ) ^ power * radius ^ power) / (2 * Real.pi)) *
      ((2 * (24 - 1) * radius / Real.pi) * distance⁻¹ ^ (power + 1)) * weight ^ 2 := by positivity
  apply sub_nonneg.mp
  convert nonnegative using 1 <;> unfold temporalCoefficientEnvelope <;> rw [mul_pow] <;> ring

theorem summable_weight48_temporalCoefficientEnvelope {radius distance weight mass : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance)
    (weightNonnegative : 0 ≤ weight) (massNonnegative : 0 ≤ mass)
    (small : 96 * radius / distance < 1) :
    Summable (fun power : ℕ => (48 : ℝ) ^ (power + 1) *
      temporalCoefficientEnvelope radius distance weight mass power) := by
  have scaledSmall : 4 * (24 * radius) / distance < 1 := by convert small using 1 <;> ring
  have scaled := (summable_weighted_temporalCoefficientEnvelope (by positivity : 0 ≤ 24 * radius)
    positive scaledSmall weight mass).mul_left 24
  apply Summable.of_nonneg_of_le (fun power => mul_nonneg (by positivity)
    (temporalCoefficientEnvelope_nonnegative radiusNonnegative positive.le weightNonnegative massNonnegative power))
    (fun power => ?_) scaled
  have numerical := mul_le_mul_of_nonneg_left
    (temporalCoefficientEnvelope_scaled_radius_le (weight := weight) (mass := mass) radiusNonnegative positive.le power)
    (show 0 ≤ 24 * (2 : ℝ) ^ (power + 1) by positivity)
  convert numerical using 1 <;> simp only [show (48 : ℝ) = 2 * 24 by norm_num, mul_pow, pow_succ] <;> ring

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem exists_uniform_exteriorCoefficient_moving_angular_envelopes {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (times : Set ℝ)
    {distance weight mass : ℝ} (positive : 0 < distance)
    (small : 192 * (family.patch index).radius ≤ distance)
    (weightNonnegative : 0 ≤ weight) (massNonnegative : 0 ≤ mass)
    (inside : ∀ time ∈ times, time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ time ∈ times, ∀ label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (centered : ∀ time ∈ times, (family.patch index).center =ᶠ[nhds time] (family.patch index).centroid)
    (separated : ∀ time ∈ times, ∀ source ∈ Finset.univ.erase index,
      ∀ position ∈ (family.patch source).domain time, distance ≤ ‖(family.patch index).center time - position‖)
    (weightBound : ∀ time ∈ times, (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight)
    (massBound : ∀ time ∈ times, (∫ position, |family.patchVorticity time index position|) ≤ mass) :
    ∃ valueEnvelope derivativeEnvelope : ℕ → ℝ,
      (∀ power, 0 ≤ valueEnvelope power ∧ 0 ≤ derivativeEnvelope power) ∧
      Summable (fun power => (48 : ℝ) ^ (power + 1) * valueEnvelope power) ∧
      Summable (fun power => (48 : ℝ) ^ (power + 1) * derivativeEnvelope power) ∧
      ∀ time ∈ times, ∀ power,
        ‖family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
          (family.patch index).radius (power + 1) time‖ ≤ valueEnvelope power ∧
        ‖family.exteriorMaterialCoefficientDerivative index power time‖ ≤ derivativeEnvelope power := by
  have radiusNonnegative : 0 ≤ (family.patch index).radius := (family.patch index).radius_positive.le
  have ratio : 48 * (family.patch index).radius / distance < 1 :=
    (div_lt_one positive).mpr (by linarith [(family.patch index).radius_positive])
  have derivativeRatio : 96 * (family.patch index).radius / distance < 1 :=
    (div_lt_one positive).mpr (by linarith [(family.patch index).radius_positive])
  have summableValue : Summable (fun power : ℕ => (48 : ℝ) ^ (power + 1) *
      (((family.patch index).radius / distance) ^ power * (weight / (2 * Real.pi)))) := by
    have geometric := (summable_geometric_of_lt_one (by positivity : 0 ≤ 48 * (family.patch index).radius / distance)
      ratio).mul_right (48 * weight / (2 * Real.pi))
    convert geometric using 1
    funext power
    rw [show 48 * (family.patch index).radius / distance = 48 * ((family.patch index).radius / distance) by ring,
      mul_pow, pow_succ]
    ring
  refine ⟨(fun power => ((family.patch index).radius / distance) ^ power * (weight / (2 * Real.pi))),
    temporalCoefficientEnvelope (family.patch index).radius distance weight mass, ?_, summableValue,
    summable_weight48_temporalCoefficientEnvelope radiusNonnegative positive weightNonnegative massNonnegative derivativeRatio, ?_⟩
  · intro power
    exact ⟨by positivity, temporalCoefficientEnvelope_nonnegative radiusNonnegative positive.le weightNonnegative massNonnegative power⟩
  · intro time member power
    exact ⟨family.norm_exteriorTaylorCoefficient_le_uniform index positive (separated time member) (weightBound time member) power,
      family.norm_exteriorMaterialCoefficientDerivative_le_uniform index (inside time member) (material time member)
        (centered time member) positive (by linarith [(family.patch index).radius_positive])
        (separated time member) (weightBound time member) (massBound time member) power⟩

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
