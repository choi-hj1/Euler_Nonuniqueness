import EulerNonuniqueness.Section6.UniformExteriorCoefficientBounds

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem exists_uniform_exteriorCoefficient_envelopes {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (times : Set ℝ)
    {distance weight mass : ℝ} (positive : 0 < distance)
    (small : 4 * (family.patch index).radius / distance < 1)
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
      Summable (fun power => (2 : ℝ) ^ (power + 1) * valueEnvelope power) ∧
      Summable (fun power => (2 : ℝ) ^ (power + 1) * derivativeEnvelope power) ∧
      ∀ time ∈ times, ∀ power,
        ‖family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
          (family.patch index).radius (power + 1) time‖ ≤ valueEnvelope power ∧
        ‖family.exteriorMaterialCoefficientDerivative index power time‖ ≤ derivativeEnvelope power := by
  have ratioSmall : 2 * (family.patch index).radius / distance < 1 := by
    rw [mul_div_assoc] at small ⊢
    have nonnegative := div_nonneg (family.patch index).radius_positive.le positive.le
    linarith
  have geometrySmall : 4 * (family.patch index).radius ≤ distance := ((div_lt_one positive).mp small).le
  have summableValue : Summable (fun power : ℕ => (2 : ℝ) ^ (power + 1) *
      (((family.patch index).radius / distance) ^ power * (weight / (2 * Real.pi)))) := by
    have geometric := (summable_geometric_of_lt_one
      (div_nonneg (mul_nonneg (by norm_num) (family.patch index).radius_positive.le) positive.le)
      ratioSmall).mul_right (weight / Real.pi)
    convert geometric using 1
    funext power
    rw [show 2 * (family.patch index).radius / distance = 2 * ((family.patch index).radius / distance) by ring,
      mul_pow, pow_succ]
    ring
  refine ⟨(fun power => ((family.patch index).radius / distance) ^ power * (weight / (2 * Real.pi))),
    temporalCoefficientEnvelope (family.patch index).radius distance weight mass, ?_, summableValue,
    summable_weighted_temporalCoefficientEnvelope (family.patch index).radius_positive.le positive small weight mass, ?_⟩
  · intro power
    constructor
    · exact mul_nonneg (pow_nonneg (div_nonneg (family.patch index).radius_positive.le positive.le) _)
        (div_nonneg weightNonnegative (by positivity))
    · exact temporalCoefficientEnvelope_nonnegative (family.patch index).radius_positive.le positive.le
        weightNonnegative massNonnegative power
  · intro time member power
    exact ⟨family.norm_exteriorTaylorCoefficient_le_uniform index positive (separated time member) (weightBound time member) power,
      family.norm_exteriorMaterialCoefficientDerivative_le_uniform index (inside time member) (material time member)
        (centered time member) positive geometrySmall (separated time member) (weightBound time member) (massBound time member) power⟩

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
