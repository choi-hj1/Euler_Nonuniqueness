import EulerNonuniqueness.Section6.ExteriorCoefficientBound

noncomputable section

namespace EulerNonuniqueness.Section6

def exteriorKernelCoefficient (radius : ℝ) (power : ℕ) (displacement : ℂ) : ℂ :=
  ((-1 : ℂ) ^ (power + 1) * Complex.I * (radius : ℂ) ^ power / ((2 * Real.pi : ℝ) : ℂ)) *
    (star displacement)⁻¹ ^ (power + 2)

private theorem exteriorKernelSeries_rational (base step coefficient scale : ℂ)
    (baseNonzero : base ≠ 0) (scaleNonzero : scale ≠ 0) (sumNonzero : base + scale * step ≠ 0) :
    scale⁻¹ * (coefficient * (base + scale * step)⁻¹ - coefficient * base⁻¹) =
      -coefficient * step * base⁻¹ ^ 2 * (1 - -scale * step * base⁻¹)⁻¹ := by
  have denominator : 1 - -scale * step * base⁻¹ = (base + scale * step) * base⁻¹ := by
    field_simp
    <;> ring
  rw [denominator, mul_inv_rev, inv_inv]
  field_simp
  <;> ring

theorem exteriorKernelSeries_hasSum {radius : ℝ} (positive : 0 < radius)
    (displacement normalized : ℂ) (nearby : radius * ‖normalized‖ < ‖displacement‖) :
    HasSum (fun power : ℕ => exteriorKernelCoefficient radius power displacement *
      (star normalized) ^ (power + 1))
      ((radius : ℂ)⁻¹ * (biotSavartKernel (displacement + (radius : ℂ) * normalized) -
        biotSavartKernel displacement)) := by
  have displacementPositive : 0 < ‖displacement‖ := lt_of_le_of_lt (by positivity) nearby
  have displacementNonzero : displacement ≠ 0 := norm_pos_iff.mp displacementPositive
  have conjugateNonzero : star displacement ≠ 0 := by simpa using displacementNonzero
  have radiusNonzero : (radius : ℂ) ≠ 0 := by exact_mod_cast positive.ne'
  have ratioSmall : ‖-(radius : ℂ) * star normalized * (star displacement)⁻¹‖ < 1 := by
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive,
      norm_star, norm_inv, norm_star, ← div_eq_mul_inv]
    exact (div_lt_one displacementPositive).mpr nearby
  have sumNonzero : displacement + (radius : ℂ) * normalized ≠ 0 := by
    intro zero
    have equality : displacement = -(radius : ℂ) * normalized := by linear_combination zero
    have normEquality := congrArg norm equality
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive] at normEquality
    linarith
  have conjugateSumNonzero : star displacement + (radius : ℂ) * star normalized ≠ 0 := by
    intro zero
    apply sumNonzero
    have conjugate := congrArg (starRingEnd ℂ) zero
    simpa only [Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_conj, map_zero] using conjugate
  have geometric := (hasSum_geometric_of_norm_lt_one ratioSmall).mul_left
    (-(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star normalized * (star displacement)⁻¹ ^ 2)
  convert geometric using 1
  · funext power
    rw [show -(radius : ℂ) = (-1 : ℂ) * (radius : ℂ) by ring]
    simp only [exteriorKernelCoefficient, mul_pow, pow_add, pow_succ]
    ring
  · rw [biotSavartKernel_eq_conj_inv, biotSavartKernel_eq_conj_inv]
    simp only [← Complex.star_def]
    have conjugateSum : star (displacement + (radius : ℂ) * normalized) =
        star displacement + (radius : ℂ) * star normalized := by
      simp only [Complex.star_def, map_add, map_mul, Complex.conj_ofReal]
    rw [conjugateSum]
    exact exteriorKernelSeries_rational (star displacement) (star normalized)
      (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) (radius : ℂ)
      conjugateNonzero radiusNonzero conjugateSumNonzero

end EulerNonuniqueness.Section6
