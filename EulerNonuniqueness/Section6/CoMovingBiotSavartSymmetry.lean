import EulerNonuniqueness.Section6.WeightedCoMovingKernel

noncomputable section

namespace EulerNonuniqueness.Section6

theorem star_biotSavartKernel (position : ℂ) :
    star (biotSavartKernel position) = -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * position⁻¹ := by
  rw [Complex.star_def, biotSavartKernel_eq_conj_inv]
  change (starRingEnd ℂ) ((Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * ((starRingEnd ℂ) position)⁻¹) = _
  rw [map_mul, map_inv₀, Complex.conj_conj, map_div₀, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem coMoving_biotSavartKernel_symmetrization (power : ℕ) {first second : ℂ}
    (firstNonzero : first ≠ 0) (secondNonzero : second ≠ 0) (distinct : first ≠ second) :
    star (biotSavartKernel second - biotSavartKernel (second - first)) * (star first)⁻¹ ^ power +
      star (biotSavartKernel first - biotSavartKernel (first - second)) * (star second)⁻¹ ^ power =
        -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * coMovingInversePowerKernel power first second := by
  have differenceNonzero := sub_ne_zero.mpr distinct
  have reverseNonzero := sub_ne_zero.mpr distinct.symm
  have rationalIdentity (firstWeight secondWeight : ℂ) :
      (second⁻¹ - (second - first)⁻¹) * firstWeight +
        (first⁻¹ - (first - second)⁻¹) * secondWeight =
          (first / second * firstWeight - second / first * secondWeight) / (first - second) := by
    field_simp [firstNonzero, secondNonzero, differenceNonzero, reverseNonzero]
    ring
  rw [star_sub, star_sub, star_biotSavartKernel, star_biotSavartKernel, star_biotSavartKernel, star_biotSavartKernel]
  calc
    _ = -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) *
        ((second⁻¹ - (second - first)⁻¹) * (star first)⁻¹ ^ power +
          (first⁻¹ - (first - second)⁻¹) * (star second)⁻¹ ^ power) := by ring
    _ = _ := by rw [rationalIdentity]; rfl

end EulerNonuniqueness.Section6
