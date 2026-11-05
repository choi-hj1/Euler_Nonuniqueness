import EulerNonuniqueness.Section3.PatchMass

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem norm_patchSign (patch : Fin 4) : ‖patchSign patch‖ = 1 := by
  unfold patchSign
  split_ifs <;> norm_num

theorem patchDensity_memLp {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ) (index : Fin count) (patch : Fin 4)
    (domainOpen : IsOpen (motion.domain time index patch))
    (domainBounded : Bornology.IsBounded (motion.domain time index patch)) (exponent : ℝ≥0∞) :
    MemLp (patchDensity scales motion time index patch) exponent volume :=
  memLp_indicator_const exponent domainOpen.measurableSet _ (Or.inr domainBounded.measure_lt_top.ne)

theorem patchDensity_eLpNorm {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ) (index : Fin count) (patch : Fin 4)
    (domainOpen : IsOpen (motion.domain time index patch))
    (amplitudePositive : 0 < scales.amplitude) {exponent : ℝ≥0∞}
    (exponentNonzero : exponent ≠ 0) (exponentFinite : exponent ≠ ∞) :
    eLpNorm (patchDensity scales motion time index patch) exponent volume =
      ENNReal.ofReal (scales.amplitude * scales.omega (index.val + 1) ^ 4) *
        volume (motion.domain time index patch) ^ (1 / exponent.toReal) := by
  rw [patchDensity, eLpNorm_indicator_const domainOpen.measurableSet exponentNonzero exponentFinite]
  congr 1
  rw [← ofReal_norm_eq_enorm, norm_mul, norm_mul, norm_patchSign, one_mul,
    Real.norm_of_nonneg amplitudePositive.le,
    Real.norm_of_nonneg (show 0 ≤ scales.omega (index.val + 1) ^ 4 by positivity)]

theorem patchDensity_eLpNorm_toReal {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ) (index : Fin count) (patch : Fin 4)
    (domainOpen : IsOpen (motion.domain time index patch))
    (domainArea : volume (motion.domain time index patch) =
      ENNReal.ofReal (Real.pi * scales.radius (index.val + 1) ^ 2))
    (amplitudePositive : 0 < scales.amplitude) {exponent : ℝ} (exponentPositive : 0 < exponent) :
    (eLpNorm (patchDensity scales motion time index patch) (ENNReal.ofReal exponent) volume).toReal =
      scales.amplitude * scales.omega (index.val + 1) ^ 4 *
        (Real.pi * scales.radius (index.val + 1) ^ 2) ^ (1 / exponent) := by
  rw [patchDensity_eLpNorm scales motion time index patch domainOpen amplitudePositive
    (ENNReal.ofReal_pos.mpr exponentPositive).ne' ENNReal.ofReal_ne_top, domainArea,
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (show 0 ≤ scales.amplitude * scales.omega (index.val + 1) ^ 4 by positivity),
    ENNReal.toReal_ofReal (show 0 ≤ Real.pi * scales.radius (index.val + 1) ^ 2 by positivity),
    ENNReal.toReal_ofReal exponentPositive.le]

end EulerNonuniqueness.Paper
