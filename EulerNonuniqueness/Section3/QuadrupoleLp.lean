import EulerNonuniqueness.Section3.PatchLp
import EulerNonuniqueness.General.FiniteLpNormBounds

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem quadrupoleDensity_memLp {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ) (index : Fin count)
    (domainOpen : ∀ patch, IsOpen (motion.domain time index patch))
    (domainBounded : ∀ patch, Bornology.IsBounded (motion.domain time index patch)) (exponent : ℝ≥0∞) :
    MemLp (quadrupoleDensity scales motion time index) exponent volume :=
  memLp_finset_sum' Finset.univ (fun patch _ =>
    patchDensity_memLp scales motion time index patch (domainOpen patch) (domainBounded patch) exponent)

theorem quadrupoleDensity_eLpNorm_toReal_le {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ) (index : Fin count)
    (domainOpen : ∀ patch, IsOpen (motion.domain time index patch))
    (domainBounded : ∀ patch, Bornology.IsBounded (motion.domain time index patch))
    (domainArea : ∀ patch, volume (motion.domain time index patch) =
      ENNReal.ofReal (Real.pi * scales.radius (index.val + 1) ^ 2))
    (amplitudePositive : 0 < scales.amplitude) {exponent : ℝ} (exponentBound : 1 ≤ exponent) :
    (eLpNorm (quadrupoleDensity scales motion time index) (ENNReal.ofReal exponent) volume).toReal ≤
      4 * (scales.amplitude * scales.omega (index.val + 1) ^ 4 *
        (Real.pi * scales.radius (index.val + 1) ^ 2) ^ (1 / exponent)) := by
  have exponentPositive : 0 < exponent := zero_lt_one.trans_le exponentBound
  have lpBound : 1 ≤ ENNReal.ofReal exponent := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal exponentBound
  letI : Fact (1 ≤ ENNReal.ofReal exponent) := ⟨lpBound⟩
  have densityEqual : quadrupoleDensity scales motion time index =
      ∑ patch : Fin 4, patchDensity scales motion time index patch := by
    funext position
    simp only [quadrupoleDensity, Finset.sum_apply]
  rw [densityEqual]
  calc
    _ ≤ ∑ patch : Fin 4,
        (eLpNorm (patchDensity scales motion time index patch) (ENNReal.ofReal exponent) volume).toReal :=
      eLpNorm_toReal_finset_sum_le
        (fun patch => patchDensity_memLp scales motion time index patch
          (domainOpen patch) (domainBounded patch) _) Finset.univ
    _ = _ := by
      simp only [patchDensity_eLpNorm_toReal scales motion time index _ (domainOpen _) (domainArea _)
        amplitudePositive exponentPositive, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]

theorem patchVorticity_memLp {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ)
    (domainOpen : ∀ index patch, IsOpen (motion.domain time index patch))
    (domainBounded : ∀ index patch, Bornology.IsBounded (motion.domain time index patch)) (exponent : ℝ≥0∞) :
    MemLp (patchVorticity scales motion time) exponent volume := by
  have vorticityEqual : patchVorticity scales motion time =
      ∑ index : Fin count, quadrupoleDensity scales motion time index := by
    funext position
    simp only [patchVorticity, Finset.sum_apply]
  rw [vorticityEqual]
  exact memLp_finset_sum' Finset.univ (fun index _ =>
    quadrupoleDensity_memLp scales motion time index (domainOpen index) (domainBounded index) exponent)

theorem patchVorticity_eLpNorm_toReal_le_sum {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ)
    (domainOpen : ∀ index patch, IsOpen (motion.domain time index patch))
    (domainBounded : ∀ index patch, Bornology.IsBounded (motion.domain time index patch))
    (domainArea : ∀ index patch, volume (motion.domain time index patch) =
      ENNReal.ofReal (Real.pi * scales.radius (index.val + 1) ^ 2))
    (amplitudePositive : 0 < scales.amplitude) {exponent : ℝ} (exponentBound : 1 ≤ exponent) :
    (eLpNorm (patchVorticity scales motion time) (ENNReal.ofReal exponent) volume).toReal ≤
      4 * ∑ index ∈ Finset.range count, scales.amplitude * scales.omega (index + 1) ^ 4 *
        (Real.pi * scales.radius (index + 1) ^ 2) ^ (1 / exponent) := by
  have lpBound : 1 ≤ ENNReal.ofReal exponent := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal exponentBound
  letI : Fact (1 ≤ ENNReal.ofReal exponent) := ⟨lpBound⟩
  have vorticityEqual : patchVorticity scales motion time =
      ∑ index : Fin count, quadrupoleDensity scales motion time index := by
    funext position
    simp only [patchVorticity, Finset.sum_apply]
  rw [vorticityEqual]
  calc
    _ ≤ ∑ index : Fin count,
        (eLpNorm (quadrupoleDensity scales motion time index) (ENNReal.ofReal exponent) volume).toReal :=
      eLpNorm_toReal_finset_sum_le
        (fun index => quadrupoleDensity_memLp scales motion time index
          (domainOpen index) (domainBounded index) _) Finset.univ
    _ ≤ ∑ index : Fin count, 4 * (scales.amplitude * scales.omega (index.val + 1) ^ 4 *
        (Real.pi * scales.radius (index.val + 1) ^ 2) ^ (1 / exponent)) :=
      Finset.sum_le_sum fun index _ => quadrupoleDensity_eLpNorm_toReal_le scales motion time index
        (domainOpen index) (domainBounded index) (domainArea index) amplitudePositive exponentBound
    _ = 4 * ∑ index ∈ Finset.range count, scales.amplitude * scales.omega (index + 1) ^ 4 *
        (Real.pi * scales.radius (index + 1) ^ 2) ^ (1 / exponent) := by
      rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range
        (fun index => scales.amplitude * scales.omega (index + 1) ^ 4 *
          (Real.pi * scales.radius (index + 1) ^ 2) ^ (1 / exponent)) count]

end EulerNonuniqueness.Paper
