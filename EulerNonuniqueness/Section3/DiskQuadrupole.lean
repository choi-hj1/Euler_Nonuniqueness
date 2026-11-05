import EulerNonuniqueness.Section3.DiskNorm
import EulerNonuniqueness.Section1.PatchNormSummability
import EulerNonuniqueness.General.SupportedLpSeries

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace EulerNonuniqueness.Paper

def diskQuadrupoleDensity (scales : Scales) (centers : ℕ → Fin 4 → Plane) (index : ℕ) : Vorticity :=
  ∑ patch : Fin 4, diskDensity (centers index patch) (scales.radius (index + 1))
    (patchSign patch * scales.amplitude * scales.omega (index + 1) ^ 4)

theorem diskQuadrupoleDensity_memLp (scales : Scales) (centers : ℕ → Fin 4 → Plane)
    (index : ℕ) (exponent : ℝ≥0∞) :
    MemLp (diskQuadrupoleDensity scales centers index) exponent volume :=
  memLp_finset_sum' Finset.univ (fun _ _ => diskDensity_memLp _ _ _ _)

theorem diskQuadrupoleDensity_eLpNorm_toReal_le (scales : Scales)
    (centers : ℕ → Fin 4 → Plane) (index : ℕ)
    (amplitudePositive : 0 < scales.amplitude) {exponent : ℝ} (exponentBound : 1 ≤ exponent) :
    (eLpNorm (diskQuadrupoleDensity scales centers index) (ENNReal.ofReal exponent) volume).toReal ≤
      4 * (scales.amplitude * scales.omega (index + 1) ^ 4 *
        (Real.pi * scales.radius (index + 1) ^ 2) ^ (1 / exponent)) := by
  have exponentPositive : 0 < exponent := zero_lt_one.trans_le exponentBound
  have lpBound : 1 ≤ ENNReal.ofReal exponent := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal exponentBound
  letI : Fact (1 ≤ ENNReal.ofReal exponent) := ⟨lpBound⟩
  let fields : Fin 4 → Vorticity := fun patch => diskDensity (centers index patch)
    (scales.radius (index + 1)) (patchSign patch * scales.amplitude * scales.omega (index + 1) ^ 4)
  have members (patch : Fin 4) : MemLp (fields patch) (ENNReal.ofReal exponent) volume :=
    diskDensity_memLp _ _ _ _
  have radiusNonnegative : 0 ≤ scales.radius (index + 1) := Real.sqrt_nonneg _
  have eachNorm (patch : Fin 4) :
      (eLpNorm (fields patch) (ENNReal.ofReal exponent) volume).toReal =
        scales.amplitude * scales.omega (index + 1) ^ 4 *
          (Real.pi * scales.radius (index + 1) ^ 2) ^ (1 / exponent) := by
    dsimp only [fields]
    rw [diskDensity_eLpNorm_toReal _ _ _ radiusNonnegative exponentPositive,
      ← Real.norm_eq_abs, norm_mul, norm_mul, norm_patchSign, one_mul,
      Real.norm_of_nonneg amplitudePositive.le,
      Real.norm_of_nonneg (show 0 ≤ scales.omega (index + 1) ^ 4 by positivity)]
  have sumEqual : diskQuadrupoleDensity scales centers index = ∑ patch : Fin 4, fields patch := rfl
  rw [sumEqual, ← Lp.norm_toLp, toLp_finset_sum members]
  calc
    ‖∑ patch : Fin 4, (members patch).toLp (fields patch)‖ ≤
        ∑ patch : Fin 4, ‖(members patch).toLp (fields patch)‖ := norm_sum_le _ _
    _ = 4 * (scales.amplitude * scales.omega (index + 1) ^ 4 *
        (Real.pi * scales.radius (index + 1) ^ 2) ^ (1 / exponent)) := by
      simp only [Lp.norm_toLp, eachNorm, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]

theorem diskQuadrupoleDensity_integral_zero (scales : Scales)
    (centers : ℕ → Fin 4 → Plane) (index : ℕ) :
    (∫ position, diskQuadrupoleDensity scales centers index position) = 0 := by
  simp only [diskQuadrupoleDensity, Finset.sum_apply]
  rw [integral_finset_sum _ (fun patch _ =>
    memLp_one_iff_integrable.mp (diskDensity_memLp _ _ _ 1))]
  have integrals (patch : Fin 4) :
      (∫ position, diskDensity (centers index patch) (scales.radius (index + 1))
        (patchSign patch * scales.amplitude * scales.omega (index + 1) ^ 4) position) =
        Real.pi * scales.radius (index + 1) ^ 2 *
          (patchSign patch * scales.amplitude * scales.omega (index + 1) ^ 4) :=
    diskDensity_integral _ _ _ (Real.sqrt_nonneg _)
  simp only [integrals]
  norm_num [Fin.sum_univ_succ, patchSign]

theorem diskQuadrupoleDensity_support_subset (scales : Scales)
    (centers : ℕ → Fin 4 → Plane) (index : ℕ) {region : Set Plane}
    (disksInside : ∀ patch, Metric.ball (centers index patch) (scales.radius (index + 1)) ⊆ region) :
    Function.support (diskQuadrupoleDensity scales centers index) ⊆ region := by
  intro position nonzero
  by_contra outside
  have zero (patch : Fin 4) : diskDensity (centers index patch) (scales.radius (index + 1))
      (patchSign patch * scales.amplitude * scales.omega (index + 1) ^ 4) position = 0 :=
    Function.nmem_support.mp fun supported => outside
      (disksInside patch (diskDensity_support_subset _ _ _ supported))
  exact nonzero (by simp only [diskQuadrupoleDensity, Finset.sum_apply, zero, Finset.sum_const_zero])

end EulerNonuniqueness.Paper
