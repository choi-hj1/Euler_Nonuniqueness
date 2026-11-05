import EulerNonuniqueness.Section3.DiskQuadrupole

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem diskQuadrupoleDensity_norms_summable (scales : Scales)
    (centers : ℕ → Fin 4 → Plane) (amplitudePositive : 0 < scales.amplitude)
    (frequencyPositive : 0 < scales.frequency) (ratioGreaterOne : 1 < scales.ratio)
    (alphaPositive : 0 < scales.alpha) {exponent : ℝ} (exponentBound : 1 ≤ exponent) :
    Summable (fun index => (eLpNorm (diskQuadrupoleDensity scales centers index)
      (ENNReal.ofReal exponent) volume).toReal) := by
  have envelope := scales.patch_Lp_envelope_summable amplitudePositive frequencyPositive
    ratioGreaterOne alphaPositive (zero_lt_one.trans_le exponentBound)
  have shifted : Summable (fun index => scales.amplitude * scales.omega (index + 1) ^ 4 *
      (Real.pi * scales.radius (index + 1) ^ 2) ^ (1 / exponent)) :=
    (summable_nat_add_iff 1).mpr envelope
  apply Summable.of_norm_bounded _ (shifted.mul_left 4)
  intro index
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact diskQuadrupoleDensity_eLpNorm_toReal_le scales centers index amplitudePositive exponentBound

theorem exists_initialDatum_of_disk_quadrupole_series (scales : Scales)
    (centers : ℕ → Fin 4 → Plane) (amplitudePositive : 0 < scales.amplitude)
    (frequencyPositive : 0 < scales.frequency) (ratioGreaterOne : 1 < scales.ratio)
    (alphaPositive : 0 < scales.alpha) {region : Set Plane} (compact : IsCompact region)
    (disksInside : ∀ index patch,
      Metric.ball (centers index patch) (scales.radius (index + 1)) ⊆ region) :
    ∃ initial : Vorticity, InitialDatum initial ∧ Function.support initial ⊆ region ∧
      ∀ exponent : ℝ, 1 ≤ exponent → Tendsto
        (fun count => eLpNorm ((∑ index ∈ Finset.range count, diskQuadrupoleDensity scales centers index) - initial)
          (ENNReal.ofReal exponent) volume) atTop (𝓝 0) := by
  obtain ⟨initial, compactSupport, supported, meanZero, properties⟩ :=
    exists_supported_all_finiteLp_limit_of_summable_eLpNorm
      (fun exponent _ index => diskQuadrupoleDensity_memLp scales centers index (ENNReal.ofReal exponent))
      (fun _ bound => diskQuadrupoleDensity_norms_summable scales centers amplitudePositive
        frequencyPositive ratioGreaterOne alphaPositive bound)
      compact (fun index => diskQuadrupoleDensity_support_subset scales centers index (disksInside index))
      (diskQuadrupoleDensity_integral_zero scales centers)
  exact ⟨initial, ⟨compactSupport, fun exponent bound => (properties exponent bound).1, meanZero⟩,
    supported, fun exponent bound => (properties exponent bound).2⟩

end EulerNonuniqueness.Paper
