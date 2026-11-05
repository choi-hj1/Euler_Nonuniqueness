import EulerNonuniqueness.Section1.DiskInitialSeries
import EulerNonuniqueness.Section3.DiskQuadrupoleContinuity
import EulerNonuniqueness.General.CompactCoordinateSubsequence
import EulerNonuniqueness.General.SupportedLpLimit

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem exists_common_initialDatum_of_disk_arrays (scales : Scales)
    (centers : ℕ → ℕ → Fin 4 → Plane) (amplitudePositive : 0 < scales.amplitude)
    (frequencyPositive : 0 < scales.frequency) (ratioGreaterOne : 1 < scales.ratio)
    (alphaPositive : 0 < scales.alpha) {lengths : ℕ → ℕ} (lengthsTendsto : Tendsto lengths atTop atTop)
    {centerRegion region : Set Plane} (centersCompact : IsCompact centerRegion)
    (centersInside : ∀ step index patch, centers step index patch ∈ centerRegion)
    (compact : IsCompact region) (disksInside : ∀ step index patch,
      Metric.ball (centers step index patch) (scales.radius (index + 1)) ⊆ region) :
    ∃ initial : Vorticity, InitialDatum initial ∧ Function.support initial ⊆ region ∧
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
        ∀ exponent : ℝ, 1 ≤ exponent → Tendsto
          (fun step => eLpNorm
            ((∑ index ∈ Finset.range (lengths (subsequence step)),
              diskQuadrupoleDensity scales (centers (subsequence step)) index) - initial)
            (ENNReal.ofReal exponent) volume) atTop (𝓝 0) := by
  classical
  obtain ⟨limitCenters, _, subsequence, increasing, centerConverges⟩ :=
    exists_coordinatewise_convergent_subsequence_of_common_compact_range centersCompact
      (sequence := fun step (coordinate : ℕ × Fin 4) => centers step coordinate.1 coordinate.2)
      (fun step coordinate => centersInside step coordinate.1 coordinate.2)
  let rows : ℕ → ℕ → Vorticity := fun step index =>
    if index < lengths (subsequence step) then diskQuadrupoleDensity scales (centers (subsequence step)) index else 0
  let limits : ℕ → Vorticity := fun index =>
    diskQuadrupoleDensity scales (fun index patch => limitCenters (index, patch)) index
  have members (exponent : ℝ) (_ : 1 ≤ exponent) (step index : ℕ) :
      MemLp (rows step index) (ENNReal.ofReal exponent) volume := by
    dsimp only [rows]
    split_ifs
    · exact diskQuadrupoleDensity_memLp _ _ _ _
    · exact MemLp.zero
  have limitMembers (exponent : ℝ) (_ : 1 ≤ exponent) (index : ℕ) :
      MemLp (limits index) (ENNReal.ofReal exponent) volume := diskQuadrupoleDensity_memLp _ _ _ _
  have domination (exponent : ℝ) (exponentBound : 1 ≤ exponent) :
      ∃ bounds : ℕ → ℝ, Summable bounds ∧ ∀ step index,
        (eLpNorm (rows step index) (ENNReal.ofReal exponent) volume).toReal ≤ bounds index := by
    let bounds : ℕ → ℝ := fun index => 4 * (scales.amplitude * scales.omega (index + 1) ^ 4 *
      (Real.pi * scales.radius (index + 1) ^ 2) ^ (1 / exponent))
    have envelope := scales.patch_Lp_envelope_summable amplitudePositive frequencyPositive
      ratioGreaterOne alphaPositive (zero_lt_one.trans_le exponentBound)
    have shifted : Summable (fun index => scales.amplitude * scales.omega (index + 1) ^ 4 *
        (Real.pi * scales.radius (index + 1) ^ 2) ^ (1 / exponent)) :=
      (summable_nat_add_iff 1).mpr envelope
    refine ⟨bounds, shifted.mul_left 4, fun step index => ?_⟩
    dsimp only [rows]
    split_ifs
    · exact diskQuadrupoleDensity_eLpNorm_toReal_le scales _ index amplitudePositive exponentBound
    · simp only [eLpNorm_zero, ENNReal.toReal_zero]
      dsimp only [bounds]
      positivity
  have coordinateConverges (exponent : ℝ) (exponentBound : 1 ≤ exponent) (index : ℕ) :
      Tendsto (fun step => eLpNorm (rows step index - limits index)
        (ENNReal.ofReal exponent) volume) atTop (𝓝 0) := by
    have lpBound : 1 ≤ ENNReal.ofReal exponent := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal exponentBound
    letI : Fact (1 ≤ ENNReal.ofReal exponent) := ⟨lpBound⟩
    have included : ∀ᶠ step in atTop, index < lengths (subsequence step) :=
      (lengthsTendsto.comp increasing.tendsto_atTop).eventually (eventually_gt_atTop index)
    have quadConverges := tendsto_eLpNorm_diskQuadrupoleDensity_sub scales
      (centers := fun step => centers (subsequence step))
      (limitCenters := fun index patch => limitCenters (index, patch))
      index (exponent := ENNReal.ofReal exponent) ENNReal.ofReal_ne_top
      (fun patch => centerConverges (index, patch))
    apply quadConverges.congr'
    filter_upwards [included] with step inside
    simp only [rows, if_pos inside, limits]
  have truncated (step index : ℕ) (outside : lengths (subsequence step) ≤ index) : rows step index = 0 := by
    simp only [rows, if_neg (not_lt.mpr outside)]
  obtain ⟨raw, rawProperties⟩ := exists_all_finiteLp_limit_of_dominated_triangular_sums
    members limitMembers domination coordinateConverges truncated
  let sequence : ℕ → Vorticity := fun step =>
    ∑ index ∈ Finset.range (lengths (subsequence step)), diskQuadrupoleDensity scales (centers (subsequence step)) index
  have prefixEqual (step : ℕ) :
      (∑ index ∈ Finset.range (lengths (subsequence step)), rows step index) = sequence step := by
    apply Finset.sum_congr rfl
    intro index inside
    simp only [rows, if_pos (Finset.mem_range.mp inside)]
  have integrable (step : ℕ) : Integrable (sequence step) := by
    apply memLp_one_iff_integrable.mp
    exact memLp_finset_sum' _ (fun index _ => diskQuadrupoleDensity_memLp _ _ index 1)
  have possible (exponent : ℝ) (exponentBound : 1 ≤ exponent) : ∃ limit : Vorticity,
      MemLp limit (ENNReal.ofReal exponent) volume ∧ Tendsto
        (fun step => eLpNorm (sequence step - limit) (ENNReal.ofReal exponent) volume) atTop (𝓝 0) := by
    refine ⟨raw, (rawProperties exponent exponentBound).1, ?_⟩
    simpa only [prefixEqual] using (rawProperties exponent exponentBound).2
  have supported (step : ℕ) : Function.support (sequence step) ⊆ region := by
    intro position nonzero
    by_contra outside
    have zero (index : ℕ) : diskQuadrupoleDensity scales (centers (subsequence step)) index position = 0 :=
      Function.nmem_support.mp fun inSupport => outside
        (diskQuadrupoleDensity_support_subset scales _ index (disksInside (subsequence step) index) inSupport)
    exact nonzero (by simp only [sequence, Finset.sum_apply, zero, Finset.sum_const_zero])
  have zeroMean (step : ℕ) : (∫ position, sequence step position) = 0 := by
    simp only [sequence, Finset.sum_apply]
    rw [integral_finset_sum _ (fun index _ =>
      memLp_one_iff_integrable.mp (diskQuadrupoleDensity_memLp _ _ index 1))]
    simp only [diskQuadrupoleDensity_integral_zero, Finset.sum_const_zero]
  obtain ⟨initial, compactSupport, initialSupported, initialMean, properties⟩ :=
    exists_supported_all_finiteLp_limit integrable possible compact supported zeroMean
  exact ⟨initial, ⟨compactSupport, fun exponent bound => (properties exponent bound).1, initialMean⟩,
    initialSupported, subsequence, increasing, fun exponent bound => (properties exponent bound).2⟩

end EulerNonuniqueness.Paper
