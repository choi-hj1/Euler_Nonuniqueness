import EulerNonuniqueness.Section3.QuadrupoleLp
import EulerNonuniqueness.Section1.PatchNormSummability
import EulerNonuniqueness.General.FiniteCompactSupport

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem patchDensity_hasCompactSupport {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ) (index : Fin count) (patch : Fin 4)
    (bounded : Bornology.IsBounded (motion.domain time index patch)) :
    HasCompactSupport (patchDensity scales motion time index patch) :=
  HasCompactSupport.of_support_subset_isCompact bounded.isCompact_closure
    (support_indicator_subset.trans subset_closure)

theorem quadrupoleDensity_hasCompactSupport {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ) (index : Fin count)
    (bounded : ∀ patch, Bornology.IsBounded (motion.domain time index patch)) :
    HasCompactSupport (quadrupoleDensity scales motion time index) := by
  have densityEqual : quadrupoleDensity scales motion time index =
      ∑ patch : Fin 4, patchDensity scales motion time index patch := by
    funext position
    simp only [quadrupoleDensity, Finset.sum_apply]
  rw [densityEqual]
  exact HasCompactSupport.finset_sum (fields := fun patch => patchDensity scales motion time index patch)
    Finset.univ (fun patch _ =>
    patchDensity_hasCompactSupport scales motion time index patch (bounded patch))

theorem patchVorticity_hasCompactSupport {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ)
    (bounded : ∀ index patch, Bornology.IsBounded (motion.domain time index patch)) :
    HasCompactSupport (patchVorticity scales motion time) := by
  have vorticityEqual : patchVorticity scales motion time =
      ∑ index : Fin count, quadrupoleDensity scales motion time index := by
    funext position
    simp only [patchVorticity, Finset.sum_apply]
  rw [vorticityEqual]
  exact HasCompactSupport.finset_sum (fields := fun index => quadrupoleDensity scales motion time index)
    Finset.univ (fun index _ =>
    quadrupoleDensity_hasCompactSupport scales motion time index (bounded index))

theorem patchVorticity_integral_zero {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ)
    (domainOpen : ∀ index patch, IsOpen (motion.domain time index patch))
    (domainBounded : ∀ index patch, Bornology.IsBounded (motion.domain time index patch))
    (domainArea : ∀ index patch, volume (motion.domain time index patch) =
      ENNReal.ofReal (Real.pi * scales.radius (index.val + 1) ^ 2))
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) :
    (∫ position, patchVorticity scales motion time position) = 0 := by
  unfold patchVorticity
  rw [integral_finset_sum _ (fun index _ => memLp_one_iff_integrable.mp
    (quadrupoleDensity_memLp scales motion time index (domainOpen index) (domainBounded index) 1))]
  simp only [quadrupoleDensity_integral_zero scales motion time _ (domainOpen _) (domainBounded _)
    (domainArea _) amplitudePositive frequencyPositive ratioPositive, Finset.sum_const_zero]

theorem patchVorticity_eLpNorm_toReal_le_tsum {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ)
    (domainOpen : ∀ index patch, IsOpen (motion.domain time index patch))
    (domainBounded : ∀ index patch, Bornology.IsBounded (motion.domain time index patch))
    (domainArea : ∀ index patch, volume (motion.domain time index patch) =
      ENNReal.ofReal (Real.pi * scales.radius (index.val + 1) ^ 2))
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioGreaterOne : 1 < scales.ratio) (alphaPositive : 0 < scales.alpha)
    {exponent : ℝ} (exponentBound : 1 ≤ exponent) :
    (eLpNorm (patchVorticity scales motion time) (ENNReal.ofReal exponent) volume).toReal ≤
      4 * ∑' index : ℕ, scales.amplitude * scales.omega (index + 1) ^ 4 *
        (Real.pi * scales.radius (index + 1) ^ 2) ^ (1 / exponent) := by
  have envelope := scales.patch_Lp_envelope_summable amplitudePositive frequencyPositive ratioGreaterOne
    alphaPositive (zero_lt_one.trans_le exponentBound)
  have shifted : Summable (fun index => scales.amplitude * scales.omega (index + 1) ^ 4 *
      (Real.pi * scales.radius (index + 1) ^ 2) ^ (1 / exponent)) := (summable_nat_add_iff 1).mpr envelope
  apply (patchVorticity_eLpNorm_toReal_le_sum scales motion time domainOpen domainBounded domainArea
    amplitudePositive exponentBound).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact shifted.sum_le_tsum (Finset.range count) (fun index _ => by positivity)

theorem FinitePatchEvolution.initialDatum {count : ℕ} {scales : Scales}
    {motion : PatchMotion count} {horizon : ℝ} (evolution : FinitePatchEvolution scales motion horizon)
    (horizonNonnegative : 0 ≤ horizon) (amplitudePositive : 0 < scales.amplitude)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio) :
    InitialDatum (patchVorticity scales motion 0) := by
  have domainProperties := evolution.2.2.2.1 0 ⟨le_rfl, horizonNonnegative⟩
  exact ⟨patchVorticity_hasCompactSupport scales motion 0 (fun index patch => (domainProperties index patch).2.1),
    fun exponent _ => patchVorticity_memLp scales motion 0 (fun index patch => (domainProperties index patch).1)
      (fun index patch => (domainProperties index patch).2.1) _,
    patchVorticity_integral_zero scales motion 0 (fun index patch => (domainProperties index patch).1)
      (fun index patch => (domainProperties index patch).2.1) (fun index patch => (domainProperties index patch).2.2.1)
      amplitudePositive frequencyPositive ratioPositive⟩

end EulerNonuniqueness.Paper
