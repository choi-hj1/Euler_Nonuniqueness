import EulerNonuniqueness.Section4.ReferenceCoarseConstruction
import EulerNonuniqueness.Section4.UniversalReferencePhaseLift

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000

theorem exists_uniform_reference_coarse_preparation
    {alpha ratio : ℝ} (alphaPositive : 0 < alpha) (ratioLarge : 2 ≤ ratio) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ constantMin > (0 : ℝ),
      ∀ threshold : ℝ, 0 < threshold → threshold ≤ thresholdMax →
      ∀ constant : ℝ, constantMin ≤ constant →
      ∃ amplitudeMin > (0 : ℝ), constant ≤ amplitudeMin ∧
      ∀ amplitude : ℝ, amplitudeMin ≤ amplitude →
      ∀ᶠ frequency : ℝ in atTop,
      ∀ count : ℕ, 0 < count → ∀ phase : Fin count → ℝ,
      ∃ motion : PatchMotion count, ∃ unstable : Fin count → ℝ, ∃ phaseLift : ℝ → Fin count → ℝ,
        ReferenceInitialDisks ⟨alpha, amplitude, ratio, frequency⟩ motion phase unstable threshold ∧
        ReferencePhaseLift motion phase phaseLift ∧
        FinitePatchEvolution ⟨alpha, amplitude, ratio, frequency⟩ motion 2 ∧
        ReferenceCoarseBounds ⟨alpha, amplitude, ratio, frequency⟩ motion threshold constant := by
  obtain ⟨thresholdMax, thresholdMaxPositive, thresholdMaxSmall, constantMin, constantMinPositive, constructions⟩ :=
    exists_uniform_reference_coarse_construction alphaPositive ratioLarge
  refine ⟨thresholdMax, thresholdMaxPositive, thresholdMaxSmall, constantMin, constantMinPositive, ?_⟩
  intro threshold thresholdPositive thresholdBound constant constantLarge
  obtain ⟨constructionMin, constructionMinPositive, construction⟩ := constructions threshold thresholdPositive thresholdBound
  refine ⟨max constructionMin constant, constructionMinPositive.trans_le (le_max_left _ _), le_max_right _ _, ?_⟩
  intro amplitude amplitudeLarge
  have constructionLarge : constructionMin ≤ amplitude := (le_max_left _ _).trans amplitudeLarge
  have amplitudePositive : 0 < amplitude := constructionMinPositive.trans_le constructionLarge
  have constantPositive : 0 < constant := constantMinPositive.trans_le constantLarge
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans thresholdMaxSmall
  let scales : Scales := ⟨alpha, amplitude, ratio, 0⟩
  filter_upwards [construction amplitude constructionLarge, eventually_ge_atTop (1 : ℝ),
    scales.eventually_reference_phaseLift_of_coarse amplitudePositive ratioLarge alphaPositive thresholdSmall constantPositive.le]
    with frequency constructed frequencyLarge lifted
  intro count countPositive phase
  obtain ⟨motion, unstable, initial, evolution, coarse⟩ := constructed count countPositive phase
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyLarge
  have ratioPositive : 0 < changed.ratio := by change 0 < ratio; linarith
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (changed.location_pos _).le _)
  have actualCoarse := coarse.mono_constant constantMinPositive.le constantLarge strainNonnegative hessianNonnegative
  obtain ⟨phaseLift, lift⟩ := lifted motion initial evolution actualCoarse
  exact ⟨motion, unstable, phaseLift, initial, lift, evolution, actualCoarse⟩

end EulerNonuniqueness.Paper
