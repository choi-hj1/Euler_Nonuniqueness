import EulerNonuniqueness.Section6.PaperQuadrupoleStaticMoments
import EulerNonuniqueness.Section6.VorticityAngularCancellation
import EulerNonuniqueness.Section3.FinitePatchBounds

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.quadrupole_self_cancellation_genuine
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (center : ℂ) :
    Integrable (fun position => quadrupoleDensity scales motion time index position •
      biotSavart (quadrupoleDensity scales motion time index) position) ∧
    (∫ position, quadrupoleDensity scales motion time index position •
      biotSavart (quadrupoleDensity scales motion time index) position) = 0 ∧
    Integrable (fun position => @inner ℝ ℂ _ (position - center)
      (quadrupoleDensity scales motion time index position • biotSavart (quadrupoleDensity scales motion time index) position)) ∧
    (∫ position, @inner ℝ ℂ _ (position - center)
      (quadrupoleDensity scales motion time index position • biotSavart (quadrupoleDensity scales motion time index) position)) = 0 := by
  have compact := quadrupoleDensity_hasCompactSupport scales motion time index
    (fun patch => (evolution.2.2.2.1 time inside index patch).2.1)
  obtain ⟨radius, _, radiusBound⟩ := compact.isCompact.isBounded.exists_pos_norm_le
  have supported : Function.support (quadrupoleDensity scales motion time index) ⊆ Metric.closedBall 0 radius := by
    intro position member
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      radiusBound position (subset_tsupport _ member)
  have bounded (position : ℂ) : |quadrupoleDensity scales motion time index position| ≤
      ∑ patch : Fin 4, |patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4| := by
    change ‖∑ patch : Fin 4, patchDensity scales motion time index patch position‖ ≤ _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro patch _
    by_cases member : position ∈ motion.domain time index patch
    · simp only [patchDensity, indicator_of_mem member, Real.norm_eq_abs, le_refl]
    · simp only [patchDensity, indicator_of_not_mem member, norm_zero]
      exact abs_nonneg _
  have integrable := evolution.quadrupoleDensity_integrable inside index
  exact ⟨Section6.integrable_vorticity_self_interaction integrable supported bounded,
    Section6.integral_vorticity_self_interaction integrable supported bounded,
    Section6.integrable_vorticity_angular_self_interaction integrable supported bounded center,
    Section6.integral_vorticity_angular_self_interaction integrable supported bounded center⟩

end EulerNonuniqueness.Paper
