import EulerNonuniqueness.Section5.CascadeCutoffSlack
import EulerNonuniqueness.Section3.MovingContourInitialMargin
import EulerNonuniqueness.Section1.UniformScaleBounds

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

theorem cascade_cutoff_margin_of_nonpositive_geometric_monitors
    {count : ℕ} (countPositive : 0 < count) (scales : Scales)
    (configuration : FiniteContourConfiguration (count * 4)) (state : MovingContourState (count * 4))
    {factor shapeRadius gap margin : ℝ} (factorPositive : 0 < factor)
    (radiusIdentity : ∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1))
    (marginShape : margin ≤ shapeRadius / 8) (marginUnit : margin ≤ 1 / 8)
    (marginSlack : ∀ first second : Fin count × Fin 4, gap + 4 * margin ≤ 4 * cascadePairCutoffSlack scales factor first second)
    (internal : ∀ receiver source, cascadeInternalGapMonitor scales factor receiver source
      (fun label => state.2.1 (finProdFinEquiv label)) ≤ 0)
    (offset : ∀ label, cascadeLocationMonitor scales label (fun label => state.2.1 (finProdFinEquiv label)) ≤ 0)
    (radiusInternal : ∀ index : Fin count, scales.radius (index.val + 1) ≤ factor * scales.length (index.val + 1) / 1000)
    (radiusLocation : ∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (shape : ∀ label, ‖state.2.2 label - standardCircleBanach‖ ≤ shapeRadius / 2) :
    2 * margin ≤ infDist state (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ := by
  let centers := fun label : Fin count × Fin 4 => state.2.1 (finProdFinEquiv label)
  have offsets (label : Fin count × Fin 4) : ‖centers label - (scales.location (label.1.val + 1) : ℂ)‖ ≤
      scales.location (label.1.val + 1) / 100 := sub_nonpos.mp (offset label)
  have internalGap (index : Fin count) (first second : Fin 4) (different : first ≠ second) :
      factor * scales.length (index.val + 1) ≤ ‖centers (index, first) - centers (index, second)‖ := by
    have estimate := internal (index, first) (index, second)
    have condition : (index, first).1 = (index, second).1 ∧ (index, first).2 ≠ (index, second).2 := ⟨rfl, different⟩
    rw [cascadeInternalGapMonitor, if_pos condition] at estimate
    exact sub_nonpos.mp estimate
  have radius (label : Fin (count * 4)) : configuration.radius label =
      scales.radius ((finProdFinEquiv.symm label).1.val + 1) := by
    simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using
      radiusIdentity (finProdFinEquiv.symm label).1 (finProdFinEquiv.symm label).2
  apply configuration.movingStateAdmissible_infDist_lower_bound (by omega) (by norm_num)
  · intro label
    have triangle := norm_add_le
      (centers (finProdFinEquiv.symm label) - (scales.location ((finProdFinEquiv.symm label).1.val + 1) : ℂ))
      (scales.location ((finProdFinEquiv.symm label).1.val + 1) : ℂ)
    simp only [sub_add_cancel, centers, Equiv.apply_symm_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (scales.location_pos _)] at triangle
    have offsetBound := offsets (finProdFinEquiv.symm label)
    simp only [centers, Equiv.apply_symm_apply] at offsetBound
    linarith [scales.location_le_one ((finProdFinEquiv.symm label).1.val + 1)]
  · intro label
    linarith [shape label, norm_nonneg (state.2.2 label - standardCircleBanach)]
  · intro first second different
    have bound := cascade_pair_cutoff_slack_of_geometric_bounds scales centers factorPositive internalGap offsets
      radiusInternal radiusLocation (finProdFinEquiv.symm first) (finProdFinEquiv.symm second)
      (fun equality => different (finProdFinEquiv.symm.injective equality))
    have slack := marginSlack (finProdFinEquiv.symm first) (finProdFinEquiv.symm second)
    rw [radius first, radius second]
    simp only [centers, Equiv.apply_symm_apply] at bound
    linarith

end EulerNonuniqueness.Paper
