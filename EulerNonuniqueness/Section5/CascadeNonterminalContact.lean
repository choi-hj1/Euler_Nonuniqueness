import EulerNonuniqueness.Section5.CascadeTerminalInternalGap

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem exists_cascade_nonterminal_contact_continuation (orbit : SeparatingOrbit)
    (normalized : IsNormalizedSeparatingOrbit orbit) :
    ∃ sectionTime > (0 : ℝ), ∀ scales : Scales,
    0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ {factor threshold scaleRoot boundaryConstant : ℝ}, 0 < factor → factor ≤ 1 / 8 →
    0 < scaleRoot → 0 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, path.stop < 1 →
      ∃ index : Fin count, index.val + 1 < count ∧ ∃ first second : Fin 4, first ≠ second ∧
        ‖patchCentroid prepared.trajectory.movingFamily.patchMotion path.stop index first -
          patchCentroid prepared.trajectory.movingFamily.patchMotion path.stop index second‖ =
            factor * ({scales with frequency := frequency} : Scales).length (index.val + 1) := by
  obtain ⟨sectionTime, sectionPositive, terminalGap⟩ :=
    exists_cascade_terminal_gap_continuation orbit normalized
  refine ⟨sectionTime, sectionPositive, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive factor threshold scaleRoot boundaryConstant
    factorPositive factorSmall rootPositive boundaryNonnegative
  filter_upwards [terminalGap scales amplitudePositive ratioBound alphaPositive
    factorPositive factorSmall rootPositive boundaryNonnegative] with frequency actualGap
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path premature
  obtain ⟨index, first, second, different, contact⟩ := path.premature_contact premature
  have notLast : index.val + 1 ≠ count := by
    intro last
    have lower := actualGap count phase dipoleAngle prepared path index last path.stop
      ⟨path.stopPositive.le, le_rfl⟩ first second different
    rw [contact] at lower
    have positive := ({scales with frequency := frequency} : Scales).length_pos (index.val + 1)
    have scaled := mul_le_mul_of_nonneg_right factorSmall positive.le
    nlinarith
  exact ⟨index, lt_of_le_of_ne (Nat.succ_le_of_lt index.isLt) notLast,
    first, second, different, contact⟩

end EulerNonuniqueness.Paper

