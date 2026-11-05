import EulerNonuniqueness.Section6.DipoleBootstrap

noncomputable section

open Set

namespace EulerNonuniqueness.Section6

theorem strict_bootstrap_on_Icc {monitor : ℝ → ℝ} {horizon : ℝ}
    (continuous : ContinuousOn monitor (Icc 0 horizon)) (initial : monitor 0 < 0)
    (improvement : ∀ time ∈ Icc 0 horizon, (∀ current ∈ Icc 0 time, monitor current ≤ 0) → monitor time < 0) :
    ∀ time ∈ Icc 0 horizon, monitor time < 0 := by
  intro time timeInside
  by_contra failure
  have nonnegative : 0 ≤ monitor time := le_of_not_gt failure
  have intervalInside : Icc (0 : ℝ) time ⊆ Icc 0 horizon := Icc_subset_Icc le_rfl timeInside.2
  have intervalContinuous := continuous.mono intervalInside
  obtain ⟨zeroTime, zeroInside, zeroValue⟩ := intermediate_value_Icc timeInside.1 intervalContinuous
    (show (0 : ℝ) ∈ Icc (monitor 0) (monitor time) from ⟨initial.le, nonnegative⟩)
  have zerosClosed : IsClosed (Icc (0 : ℝ) time ∩ monitor ⁻¹' {0}) :=
    intervalContinuous.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have zerosCompact : IsCompact (Icc (0 : ℝ) time ∩ monitor ⁻¹' {0}) :=
    isCompact_Icc.of_isClosed_subset zerosClosed inter_subset_left
  obtain ⟨firstZero, least⟩ := zerosCompact.exists_isLeast ⟨zeroTime, zeroInside, zeroValue⟩
  have priorBound : ∀ current ∈ Icc 0 firstZero, monitor current ≤ 0 := by
    intro current currentInside
    by_contra positive
    have currentPositive : 0 < monitor current := lt_of_not_ge positive
    have currentContinuous := continuous.mono
      (Icc_subset_Icc le_rfl (currentInside.2.trans (least.1.1.2.trans timeInside.2)))
    obtain ⟨earlierZero, earlierInside, earlierValue⟩ := intermediate_value_Icc currentInside.1 currentContinuous
      (show (0 : ℝ) ∈ Icc (monitor 0) (monitor current) from ⟨initial.le, currentPositive.le⟩)
    have firstLe : firstZero ≤ earlierZero := least.2
      ⟨⟨earlierInside.1, earlierInside.2.trans (currentInside.2.trans least.1.1.2)⟩, earlierValue⟩
    have equality : current = firstZero := le_antisymm currentInside.2 (firstLe.trans earlierInside.2)
    subst current
    have zero : monitor firstZero = 0 := least.1.2
    linarith
  have strict := improvement firstZero (intervalInside least.1.1) priorBound
  have zero : monitor firstZero = 0 := least.1.2
  linarith

end EulerNonuniqueness.Section6
