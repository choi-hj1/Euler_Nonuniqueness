import EulerNonuniqueness.General.FirstContact

noncomputable section

open Set

theorem exists_first_zero_of_initial_nonpos_of_nonnegative
    {monitor : ℝ → ℝ} {horizon : ℝ} (horizonNonnegative : 0 ≤ horizon)
    (continuous : ContinuousOn monitor (Icc 0 horizon)) (initial : monitor 0 ≤ 0)
    (terminal : 0 ≤ monitor horizon) :
    ∃ contact ∈ Icc 0 horizon, monitor contact = 0 ∧
      ∀ time, 0 ≤ time → time < contact → monitor time < 0 := by
  obtain ⟨zeroTime, zeroInside, zeroValue⟩ := intermediate_value_Icc horizonNonnegative continuous
    (show (0 : ℝ) ∈ Icc (monitor 0) (monitor horizon) from ⟨initial, terminal⟩)
  have zerosClosed : IsClosed (Icc (0 : ℝ) horizon ∩ monitor ⁻¹' {0}) :=
    continuous.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have zerosCompact : IsCompact (Icc (0 : ℝ) horizon ∩ monitor ⁻¹' {0}) :=
    isCompact_Icc.of_isClosed_subset zerosClosed inter_subset_left
  obtain ⟨contact, least⟩ := zerosCompact.exists_isLeast ⟨zeroTime, zeroInside, zeroValue⟩
  refine ⟨contact, least.1.1, least.1.2, ?_⟩
  intro time nonnegative earlier
  by_contra failure
  have timeBound : time ≤ horizon := earlier.le.trans least.1.1.2
  obtain ⟨earlierZero, earlierInside, earlierValue⟩ := intermediate_value_Icc nonnegative
    (continuous.mono (Icc_subset_Icc le_rfl timeBound))
    (show (0 : ℝ) ∈ Icc (monitor 0) (monitor time) from ⟨initial, le_of_not_gt failure⟩)
  have minimal : contact ≤ earlierZero := least.2
    ⟨⟨earlierInside.1, earlierInside.2.trans timeBound⟩, earlierValue⟩
  linarith [earlierInside.2]

theorem strictly_negative_of_prefix_improvement
    {monitor : ℝ → ℝ} {horizon : ℝ}
    (continuous : ContinuousOn monitor (Icc 0 horizon)) (initial : monitor 0 < 0)
    (improve : ∀ time ∈ Icc 0 horizon,
      (∀ current ∈ Icc 0 time, monitor current ≤ 0) → monitor time < 0) :
    ∀ time ∈ Icc 0 horizon, monitor time < 0 := by
  intro time inside
  by_contra failure
  obtain ⟨contact, contactInside, zero, strictBefore⟩ := exists_first_zero_of_initial_nonpos_of_nonnegative inside.1
    (continuous.mono (Icc_subset_Icc le_rfl inside.2)) initial.le (le_of_not_gt failure)
  have improved := improve contact ⟨contactInside.1, contactInside.2.trans inside.2⟩ (by
    intro current currentInside
    rcases eq_or_lt_of_le currentInside.2 with equal | earlier
    · rw [equal, zero]
    · exact (strictBefore current currentInside.1 earlier).le)
  linarith

theorem norm_strictly_confined_of_prefix_improvement
    {space : Type*} [NormedAddCommGroup space] {curve : ℝ → space} {horizon radius : ℝ}
    (continuous : ContinuousOn curve (Icc 0 horizon)) (initial : ‖curve 0‖ < radius)
    (improve : ∀ time ∈ Icc 0 horizon,
      (∀ current ∈ Icc 0 time, ‖curve current‖ ≤ radius) → ‖curve time‖ < radius) :
    ∀ time ∈ Icc 0 horizon, ‖curve time‖ < radius := by
  have estimate := strictly_negative_of_prefix_improvement (continuous.norm.sub continuousOn_const)
    (sub_neg.mpr initial) (by
      intro time inside prefixControl
      exact sub_neg.mpr (improve time inside fun current member => sub_nonpos.mp (prefixControl current member)))
  intro time inside
  exact sub_neg.mp (estimate time inside)
