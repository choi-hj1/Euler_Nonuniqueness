import Mathlib

noncomputable section

open Set Filter
open scoped Topology

theorem exists_first_zero_of_initial_nonpos_of_positive
    {monitor : ℝ → ℝ} {horizon : ℝ} (horizonNonnegative : 0 ≤ horizon)
    (continuous : ContinuousOn monitor (Icc 0 horizon)) (initial : monitor 0 ≤ 0)
    (terminal : 0 < monitor horizon) :
    ∃ contact ∈ Icc 0 horizon, monitor contact = 0 ∧
      ∀ time, 0 ≤ time → time < contact → monitor time < 0 := by
  obtain ⟨zeroTime, zeroInside, zeroValue⟩ := intermediate_value_Icc horizonNonnegative continuous
    (show (0 : ℝ) ∈ Icc (monitor 0) (monitor horizon) from ⟨initial, terminal.le⟩)
  have zerosClosed : IsClosed (Icc (0 : ℝ) horizon ∩ monitor ⁻¹' {0}) :=
    continuous.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have zerosCompact : IsCompact (Icc (0 : ℝ) horizon ∩ monitor ⁻¹' {0}) :=
    isCompact_Icc.of_isClosed_subset zerosClosed inter_subset_left
  obtain ⟨contact, least⟩ := zerosCompact.exists_isLeast ⟨zeroTime, zeroInside, zeroValue⟩
  refine ⟨contact, least.1.1, least.1.2, ?_⟩
  intro time nonnegative earlier
  by_contra failure
  have timeBound : time ≤ horizon := earlier.le.trans least.1.1.2
  have continuousBefore := continuous.mono (Icc_subset_Icc le_rfl timeBound)
  obtain ⟨earlierZero, earlierInside, earlierValue⟩ := intermediate_value_Icc nonnegative continuousBefore
    (show (0 : ℝ) ∈ Icc (monitor 0) (monitor time) from ⟨initial, le_of_not_gt failure⟩)
  have minimal : contact ≤ earlierZero := least.2
    ⟨⟨earlierInside.1, earlierInside.2.trans timeBound⟩, earlierValue⟩
  linarith [earlierInside.2]
