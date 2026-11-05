import EulerNonuniqueness.General.StrictPrefixBootstrap

noncomputable section

open Set

namespace EulerNonuniqueness.General

theorem exists_positive_finite_monitor_stop {Index : Type*} [Fintype Index] [Nonempty Index]
    (monitor : Index → ℝ → ℝ) {horizon : ℝ} (horizonPositive : 0 < horizon)
    (continuous : ∀ index, ContinuousOn (monitor index) (Icc 0 horizon))
    (initial : ∀ index, monitor index 0 < 0) :
    ∃ stop : ℝ, 0 < stop ∧ stop ≤ horizon ∧
      (∀ time ∈ Icc 0 stop, ∀ index, monitor index time ≤ 0) ∧
      (∀ time ∈ Ico 0 stop, ∀ index, monitor index time < 0) ∧
      (stop = horizon ∨ ∃ index, monitor index stop = 0) := by
  classical
  let maximum := fun time => Finset.univ.sup' Finset.univ_nonempty (fun index => monitor index time)
  have maximumContinuous : ContinuousOn maximum (Icc 0 horizon) :=
    ContinuousOn.finset_sup'_apply Finset.univ_nonempty (fun index _ => continuous index)
  have maximumInitial : maximum 0 < 0 :=
    (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun index _ => initial index)
  by_cases everywhere : ∀ time ∈ Icc (0 : ℝ) horizon, maximum time < 0
  · refine ⟨horizon, horizonPositive, le_rfl, ?_, ?_, Or.inl rfl⟩
    · intro time member index
      exact ((Finset.sup'_lt_iff Finset.univ_nonempty).mp (everywhere time member) index (Finset.mem_univ _)).le
    · intro time member index
      exact (Finset.sup'_lt_iff Finset.univ_nonempty).mp
        (everywhere time ⟨member.1, member.2.le⟩) index (Finset.mem_univ _)
  simp only [not_forall, _root_.not_imp, not_lt] at everywhere
  obtain ⟨time, inside, bad⟩ := everywhere
  obtain ⟨stop, stopInside, zero, before⟩ := exists_first_zero_of_initial_nonpos_of_nonnegative inside.1
    (maximumContinuous.mono (Icc_subset_Icc le_rfl inside.2)) maximumInitial.le bad
  have stopPositive : 0 < stop := by
    have different : stop ≠ 0 := by
      intro equal
      rw [equal] at zero
      linarith
    exact lt_of_le_of_ne stopInside.1 (Ne.symm different)
  refine ⟨stop, stopPositive, stopInside.2.trans inside.2, ?_, ?_, ?_⟩
  · intro current member index
    have maximumBound : maximum current ≤ 0 := by
      rcases eq_or_lt_of_le member.2 with equal | earlier
      · simpa only [equal] using zero.le
      · exact (before current member.1 earlier).le
    exact (Finset.sup'_le_iff Finset.univ_nonempty _).mp maximumBound index (Finset.mem_univ _)
  · intro current member index
    exact (Finset.sup'_lt_iff Finset.univ_nonempty).mp (before current member.1 member.2)
      index (Finset.mem_univ _)
  · obtain ⟨index, _, attained⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty
      (fun index => monitor index stop)
    exact Or.inr ⟨index, attained.symm.trans zero⟩

end EulerNonuniqueness.General
