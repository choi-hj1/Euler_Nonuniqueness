import EulerNonuniqueness.General.ContinuousPrefixBootstrap

noncomputable section

open Set

namespace EulerNonuniqueness.General

theorem strictly_negative_of_strict_prefix_improvement
    {monitor : ℝ → ℝ} {horizon : ℝ}
    (continuous : ContinuousOn monitor (Icc 0 horizon)) (initial : monitor 0 < 0)
    (improve : ∀ time ∈ Icc 0 horizon,
      (∀ current ∈ Icc 0 time, monitor current ≤ 0) →
      (∀ current ∈ Ico 0 time, monitor current < 0) → monitor time < 0) :
    ∀ time ∈ Icc 0 horizon, monitor time < 0 := by
  intro time inside
  by_contra failure
  obtain ⟨contact, contactInside, zero, strictBefore⟩ := exists_first_zero_of_initial_nonpos_of_nonnegative inside.1
    (continuous.mono (Icc_subset_Icc le_rfl inside.2)) initial.le (le_of_not_gt failure)
  have improved := improve contact ⟨contactInside.1, contactInside.2.trans inside.2⟩
    (by
      intro current currentInside
      rcases eq_or_lt_of_le currentInside.2 with equal | earlier
      · rw [equal, zero]
      · exact (strictBefore current currentInside.1 earlier).le)
    (fun current currentInside => strictBefore current currentInside.1 currentInside.2)
  linarith

theorem finite_strictly_negative_of_strict_prefix_improvement
    {Index : Type*} [Fintype Index] [Nonempty Index]
    {monitor : Index → ℝ → ℝ} {horizon : ℝ}
    (continuous : ∀ index, ContinuousOn (monitor index) (Icc 0 horizon))
    (initial : ∀ index, monitor index 0 < 0)
    (improve : ∀ time ∈ Icc 0 horizon,
      (∀ current ∈ Icc 0 time, ∀ index, monitor index current ≤ 0) →
      (∀ current ∈ Ico 0 time, ∀ index, monitor index current < 0) →
      ∀ index, monitor index time < 0) :
    ∀ time ∈ Icc 0 horizon, ∀ index, monitor index time < 0 := by
  classical
  let maximum : ℝ → ℝ := fun time => Finset.univ.sup' Finset.univ_nonempty (fun index => monitor index time)
  have maximumContinuous : ContinuousOn maximum (Icc 0 horizon) :=
    ContinuousOn.finset_sup'_apply Finset.univ_nonempty (fun index _ => continuous index)
  have maximumInitial : maximum 0 < 0 := by
    exact (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun index _ => initial index)
  have maximumStrict := strictly_negative_of_strict_prefix_improvement maximumContinuous maximumInitial
    (by
      intro time inside closed strict
      apply (Finset.sup'_lt_iff Finset.univ_nonempty).mpr
      intro index _
      apply improve time inside
      · intro current currentInside other
        exact (Finset.sup'_le_iff Finset.univ_nonempty _).mp (closed current currentInside) other (Finset.mem_univ _)
      · intro current currentInside other
        exact (Finset.sup'_lt_iff Finset.univ_nonempty).mp (strict current currentInside) other (Finset.mem_univ _))
  intro time inside index
  exact (Finset.sup'_lt_iff Finset.univ_nonempty).mp (maximumStrict time inside) index (Finset.mem_univ _)

end EulerNonuniqueness.General
