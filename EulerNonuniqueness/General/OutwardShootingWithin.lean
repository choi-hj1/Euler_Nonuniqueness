import EulerNonuniqueness.General.NoRetraction
import EulerNonuniqueness.General.ContactTimeContinuity
import EulerNonuniqueness.General.FirstContact

noncomputable section

open Set Filter Metric
open scoped Topology

theorem exists_confined_trajectory_of_strict_outward_boundary_before_horizon
    {space : Type*} [NormedAddCommGroup space] [NormedSpace ℝ space] [FiniteDimensional ℝ space]
    {radius horizon : ℝ} (radiusPositive : 0 < radius)
    {trajectory : closedBall (0 : space) radius → ℝ → space}
    (jointContinuous : Continuous (fun point : closedBall (0 : space) radius × ℝ => trajectory point.1 point.2))
    (initial : ∀ parameter, trajectory parameter 0 = parameter)
    (outward : ∀ parameter time, time ∈ Ico 0 horizon →
      (∀ current ∈ Icc 0 time, ‖trajectory parameter current‖ ≤ radius) →
      ‖trajectory parameter time‖ = radius → ∀ epsilon, 0 < epsilon →
      ∃ later, time < later ∧ later < time + epsilon ∧ radius < ‖trajectory parameter later‖) :
    ∃ parameter, ∀ time ∈ Icc 0 horizon, ‖trajectory parameter time‖ ≤ radius := by
  classical
  by_contra noConfined
  push_neg at noConfined
  choose escapeTime escapeInside escapePositive using noConfined
  have contacts : ∀ parameter : closedBall (0 : space) radius, ∃ contact ∈ Ico 0 horizon,
      ‖trajectory parameter contact‖ = radius ∧
        ∀ time, 0 ≤ time → time < contact → ‖trajectory parameter time‖ < radius := by
    intro parameter
    have sliceContinuous : Continuous (fun time => ‖trajectory parameter time‖ - radius) :=
      ((jointContinuous.comp (continuous_const.prodMk continuous_id)).norm).sub continuous_const
    have initialBound : ‖trajectory parameter 0‖ - radius ≤ 0 := by
      rw [initial]
      have member := parameter.property
      rw [mem_closedBall, dist_zero_right] at member
      linarith
    obtain ⟨contact, inside, zero, strict⟩ := exists_first_zero_of_initial_nonpos_of_positive
      (escapeInside parameter).1 sliceContinuous.continuousOn initialBound (sub_pos.mpr (escapePositive parameter))
    have strictlyBefore : contact < escapeTime parameter := by
      apply lt_of_le_of_ne inside.2
      intro equality
      have value : ‖trajectory parameter (escapeTime parameter)‖ = radius := by
        simpa only [equality] using sub_eq_zero.mp zero
      linarith [escapePositive parameter]
    exact ⟨contact, ⟨inside.1, strictlyBefore.trans_le (escapeInside parameter).2⟩, sub_eq_zero.mp zero,
      fun time nonnegative earlier => sub_neg.mp (strict time nonnegative earlier)⟩
  choose contactTime timeBounds contact strictBefore using contacts
  have prefixControl (parameter : closedBall (0 : space) radius) :
      ∀ current ∈ Icc 0 (contactTime parameter), ‖trajectory parameter current‖ ≤ radius := by
    intro current inside
    rcases eq_or_lt_of_le inside.2 with same | earlier
    · rw [same, contact]
    · exact (strictBefore parameter current inside.1 earlier).le
  have contactTimeContinuous : Continuous contactTime := by
    apply continuous_contactTime_of_strict_crossing
      (monitor := fun parameter time => ‖trajectory parameter time‖ - radius)
      ((jointContinuous.norm).sub continuous_const) (fun parameter => ⟨(timeBounds parameter).1, (timeBounds parameter).2.le⟩)
      (fun parameter => sub_eq_zero.mpr (contact parameter))
      (fun parameter time nonnegative earlier => sub_neg.mpr (strictBefore parameter time nonnegative earlier))
    intro parameter epsilon epsilonPositive
    obtain ⟨later, after, before, positive⟩ := outward parameter (contactTime parameter)
      (timeBounds parameter) (prefixControl parameter) (contact parameter) epsilon epsilonPositive
    exact ⟨later, after, before, sub_pos.mpr positive⟩
  apply no_continuous_ball_boundary_retraction radiusPositive
    (retraction := fun parameter => trajectory parameter (contactTime parameter))
    (jointContinuous.comp (continuous_id.prodMk contactTimeContinuous)) contact
  intro parameter onBoundary
  have contactZero : contactTime parameter = 0 := by
    have nonnegative := (timeBounds parameter).1
    by_contra nonzero
    have positive := lt_of_le_of_ne nonnegative (Ne.symm nonzero)
    have contradiction := strictBefore parameter 0 le_rfl positive
    rw [initial, onBoundary] at contradiction
    exact (lt_irrefl radius) contradiction
  rw [contactZero, initial]

