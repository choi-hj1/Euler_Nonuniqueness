import EulerNonuniqueness.General.ContinuousPrefixBootstrap
import EulerNonuniqueness.General.CoordinateShootingWithin

noncomputable section

open Set Filter
open scoped Topology

theorem HasDerivWithinAt.nonnegative_of_left_bound_on_Icc {trajectory : ℝ → ℝ} {velocity time horizon : ℝ}
    (derivative : HasDerivWithinAt trajectory velocity (Icc 0 horizon) time)
    (inside : time ∈ Ioc 0 horizon)
    (leftBound : ∀ earlier ∈ Icc 0 time, trajectory earlier ≤ trajectory time) : 0 ≤ velocity := by
  by_contra failure
  have velocityNegative : velocity < 0 := lt_of_not_ge failure
  have leftDerivative : HasDerivWithinAt trajectory velocity (Iic time) time :=
    derivative.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE_of_mem inside)
  have slopes := hasDerivWithinAt_iff_tendsto_slope.mp leftDerivative
  rw [Iic_diff_right] at slopes
  have negativeSlopes := slopes.eventually (eventually_lt_nhds velocityNegative)
  have positiveEarlier : ∀ᶠ earlier in 𝓝[<] time, 0 < earlier :=
    (eventually_gt_nhds inside.1).filter_mono nhdsWithin_le_nhds
  obtain ⟨earlier, slopeNegative, earlierBefore, earlierPositive⟩ :=
    (negativeSlopes.and (eventually_mem_nhdsWithin.and positiveEarlier)).exists
  have earlierInside : earlier ∈ Icc 0 time := ⟨earlierPositive.le, earlierBefore.le⟩
  have inverseNegative : (earlier - time)⁻¹ < 0 := inv_lt_zero.mpr (sub_neg.mpr earlierBefore)
  have differenceNonpositive : trajectory earlier - trajectory time ≤ 0 := sub_nonpos.mpr (leftBound earlier earlierInside)
  have nonnegative := mul_nonneg_of_nonpos_of_nonpos inverseNegative.le differenceNonpositive
  rw [slope_def_module, smul_eq_mul] at slopeNegative
  linarith

theorem strictly_confined_coordinates_of_inward_derivativeWithin
    {indexType : Type*} [Fintype indexType] {trajectory : ℝ → indexType → ℝ} {radius horizon : ℝ}
    (radiusPositive : 0 < radius) (continuous : ContinuousOn trajectory (Icc 0 horizon))
    (initial : ‖trajectory 0‖ < radius)
    (inward : ∀ time ∈ Ioc 0 horizon,
      (∀ current ∈ Icc 0 time, ‖trajectory current‖ ≤ radius) →
      ∀ coordinate, ∃ velocity, HasDerivWithinAt (fun current => trajectory current coordinate) velocity (Icc 0 horizon) time ∧
        (trajectory time coordinate = radius → velocity < 0) ∧
        (trajectory time coordinate = -radius → 0 < velocity)) :
    ∀ time ∈ Icc 0 horizon, ‖trajectory time‖ < radius := by
  intro time inside
  by_contra failure
  have monitorContinuous : ContinuousOn (fun current => ‖trajectory current‖ - radius) (Icc 0 time) :=
    (continuous.norm.sub continuousOn_const).mono (Icc_subset_Icc le_rfl inside.2)
  obtain ⟨contact, contactInside, zero, strictBefore⟩ := exists_first_zero_of_initial_nonpos_of_nonnegative inside.1
    monitorContinuous (sub_nonpos.mpr initial.le) (sub_nonneg.mpr (le_of_not_gt failure))
  have contactNorm : ‖trajectory contact‖ = radius := sub_eq_zero.mp zero
  have contactPositive : 0 < contact := by
    rcases eq_or_lt_of_le contactInside.1 with equal | positive
    · rw [← equal] at contactNorm
      linarith
    · exact positive
  have prefixBound : ∀ current ∈ Icc 0 contact, ‖trajectory current‖ ≤ radius := by
    intro current member
    rcases eq_or_lt_of_le member.2 with equal | earlier
    · rw [equal, contactNorm]
    · exact (sub_neg.mp (strictBefore current member.1 earlier)).le
  have contactInHorizon : contact ∈ Ioc 0 horizon := ⟨contactPositive, contactInside.2.trans inside.2⟩
  obtain ⟨coordinate, onFace⟩ := exists_coordinate_abs_eq_norm_of_norm_pos
    (show 0 < ‖trajectory contact‖ from radiusPositive.trans_eq contactNorm.symm)
  rw [contactNorm] at onFace
  obtain ⟨velocity, derivative, positiveFace, negativeFace⟩ := inward contact contactInHorizon prefixBound coordinate
  have componentBound (current : ℝ) (member : current ∈ Icc 0 contact) : |trajectory current coordinate| ≤ radius := by
    have coordinateEstimate : |trajectory current coordinate| ≤ ‖trajectory current‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (trajectory current) coordinate
    exact coordinateEstimate.trans (prefixBound current member)
  rcases (abs_eq radiusPositive.le).mp onFace with positive | negative
  · have velocityNonnegative := derivative.nonnegative_of_left_bound_on_Icc contactInHorizon (by
      intro earlier member
      rw [positive]
      exact (le_abs_self _).trans (componentBound earlier member))
    linarith [positiveFace positive]
  · have velocityNonpositive := derivative.neg.nonnegative_of_left_bound_on_Icc contactInHorizon (by
      intro earlier member
      change -trajectory earlier coordinate ≤ -trajectory contact coordinate
      rw [negative, neg_neg]
      exact (neg_le_abs _).trans (componentBound earlier member))
    linarith [negativeFace negative]
