import EulerNonuniqueness.General.OutwardShootingWithin
import EulerNonuniqueness.General.DerivativeWithinCrossing

noncomputable section

open Set Metric

theorem exists_confined_coordinates_of_outward_derivativeWithin
    {indexType : Type*} [Fintype indexType] {radius horizon : ℝ} (radiusPositive : 0 < radius)
    {trajectory : closedBall (0 : indexType → ℝ) radius → ℝ → indexType → ℝ}
    (jointContinuous : Continuous (fun point : closedBall (0 : indexType → ℝ) radius × ℝ => trajectory point.1 point.2))
    (initial : ∀ parameter, trajectory parameter 0 = parameter)
    (outward : ∀ parameter time, time ∈ Ico 0 horizon →
      (∀ current ∈ Icc 0 time, ∀ coordinate, |trajectory parameter current coordinate| ≤ radius) →
      ∀ coordinate, ∃ velocity, HasDerivWithinAt (fun current => trajectory parameter current coordinate) velocity (Icc 0 horizon) time ∧
        (trajectory parameter time coordinate = radius → 0 < velocity) ∧
        (trajectory parameter time coordinate = -radius → velocity < 0)) :
    ∃ parameter, ∀ time ∈ Icc 0 horizon, ∀ coordinate, |trajectory parameter time coordinate| ≤ radius := by
  obtain ⟨parameter, confined⟩ := exists_confined_trajectory_of_strict_outward_boundary_before_horizon radiusPositive jointContinuous initial
    (by
      intro parameter time inside prefixControl onBoundary epsilon epsilonPositive
      have coordinateControl : ∀ current ∈ Icc 0 time, ∀ coordinate,
          |trajectory parameter current coordinate| ≤ radius := by
        intro current currentInside coordinate
        simpa only [Real.norm_eq_abs] using
          (norm_le_pi_norm (trajectory parameter current) coordinate).trans (prefixControl current currentInside)
      obtain ⟨coordinate, onFace⟩ := exists_coordinate_abs_eq_norm_of_norm_pos
        (show 0 < ‖trajectory parameter time‖ from onBoundary.symm ▸ radiusPositive)
      rw [onBoundary] at onFace
      obtain ⟨velocity, derivative, positiveFace, negativeFace⟩ := outward parameter time inside coordinateControl coordinate
      rcases (abs_eq radiusPositive.le).mp onFace with positive | negative
      · obtain ⟨later, after, before, increase⟩ := derivative.exists_strict_increase_right_of_Icc inside
          (positiveFace positive) epsilonPositive
        refine ⟨later, after, before, ?_⟩
        have absoluteUpper : trajectory parameter later coordinate ≤ ‖trajectory parameter later‖ :=
          (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (trajectory parameter later) coordinate)
        linarith
      · obtain ⟨later, after, before, increase⟩ := derivative.neg.exists_strict_increase_right_of_Icc inside
          (neg_pos.mpr (negativeFace negative)) epsilonPositive
        refine ⟨later, after, before, ?_⟩
        have absoluteUpper : -trajectory parameter later coordinate ≤ ‖trajectory parameter later‖ :=
          (neg_le_abs _).trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (trajectory parameter later) coordinate)
        linarith)
  refine ⟨parameter, ?_⟩
  intro time inside coordinate
  simpa only [Real.norm_eq_abs] using
    (norm_le_pi_norm (trajectory parameter time) coordinate).trans (confined time inside)

