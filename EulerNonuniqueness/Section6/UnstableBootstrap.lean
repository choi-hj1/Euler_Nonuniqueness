import EulerNonuniqueness.Section6.IntegrableUnstableDuhamel
import EulerNonuniqueness.Section6.StoppedBootstrap

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.Section6

theorem unstable_bootstrap_from_integral_remainder {trajectory forcing remainder : ℝ → ℝ}
    {rate scale horizon directBound envelopeBound remainderBound : ℝ}
    (scalePositive : 0 < scale) (horizonNonnegative : 0 ≤ horizon)
    (remainderNonnegative : 0 ≤ remainderBound) (gap : directBound + remainderBound < envelopeBound)
    (forcingIntegrable : IntervalIntegrable (fun current => Real.exp (-rate * current) * forcing current) volume 0 horizon)
    (equation : ∀ current ∈ Icc 0 horizon, HasDerivAt trajectory
      (rate * trajectory current + scale * forcing current + remainder current) current)
    (directInput : ∀ time ∈ Icc 0 horizon,
      |trajectory 0 + scale * (∫ current in (0 : ℝ)..time, Real.exp (-rate * current) * forcing current)| ≤ scale * directBound)
    (remainderControl : ∀ time ∈ Icc 0 horizon,
      (∀ current ∈ Icc 0 time, |trajectory current| ≤ scale * envelopeBound * Real.exp (rate * current)) →
      IntervalIntegrable (fun current => Real.exp (-rate * current) * remainder current) volume 0 time ∧
        |∫ current in (0 : ℝ)..time, Real.exp (-rate * current) * remainder current| ≤ scale * remainderBound) :
    ∀ time ∈ Icc 0 horizon, |trajectory time| < scale * envelopeBound * Real.exp (rate * time) := by
  let monitor := fun time => |Real.exp (-rate * time) * trajectory time| - scale * envelopeBound
  have trajectoryContinuous : ContinuousOn trajectory (Icc 0 horizon) :=
    fun time inside => (equation time inside).continuousAt.continuousWithinAt
  have monitorContinuous : ContinuousOn monitor (Icc 0 horizon) :=
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul trajectoryContinuous).abs).sub continuousOn_const
  have initialBound := directInput 0 ⟨le_rfl, horizonNonnegative⟩
  simp only [intervalIntegral.integral_same, mul_zero, add_zero] at initialBound
  have initial : monitor 0 < 0 := by
    dsimp only [monitor]
    simp only [mul_zero, Real.exp_zero, one_mul]
    have strict : scale * directBound < scale * envelopeBound :=
      mul_lt_mul_of_pos_left (by linarith) scalePositive
    linarith
  have cancellation (time : ℝ) : Real.exp (rate * time) * Real.exp (-rate * time) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have absoluteReconstruction (time : ℝ) : |trajectory time| =
      Real.exp (rate * time) * |Real.exp (-rate * time) * trajectory time| := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _), ← mul_assoc, cancellation, one_mul]
  have improved : ∀ time ∈ Icc 0 horizon, (∀ current ∈ Icc 0 time, monitor current ≤ 0) → monitor time < 0 := by
    intro time inside prior
    have envelope : ∀ current ∈ Icc 0 time, |trajectory current| ≤ scale * envelopeBound * Real.exp (rate * current) := by
      intro current currentInside
      have bound : |Real.exp (-rate * current) * trajectory current| ≤ scale * envelopeBound :=
        sub_nonpos.mp (prior current currentInside)
      rw [absoluteReconstruction current]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left bound (Real.exp_pos (rate * current)).le
    obtain ⟨remainderIntegrable, remainderEstimate⟩ := remainderControl time inside envelope
    have intervalSubset : uIcc (0 : ℝ) time ⊆ uIcc 0 horizon := by
      rw [uIcc_of_le inside.1, uIcc_of_le horizonNonnegative]
      exact Icc_subset_Icc le_rfl inside.2
    have identity := integrable_unstable_duhamel (forcingIntegrable.mono_set intervalSubset) remainderIntegrable
      (fun current currentInside => equation current ⟨currentInside.1, currentInside.2.trans inside.2⟩)
      (show time ∈ Icc 0 time from ⟨inside.1, le_rfl⟩)
    have coefficientEstimate : |Real.exp (-rate * time) * trajectory time| ≤ scale * (directBound + remainderBound) := by
      rw [identity]
      exact (abs_add _ _).trans ((add_le_add (directInput time inside) remainderEstimate).trans_eq (by ring))
    dsimp only [monitor]
    have strict := mul_lt_mul_of_pos_left gap scalePositive
    linarith
  have strict := strict_bootstrap_on_Icc monitorContinuous initial improved
  intro time inside
  have bound : |Real.exp (-rate * time) * trajectory time| < scale * envelopeBound :=
    sub_neg.mp (strict time inside)
  rw [absoluteReconstruction time]
  simpa only [mul_comm] using mul_lt_mul_of_pos_left bound (Real.exp_pos (rate * time))

end EulerNonuniqueness.Section6
