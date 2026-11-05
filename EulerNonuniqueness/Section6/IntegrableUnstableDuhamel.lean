import EulerNonuniqueness.Section6.UnstableDuhamel

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.Section6

theorem integrable_unstable_duhamel {trajectory forcing remainder : ℝ → ℝ}
    {rate scale horizon time : ℝ}
    (forcingIntegrable : IntervalIntegrable (fun current => Real.exp (-rate * current) * forcing current) volume 0 horizon)
    (remainderIntegrable : IntervalIntegrable (fun current => Real.exp (-rate * current) * remainder current) volume 0 horizon)
    (equation : ∀ current ∈ Icc 0 horizon, HasDerivAt trajectory
      (rate * trajectory current + scale * forcing current + remainder current) current)
    (inside : time ∈ Icc 0 horizon) :
    Real.exp (-rate * time) * trajectory time = trajectory 0 +
      scale * (∫ current in (0 : ℝ)..time, Real.exp (-rate * current) * forcing current) +
        ∫ current in (0 : ℝ)..time, Real.exp (-rate * current) * remainder current := by
  have intervalInside : uIcc (0 : ℝ) time ⊆ Icc 0 horizon := by
    rw [uIcc_of_le inside.1]
    exact Icc_subset_Icc le_rfl inside.2
  have intervalSubset : uIcc (0 : ℝ) time ⊆ uIcc 0 horizon :=
    intervalInside.trans Icc_subset_uIcc
  have forcingLocal := forcingIntegrable.mono_set intervalSubset
  have remainderLocal := remainderIntegrable.mono_set intervalSubset
  have derivative (current : ℝ) (currentInside : current ∈ uIcc 0 time) :
      HasDerivAt (fun other => Real.exp (-rate * other) * trajectory other)
        (scale * (Real.exp (-rate * current) * forcing current) + Real.exp (-rate * current) * remainder current) current := by
    convert (((hasDerivAt_id current).const_mul (-rate)).exp).mul
      (equation current (intervalInside currentInside)) using 1
    simp only [id_eq, mul_one]
    ring
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt derivative
    ((forcingLocal.const_mul scale).add remainderLocal)
  rw [intervalIntegral.integral_add (forcingLocal.const_mul scale) remainderLocal,
    intervalIntegral.integral_const_mul] at identity
  simp only [mul_zero, Real.exp_zero, one_mul] at identity
  linarith

theorem integrable_unstable_coefficient_error {trajectory forcing remainder : ℝ → ℝ}
    {rate scale horizon time coefficient tail error : ℝ}
    (forcingIntegrable : IntervalIntegrable (fun current => Real.exp (-rate * current) * forcing current) volume 0 horizon)
    (remainderIntegrable : IntervalIntegrable (fun current => Real.exp (-rate * current) * remainder current) volume 0 horizon)
    (equation : ∀ current ∈ Icc 0 horizon, HasDerivAt trajectory
      (rate * trajectory current + scale * forcing current + remainder current) current)
    (inside : time ∈ Icc 0 horizon)
    (directBound : |trajectory 0 + scale * (∫ current in (0 : ℝ)..time,
      Real.exp (-rate * current) * forcing current) - scale * coefficient| ≤ scale * tail)
    (remainderBound : |∫ current in (0 : ℝ)..time,
      Real.exp (-rate * current) * remainder current| ≤ scale * error) :
    |Real.exp (-rate * time) * trajectory time - scale * coefficient| ≤ scale * (tail + error) := by
  rw [integrable_unstable_duhamel forcingIntegrable remainderIntegrable equation inside]
  have identity : trajectory 0 + scale * (∫ current in (0 : ℝ)..time,
      Real.exp (-rate * current) * forcing current) +
      (∫ current in (0 : ℝ)..time, Real.exp (-rate * current) * remainder current) - scale * coefficient =
      (trajectory 0 + scale * (∫ current in (0 : ℝ)..time,
        Real.exp (-rate * current) * forcing current) - scale * coefficient) +
        ∫ current in (0 : ℝ)..time, Real.exp (-rate * current) * remainder current := by ring
  rw [identity]
  exact (abs_add _ _).trans ((add_le_add directBound remainderBound).trans_eq (by ring))

end EulerNonuniqueness.Section6
