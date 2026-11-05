import EulerNonuniqueness.Section5.Delay

open scoped BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.predictedTime_terminal (scales : Scales) (sectionTime : ℝ) (count : ℕ) :
    scales.predictedTime sectionTime count count = 0 := by
  simp [Scales.predictedTime]

theorem Scales.predictedTime_step (scales : Scales) (sectionTime : ℝ)
    {count index : ℕ} (below : index < count) :
    scales.predictedTime sectionTime count index =
      scales.delay sectionTime index + scales.predictedTime sectionTime count (index + 1) := by
  unfold Scales.predictedTime
  exact Finset.sum_eq_sum_Ico_succ_bot below (scales.delay sectionTime)

theorem Scales.predictedTime_strict_step (scales : Scales) (sectionTime : ℝ)
    {count index : ℕ} (below : index < count)
    (positive : 0 < scales.delay sectionTime index) :
    scales.predictedTime sectionTime count (index + 1) <
      scales.predictedTime sectionTime count index := by
  rw [scales.predictedTime_step sectionTime below]
  linarith

theorem Scales.predictedTime_nonneg (scales : Scales) (sectionTime : ℝ)
    {count index : ℕ} (positive : ∀ next, index ≤ next → next < count →
      0 ≤ scales.delay sectionTime next) :
    0 ≤ scales.predictedTime sectionTime count index := by
  apply Finset.sum_nonneg
  intro next membership
  exact positive next (Finset.mem_Ico.mp membership).1 (Finset.mem_Ico.mp membership).2

theorem Scales.predictedTime_one_le_total (scales : Scales) (sectionTime : ℝ)
    (count : ℕ) (positive : ∀ index, 1 ≤ index → 0 ≤ scales.delay sectionTime index)
    (summable : Summable (fun index : ℕ => scales.delay sectionTime (index + 1))) :
    scales.predictedTime sectionTime count 1 ≤
      ∑' index : ℕ, scales.delay sectionTime (index + 1) := by
  have totalBound := summable.sum_le_tsum (Finset.range (count - 1))
    (fun index _ => positive (index + 1) (by omega))
  convert totalBound using 1
  simp only [Scales.predictedTime, Finset.range_eq_Ico]
  rw [Finset.sum_Ico_add' (fun index => scales.delay sectionTime index) 0 (count - 1) 1]
  by_cases countPositive : 1 ≤ count
  · simp [Nat.sub_add_cancel countPositive]
  · have countZero : count = 0 := by omega
    simp [countZero]

theorem Scales.predictedTime_one_lt_quarter (scales : Scales) (sectionTime : ℝ)
    (count : ℕ) (positive : ∀ index, 1 ≤ index → 0 ≤ scales.delay sectionTime index)
    (summable : Summable (fun index : ℕ => scales.delay sectionTime (index + 1)))
    (totalSmall : (∑' index : ℕ, scales.delay sectionTime (index + 1)) < 1 / 4) :
    scales.predictedTime sectionTime count 1 < 1 / 4 :=
  lt_of_le_of_lt (scales.predictedTime_one_le_total sectionTime count positive summable) totalSmall

theorem prescribedCascadePhases_exist (scales : Scales) (orbit : SeparatingOrbit)
    (sectionTime : ℝ) (count : ℕ) :
    ∃ phase dipoleAngle : ℕ → ℝ,
      PrescribedCascadePhases scales orbit sectionTime count phase dipoleAngle := by
  let increment : ℕ → ℝ := fun index =>
    (Real.arctan (1 / Real.sqrt 2) - Real.pi) / 2 +
      orbit.limitingDipoleAngle + sectionTime -
      scales.omega index * scales.delay sectionTime index
  let backward : ℕ → ℝ := fun distance =>
    Nat.rec (0 : ℝ) (fun previous value => increment (count - (previous + 1)) - value) distance
  let dipoleAngle : ℕ → ℝ := fun index => backward (count - index)
  let phase : ℕ → ℝ := fun index =>
    scales.omega index * scales.predictedTime sectionTime count (index + 1) +
      (Real.arctan (1 / Real.sqrt 2) - Real.pi) / 2 - dipoleAngle (index + 1)
  refine ⟨phase, dipoleAngle, ?_⟩
  intro index _ below
  have difference : count - index = (count - (index + 1)) + 1 := by omega
  have recover : count - ((count - (index + 1)) + 1) = index := by omega
  have recursion : dipoleAngle index = increment index - dipoleAngle (index + 1) := by
    dsimp [dipoleAngle]
    rw [difference]
    simp only [backward, Nat.rec_add_one, recover]
  constructor
  · exact ⟨0, by simp [phase]⟩
  · refine ⟨0, ?_⟩
    rw [recursion, scales.predictedTime_step sectionTime below]
    dsimp [increment, phase]
    ring

end EulerNonuniqueness.Paper
