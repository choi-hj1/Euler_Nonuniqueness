import EulerNonuniqueness.General.SaddleHistoryVolterra
import EulerNonuniqueness.General.IntegratedExponentialVolterra

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

theorem saddle_exact_weight_shape_remainder_comparison_on_Icc
    {relative leading remainder : ℝ → ℝ × ℝ} {coefficient additive : ℝ → ℝ}
    {growth finish actionBound : ℝ}
    (growthNonnegative : 0 ≤ growth) (finishNonnegative : 0 ≤ finish)
    (relativeContinuous : ContinuousOn relative (Icc 0 finish))
    (leadingContinuous : ContinuousOn leading (Icc 0 finish))
    (remainderContinuous : ContinuousOn remainder (Icc 0 finish))
    (coefficientContinuous : ContinuousOn coefficient (Icc 0 finish))
    (additiveContinuous : ContinuousOn additive (Icc 0 finish))
    (coefficientNonnegative : ∀ time ∈ Icc 0 finish, 0 ≤ coefficient time)
    (additiveNonnegative : ∀ time ∈ Icc 0 finish, 0 ≤ additive time)
    (unstableHistory : ∀ time ∈ Icc 0 finish,
      Real.exp (-growth * time) * (relative time).1 =
        ∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * (leading current + remainder current).1)
    (stableHistory : ∀ time ∈ Icc 0 finish,
      (relative time).2 = ∫ current in (0 : ℝ)..time,
        Real.exp (-growth * (time - current)) * (leading current + remainder current).2)
    (remainderBound : ∀ time ∈ Ioo 0 finish,
      ‖remainder time‖ ≤ coefficient time * (|(relative time).1| + |(relative time).2|) + additive time)
    (integratedCoefficient : (∫ time in (0 : ℝ)..finish, coefficient time) ≤ actionBound) :
    let shape := fun time => |(relative time).1| + |(relative time).2|
    let drive := fun time => ‖leading time‖ + additive time
    let weightedIntegral := fun function time => ∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * function current
    let error := fun time => 2 * actionBound * Real.exp (2 * actionBound) * weightedIntegral drive time + weightedIntegral additive time
    relative 0 = 0 ∧ IntervalIntegrable coefficient volume 0 finish ∧
    ∀ time ∈ Icc 0 finish,
      IntervalIntegrable (fun current => Real.exp (-growth * current) * shape current) volume 0 time ∧
      IntervalIntegrable (fun current => Real.exp (-growth * current) * drive current) volume 0 time ∧
      IntervalIntegrable (fun current => Real.exp (-growth * current) * ‖remainder current‖) volume 0 time ∧
      IntervalIntegrable (fun current => Real.exp (-growth * current) * additive current) volume 0 time ∧
      IntervalIntegrable (fun current => Real.exp (-growth * current) * (leading current).1) volume 0 time ∧
      Real.exp (-growth * time) * shape time ≤
        2 * Real.exp (2 * ∫ current in (0 : ℝ)..time, coefficient current) * weightedIntegral drive time ∧
      Real.exp (-growth * time) * shape time ≤
        2 * Real.exp (2 * actionBound) * weightedIntegral drive time ∧
      weightedIntegral (fun current => ‖remainder current‖) time ≤ error time ∧
      weightedIntegral (fun current => (leading current).1) time - error time ≤
        Real.exp (-growth * time) * (relative time).1 := by
  let shape := fun time => |(relative time).1| + |(relative time).2|
  let drive := fun time => ‖leading time‖ + additive time
  let weightedIntegral := fun (function : ℝ → ℝ) time => ∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * function current
  let error := fun time => 2 * actionBound * Real.exp (2 * actionBound) * weightedIntegral drive time + weightedIntegral additive time
  have shapeContinuous : ContinuousOn shape (Icc 0 finish) := relativeContinuous.fst.abs.add relativeContinuous.snd.abs
  have driveContinuous : ContinuousOn drive (Icc 0 finish) := leadingContinuous.norm.add additiveContinuous
  have driveNonnegative (time : ℝ) (inside : time ∈ Icc 0 finish) : 0 ≤ drive time :=
    add_nonneg (norm_nonneg _) (additiveNonnegative time inside)
  have coefficientIntegrable := coefficientContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have normHistory := saddle_history_norm_volterra growthNonnegative finishNonnegative relativeContinuous
    leadingContinuous remainderContinuous unstableHistory stableHistory
  have integrandContinuous : ContinuousOn (fun time => drive time + coefficient time * shape time) (Icc 0 finish) :=
    driveContinuous.add (coefficientContinuous.mul shapeContinuous)
  have volterra (time : ℝ) (inside : time ∈ Icc 0 finish) :
      shape time ≤ (0 : ℝ) * Real.exp (growth * time) +
        2 * ∫ current in (0 : ℝ)..time, Real.exp (growth * (time - current)) *
          (drive current + coefficient current * shape current) := by
    have subset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
    have kernel : Continuous (fun current : ℝ => Real.exp (growth * (time - current))) := by fun_prop
    have targetIntegrable := (kernel.continuousOn.mul (integrandContinuous.mono subset)).intervalIntegrable_of_Icc (μ := volume) inside.1
    have comparison := intervalIntegral.integral_mono_on_of_le_Ioo inside.1 (normHistory.2 time inside).2.1 targetIntegrable (by
      intro current member
      have bound := add_le_add_left (remainderBound current ⟨member.1, member.2.trans_le inside.2⟩) ‖leading current‖
      have identity : ‖leading current‖ + (coefficient current * shape current + additive current) =
          drive current + coefficient current * shape current := by dsimp only [drive]; ring
      exact mul_le_mul_of_nonneg_left (bound.trans_eq identity) (Real.exp_pos _).le)
    simpa only [zero_mul, zero_add] using (normHistory.2 time inside).2.2.trans
      (mul_le_mul_of_nonneg_left comparison (by norm_num : (0 : ℝ) ≤ 2))
  have gronwall := exponential_volterra_of_integrated_coefficient_on_Icc shapeContinuous driveContinuous coefficientContinuous
    finishNonnegative (by norm_num : (0 : ℝ) ≤ 2) driveNonnegative coefficientNonnegative volterra
  have exponential : Continuous (fun current : ℝ => Real.exp (-growth * current)) := by fun_prop
  have coefficientPrefix (time : ℝ) (inside : time ∈ Icc 0 finish) :
      (∫ current in (0 : ℝ)..time, coefficient current) ≤ actionBound := by
    apply LE.le.trans _ integratedCoefficient
    apply intervalIntegral.integral_mono_interval le_rfl inside.1 inside.2
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with current member
      exact coefficientNonnegative current ⟨member.1.le, member.2⟩
    · exact coefficientIntegrable
  have prefixUpper (time : ℝ) (inside : time ∈ Icc 0 finish) :
      Real.exp (-growth * time) * shape time ≤
        2 * Real.exp (2 * ∫ current in (0 : ℝ)..time, coefficient current) * weightedIntegral drive time := by
    have bound := gronwall time inside
    simpa only [zero_add, weightedIntegral, mul_left_comm, mul_assoc] using bound
  have uniformUpper (time : ℝ) (inside : time ∈ Icc 0 finish) :
      Real.exp (-growth * time) * shape time ≤ 2 * Real.exp (2 * actionBound) * weightedIntegral drive time := by
    have driveIntegralNonnegative : 0 ≤ weightedIntegral drive time :=
      intervalIntegral.integral_nonneg inside.1 (fun current member => mul_nonneg (Real.exp_pos _).le
        (driveNonnegative current ⟨member.1, member.2.trans inside.2⟩))
    have exponentBound := mul_le_mul_of_nonneg_left (coefficientPrefix time inside) (by norm_num : (0 : ℝ) ≤ 2)
    exact (prefixUpper time inside).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr exponentBound) (by norm_num : (0 : ℝ) ≤ 2)) driveIntegralNonnegative)
  refine ⟨normHistory.1, coefficientIntegrable, ?_⟩
  intro time inside
  have subset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
  have shapeIntegrable := (exponential.continuousOn.mul (shapeContinuous.mono subset)).intervalIntegrable_of_Icc (μ := volume) inside.1
  have driveIntegrable := (exponential.continuousOn.mul (driveContinuous.mono subset)).intervalIntegrable_of_Icc (μ := volume) inside.1
  have remainderIntegrable := (exponential.continuousOn.mul (remainderContinuous.norm.mono subset)).intervalIntegrable_of_Icc (μ := volume) inside.1
  have additiveIntegrable := (exponential.continuousOn.mul (additiveContinuous.mono subset)).intervalIntegrable_of_Icc (μ := volume) inside.1
  have leadingIntegrable := (exponential.continuousOn.mul (leadingContinuous.fst.mono subset)).intervalIntegrable_of_Icc (μ := volume) inside.1
  have signedRemainderIntegrable := (exponential.continuousOn.mul (remainderContinuous.fst.mono subset)).intervalIntegrable_of_Icc (μ := volume) inside.1
  let driveMass := weightedIntegral drive time
  let shapeBound := 2 * Real.exp (2 * actionBound) * driveMass
  have driveMassNonnegative : 0 ≤ driveMass :=
    intervalIntegral.integral_nonneg inside.1 (fun current member => mul_nonneg (Real.exp_pos _).le
      (driveNonnegative current (subset member)))
  have shapeBoundNonnegative : 0 ≤ shapeBound := mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) driveMassNonnegative
  have uniformShape (current : ℝ) (member : current ∈ Icc 0 time) :
      Real.exp (-growth * current) * shape current ≤ shapeBound := by
    have drivePrefix : weightedIntegral drive current ≤ driveMass := by
      apply intervalIntegral.integral_mono_interval le_rfl member.1 member.2
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with earlier earlierInside
        exact mul_nonneg (Real.exp_pos _).le (driveNonnegative earlier ⟨earlierInside.1.le, earlierInside.2.trans inside.2⟩)
      · exact driveIntegrable
    exact (uniformUpper current (subset member)).trans
      (mul_le_mul_of_nonneg_left drivePrefix (mul_nonneg (by norm_num) (Real.exp_pos _).le))
  let feedback := fun current => coefficient current * (Real.exp (-growth * current) * shape current)
  have feedbackContinuous : ContinuousOn feedback (Icc 0 finish) :=
    coefficientContinuous.mul (exponential.continuousOn.mul shapeContinuous)
  have feedbackIntegrable := (feedbackContinuous.mono subset).intervalIntegrable_of_Icc (μ := volume) inside.1
  have remainderComparison := intervalIntegral.integral_mono_on_of_le_Ioo inside.1 remainderIntegrable
    (feedbackIntegrable.add additiveIntegrable) (by
      intro current member
      have actual := mul_le_mul_of_nonneg_left
        (remainderBound current ⟨member.1, member.2.trans_le inside.2⟩) (Real.exp_pos (-growth * current)).le
      have identity : Real.exp (-growth * current) * (coefficient current * shape current + additive current) =
          feedback current + Real.exp (-growth * current) * additive current := by dsimp only [feedback]; ring
      exact actual.trans_eq identity)
  rw [intervalIntegral.integral_add feedbackIntegrable additiveIntegrable] at remainderComparison
  have feedbackComparison := intervalIntegral.integral_mono_on inside.1 feedbackIntegrable
    (((coefficientContinuous.mono subset).mul continuousOn_const).intervalIntegrable_of_Icc (μ := volume) inside.1)
    (fun current member => mul_le_mul_of_nonneg_left (uniformShape current member) (coefficientNonnegative current (subset member)))
  have feedbackBound : (∫ current in (0 : ℝ)..time, feedback current) ≤ shapeBound * actionBound := by
    apply feedbackComparison.trans
    calc
      (∫ current in (0 : ℝ)..time, coefficient current * shapeBound) = shapeBound * ∫ current in (0 : ℝ)..time, coefficient current := by
        simp_rw [mul_comm (coefficient _) shapeBound]
        exact intervalIntegral.integral_const_mul _ _
      _ ≤ shapeBound * actionBound := mul_le_mul_of_nonneg_left (coefficientPrefix time inside) shapeBoundNonnegative
  have errorBound : weightedIntegral (fun current => ‖remainder current‖) time ≤ error time := by
    apply remainderComparison.trans
    have bound := add_le_add_right feedbackBound (weightedIntegral additive time)
    convert bound using 1
    dsimp only [error, shapeBound, driveMass]
    ring
  have signedRemainderLower : -(weightedIntegral (fun current => ‖remainder current‖) time) ≤
      weightedIntegral (fun current => (remainder current).1) time := by
    have comparison := intervalIntegral.integral_mono_on inside.1 remainderIntegrable.neg signedRemainderIntegrable (by
      intro current _
      have projection : |(remainder current).1| ≤ ‖remainder current‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le (remainder current)
      simpa only [mul_neg] using mul_le_mul_of_nonneg_left ((neg_le_neg projection).trans (neg_abs_le _)) (Real.exp_pos (-growth * current)).le)
    change (∫ current in (0 : ℝ)..time, -(Real.exp (-growth * current) * ‖remainder current‖)) ≤
      (∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * (remainder current).1) at comparison
    simpa only [intervalIntegral.integral_neg] using comparison
  have signedHistory : Real.exp (-growth * time) * (relative time).1 =
      weightedIntegral (fun current => (leading current).1) time + weightedIntegral (fun current => (remainder current).1) time := by
    rw [unstableHistory time inside, ← intervalIntegral.integral_add leadingIntegrable signedRemainderIntegrable]
    apply intervalIntegral.integral_congr
    intro current _
    simp only [Prod.fst_add, mul_add]
  have signedLower : weightedIntegral (fun current => (leading current).1) time - error time ≤ Real.exp (-growth * time) * (relative time).1 := by
    rw [signedHistory]
    linarith only [errorBound, signedRemainderLower]
  exact ⟨shapeIntegrable, driveIntegrable, remainderIntegrable, additiveIntegrable, leadingIntegrable,
    prefixUpper time inside, uniformUpper time inside, errorBound, signedLower⟩

end EulerNonuniqueness.General
