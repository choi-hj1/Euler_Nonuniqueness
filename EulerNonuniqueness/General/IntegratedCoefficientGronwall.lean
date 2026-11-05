import Mathlib

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.General

private theorem integral_gronwall_of_integrated_coefficient
    {trajectory forcing coefficient : ℝ → ℝ} {initial horizon : ℝ}
    (trajectoryContinuous : Continuous trajectory) (forcingContinuous : Continuous forcing)
    (coefficientContinuous : Continuous coefficient) (horizonNonnegative : 0 ≤ horizon)
    (forcingNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ forcing time)
    (coefficientNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ coefficient time)
    (inequality : ∀ time ∈ Icc 0 horizon, trajectory time ≤ initial +
      ∫ current in (0 : ℝ)..time, forcing current + coefficient current * trajectory current) :
    ∀ time ∈ Icc 0 horizon, trajectory time ≤
      Real.exp (∫ current in (0 : ℝ)..time, coefficient current) *
        (initial + ∫ current in (0 : ℝ)..time, forcing current) := by
  let accumulation := fun time => ∫ current in (0 : ℝ)..time, coefficient current
  let envelope := fun time => initial +
    ∫ current in (0 : ℝ)..time, forcing current + coefficient current * trajectory current
  have integrandContinuous : Continuous (fun current => forcing current + coefficient current * trajectory current) :=
    forcingContinuous.add (coefficientContinuous.mul trajectoryContinuous)
  have accumulationDerivative (time : ℝ) : HasDerivAt accumulation (coefficient time) time :=
    intervalIntegral.integral_hasDerivAt_right (coefficientContinuous.intervalIntegrable 0 time)
      coefficientContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter coefficientContinuous.continuousAt
  have envelopeDerivative (time : ℝ) :
      HasDerivAt envelope (forcing time + coefficient time * trajectory time) time :=
    (intervalIntegral.integral_hasDerivAt_right (integrandContinuous.intervalIntegrable 0 time)
      integrandContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter integrandContinuous.continuousAt).const_add initial
  have forcingDerivative (time : ℝ) :
      HasDerivAt (fun other => ∫ current in (0 : ℝ)..other, forcing current) (forcing time) time :=
    intervalIntegral.integral_hasDerivAt_right (forcingContinuous.intervalIntegrable 0 time)
      forcingContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter forcingContinuous.continuousAt
  let difference := fun time => Real.exp (-accumulation time) * envelope time -
    ∫ current in (0 : ℝ)..time, forcing current
  have differenceDerivative (time : ℝ) : HasDerivAt difference
      ((Real.exp (-accumulation time) * forcing time - forcing time) +
        Real.exp (-accumulation time) * coefficient time * (trajectory time - envelope time)) time := by
    convert ((((accumulationDerivative time).neg.exp).mul (envelopeDerivative time)).sub
      (forcingDerivative time)) using 1
    ring
  have differenceContinuous : Continuous difference :=
    continuous_iff_continuousAt.mpr fun time => (differenceDerivative time).continuousAt
  have decreasing : AntitoneOn difference (Icc 0 horizon) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 horizon) differenceContinuous.continuousOn
      (fun time _ => (differenceDerivative time).differentiableAt.differentiableWithinAt)
    intro time inside
    have member : time ∈ Icc (0 : ℝ) horizon := interior_subset inside
    have accumulationNonnegative : 0 ≤ accumulation time :=
      intervalIntegral.integral_nonneg member.1 (fun current currentInside =>
        coefficientNonnegative current ⟨currentInside.1, currentInside.2.trans member.2⟩)
    have exponentialBound : Real.exp (-accumulation time) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr accumulationNonnegative)
    have forcingBound : Real.exp (-accumulation time) * forcing time - forcing time ≤ 0 :=
      sub_nonpos.mpr (mul_le_of_le_one_left (forcingNonnegative time member) exponentialBound)
    have feedbackBound : Real.exp (-accumulation time) * coefficient time *
        (trajectory time - envelope time) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (Real.exp_pos _).le (coefficientNonnegative time member))
        (sub_nonpos.mpr (inequality time member))
    rw [(differenceDerivative time).deriv]
    exact add_nonpos forcingBound feedbackBound
  intro time inside
  have bound := decreasing ⟨le_rfl, horizonNonnegative⟩ inside inside.1
  have initialDifference : difference 0 = initial := by simp [difference, accumulation, envelope]
  rw [initialDifference] at bound
  have cancellation : Real.exp (accumulation time) * Real.exp (-accumulation time) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have multiplied := mul_le_mul_of_nonneg_left bound (Real.exp_pos (accumulation time)).le
  dsimp only [difference] at multiplied
  rw [mul_sub, ← mul_assoc, cancellation, one_mul] at multiplied
  apply (inequality time inside).trans
  change envelope time ≤ Real.exp (accumulation time) *
    (initial + ∫ current in (0 : ℝ)..time, forcing current)
  linarith only [multiplied]

theorem integral_gronwall_of_integrated_coefficient_on_Icc
    {trajectory forcing coefficient : ℝ → ℝ} {initial horizon : ℝ}
    (trajectoryContinuous : ContinuousOn trajectory (Icc 0 horizon))
    (forcingContinuous : ContinuousOn forcing (Icc 0 horizon))
    (coefficientContinuous : ContinuousOn coefficient (Icc 0 horizon))
    (horizonNonnegative : 0 ≤ horizon)
    (forcingNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ forcing time)
    (coefficientNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ coefficient time)
    (inequality : ∀ time ∈ Icc 0 horizon, trajectory time ≤ initial +
      ∫ current in (0 : ℝ)..time, forcing current + coefficient current * trajectory current) :
    ∀ time ∈ Icc 0 horizon, trajectory time ≤
      Real.exp (∫ current in (0 : ℝ)..time, coefficient current) *
        (initial + ∫ current in (0 : ℝ)..time, forcing current) := by
  let extended := fun function : ℝ → ℝ => fun time => function (projIcc 0 horizon horizonNonnegative time)
  have agreement (function : ℝ → ℝ) (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      extended function time = function time := by
    simp only [extended, projIcc_of_mem horizonNonnegative inside]
  have extensionContinuous (function : ℝ → ℝ) (regular : ContinuousOn function (Icc 0 horizon)) :
      Continuous (extended function) :=
    continuousOn_iff_continuous_restrict.mp regular |>.comp continuous_projIcc
  have integralAgreement (function : ℝ → ℝ) (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      (∫ current in (0 : ℝ)..time, extended function current) = ∫ current in (0 : ℝ)..time, function current := by
    apply intervalIntegral.integral_congr
    intro current currentInside
    rw [uIcc_of_le inside.1] at currentInside
    exact agreement function current ⟨currentInside.1, currentInside.2.trans inside.2⟩
  have extendedInequality : ∀ time ∈ Icc 0 horizon, extended trajectory time ≤ initial +
      ∫ current in (0 : ℝ)..time, extended forcing current + extended coefficient current * extended trajectory current := by
    intro time inside
    rw [agreement trajectory time inside]
    convert inequality time inside using 2
    apply intervalIntegral.integral_congr
    intro current currentInside
    rw [uIcc_of_le inside.1] at currentInside
    have member : current ∈ Icc (0 : ℝ) horizon := ⟨currentInside.1, currentInside.2.trans inside.2⟩
    change extended forcing current + extended coefficient current * extended trajectory current =
      forcing current + coefficient current * trajectory current
    rw [agreement forcing current member, agreement coefficient current member, agreement trajectory current member]
  have bound := integral_gronwall_of_integrated_coefficient
    (extensionContinuous trajectory trajectoryContinuous) (extensionContinuous forcing forcingContinuous)
    (extensionContinuous coefficient coefficientContinuous) horizonNonnegative
    (fun time inside => by rw [agreement forcing time inside]; exact forcingNonnegative time inside)
    (fun time inside => by rw [agreement coefficient time inside]; exact coefficientNonnegative time inside)
    extendedInequality
  intro time inside
  simpa only [agreement trajectory time inside, integralAgreement coefficient time inside,
    integralAgreement forcing time inside] using bound time inside

end EulerNonuniqueness.General
