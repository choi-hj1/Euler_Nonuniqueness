import Mathlib

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness

theorem integral_gronwall_with_forcing {trajectory forcing : ℝ → ℝ}
    {initial rate horizon : ℝ} (trajectoryContinuous : Continuous trajectory)
    (forcingContinuous : Continuous forcing) (rateNonnegative : 0 ≤ rate)
    (horizonNonnegative : 0 ≤ horizon)
    (inequality : ∀ time ∈ Icc 0 horizon, trajectory time ≤ initial +
      ∫ current in (0 : ℝ)..time, forcing current + rate * trajectory current) :
    ∀ time ∈ Icc 0 horizon, trajectory time ≤ Real.exp (rate * time) *
      (initial + ∫ current in (0 : ℝ)..time, Real.exp (-rate * current) * forcing current) := by
  let envelope := fun time => initial + ∫ current in (0 : ℝ)..time,
    forcing current + rate * trajectory current
  let weightedForcing := fun current => Real.exp (-rate * current) * forcing current
  have integrandContinuous : Continuous (fun current => forcing current + rate * trajectory current) :=
    forcingContinuous.add (continuous_const.mul trajectoryContinuous)
  have weightedContinuous : Continuous weightedForcing :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul forcingContinuous
  have envelopeDerivative (time : ℝ) :
      HasDerivAt envelope (forcing time + rate * trajectory time) time := by
    exact (intervalIntegral.integral_hasDerivAt_right (integrandContinuous.intervalIntegrable 0 time)
      integrandContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      integrandContinuous.continuousAt).const_add initial
  have primitiveDerivative (time : ℝ) :
      HasDerivAt (fun other => ∫ current in (0 : ℝ)..other, weightedForcing current)
        (weightedForcing time) time :=
    intervalIntegral.integral_hasDerivAt_right (weightedContinuous.intervalIntegrable 0 time)
      weightedContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter weightedContinuous.continuousAt
  let difference := fun time => Real.exp (-rate * time) * envelope time -
    ∫ current in (0 : ℝ)..time, weightedForcing current
  have differenceDerivative (time : ℝ) : HasDerivAt difference
      (Real.exp (-rate * time) * rate * (trajectory time - envelope time)) time := by
    convert (((((hasDerivAt_id time).const_mul (-rate)).exp).mul
      (envelopeDerivative time)).sub (primitiveDerivative time)) using 1
    dsimp only [weightedForcing, id_eq]
    ring
  have differenceContinuous : Continuous difference :=
    continuous_iff_continuousAt.mpr fun time => (differenceDerivative time).continuousAt
  have decreasing : AntitoneOn difference (Icc 0 horizon) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 horizon) differenceContinuous.continuousOn
      (fun time _ => (differenceDerivative time).differentiableAt.differentiableWithinAt)
    intro time inside
    rw [(differenceDerivative time).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (Real.exp_pos _).le rateNonnegative)
      (sub_nonpos.mpr (inequality time (interior_subset inside)))
  intro time inside
  have bound := decreasing ⟨le_rfl, horizonNonnegative⟩ inside inside.1
  have atZero : difference 0 = initial := by simp [difference, envelope]
  rw [atZero] at bound
  have envelopeBound : envelope time ≤ Real.exp (rate * time) *
      (initial + ∫ current in (0 : ℝ)..time, weightedForcing current) := by
    have positive := Real.exp_pos (rate * time)
    have cancellation : Real.exp (rate * time) * Real.exp (-rate * time) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    have multiplied := mul_le_mul_of_nonneg_left bound positive.le
    dsimp only [difference] at multiplied
    rw [mul_sub, ← mul_assoc, cancellation, one_mul] at multiplied
    nlinarith
  exact (inequality time inside).trans envelopeBound

theorem integral_gronwall_with_forcing_on_Icc {trajectory forcing : ℝ → ℝ}
    {initial rate horizon : ℝ} (trajectoryContinuous : ContinuousOn trajectory (Icc 0 horizon))
    (forcingContinuous : ContinuousOn forcing (Icc 0 horizon)) (rateNonnegative : 0 ≤ rate)
    (horizonNonnegative : 0 ≤ horizon)
    (inequality : ∀ time ∈ Icc 0 horizon, trajectory time ≤ initial +
      ∫ current in (0 : ℝ)..time, forcing current + rate * trajectory current) :
    ∀ time ∈ Icc 0 horizon, trajectory time ≤ Real.exp (rate * time) *
      (initial + ∫ current in (0 : ℝ)..time, Real.exp (-rate * current) * forcing current) := by
  let trajectoryExtended := fun time : ℝ => trajectory (projIcc 0 horizon horizonNonnegative time)
  let forcingExtended := fun time : ℝ => forcing (projIcc 0 horizon horizonNonnegative time)
  have trajectoryEqual (time : ℝ) (inside : time ∈ Icc 0 horizon) : trajectoryExtended time = trajectory time := by
    simp only [trajectoryExtended, projIcc_of_mem horizonNonnegative inside]
  have forcingEqual (time : ℝ) (inside : time ∈ Icc 0 horizon) : forcingExtended time = forcing time := by
    simp only [forcingExtended, projIcc_of_mem horizonNonnegative inside]
  have extendedInequality : ∀ time ∈ Icc 0 horizon, trajectoryExtended time ≤ initial +
      ∫ current in (0 : ℝ)..time, forcingExtended current + rate * trajectoryExtended current := by
    intro time inside
    rw [trajectoryEqual time inside]
    convert inequality time inside using 2
    apply intervalIntegral.integral_congr
    intro current currentInside
    rw [uIcc_of_le inside.1] at currentInside
    change forcingExtended current + rate * trajectoryExtended current = forcing current + rate * trajectory current
    rw [forcingEqual current ⟨currentInside.1, currentInside.2.trans inside.2⟩,
      trajectoryEqual current ⟨currentInside.1, currentInside.2.trans inside.2⟩]
  have bound := integral_gronwall_with_forcing (trajectory := trajectoryExtended) (forcing := forcingExtended)
    (continuousOn_iff_continuous_restrict.mp trajectoryContinuous |>.comp continuous_projIcc)
    (continuousOn_iff_continuous_restrict.mp forcingContinuous |>.comp continuous_projIcc)
    rateNonnegative horizonNonnegative extendedInequality
  intro time inside
  have estimate := bound time inside
  rw [trajectoryEqual time inside] at estimate
  convert estimate using 2
  congr 1
  apply intervalIntegral.integral_congr
  intro current currentInside
  rw [uIcc_of_le inside.1] at currentInside
  change Real.exp (-rate * current) * forcing current = Real.exp (-rate * current) * forcingExtended current
  rw [forcingEqual current ⟨currentInside.1, currentInside.2.trans inside.2⟩]

end EulerNonuniqueness
