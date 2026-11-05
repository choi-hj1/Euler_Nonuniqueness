import EulerNonuniqueness.Section6.FollowerConvolution

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace EulerNonuniqueness.Section6

def finiteFollowerEnvelope {Index : Type*} [Fintype Index] [Nonempty Index]
    (states : Index → ℝ → ℝ) (time : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun index => states index time)

theorem continuousOn_finiteFollowerEnvelope {Index : Type*} [Fintype Index] [Nonempty Index]
    {states : Index → ℝ → ℝ} {horizon : ℝ}
    (continuous : ∀ index, ContinuousOn (states index) (Icc 0 horizon)) :
    ContinuousOn (finiteFollowerEnvelope states) (Icc 0 horizon) :=
  ContinuousOn.finset_sup'_apply Finset.univ_nonempty (fun index _ => continuous index)

theorem finite_follower_row_le {Index : Type*} [Fintype Index] [Nonempty Index]
    {states coefficients : Index → ℝ} {coupling : ℝ}
    (statesNonnegative : ∀ index, 0 ≤ states index)
    (coefficientsNonnegative : ∀ index, 0 ≤ coefficients index)
    (rowBound : ∑ index, coefficients index ≤ coupling) :
    ∑ index, coefficients index * states index ≤
      coupling * Finset.univ.sup' Finset.univ_nonempty states := by
  have stateBound (index : Index) : states index ≤ Finset.univ.sup' Finset.univ_nonempty states :=
    Finset.le_sup' states (Finset.mem_univ index)
  have envelopeNonnegative : 0 ≤ Finset.univ.sup' Finset.univ_nonempty states := by
    obtain ⟨index⟩ := ‹Nonempty Index›
    exact (statesNonnegative index).trans (stateBound index)
  calc
    _ ≤ ∑ index, coefficients index * Finset.univ.sup' Finset.univ_nonempty states :=
      Finset.sum_le_sum fun index _ => mul_le_mul_of_nonneg_left (stateBound index) (coefficientsNonnegative index)
    _ = (∑ index, coefficients index) * Finset.univ.sup' Finset.univ_nonempty states := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right rowBound envelopeNonnegative

theorem finite_follower_envelope_inequality {Index : Type*} [Fintype Index] [Nonempty Index]
    {states inputs : Index → ℝ → ℝ} {coefficients : Index → Index → ℝ → ℝ}
    {source target : ℝ → ℝ} {initial growth coupling multiplier horizon : ℝ}
    (statesContinuous : ∀ index, ContinuousOn (states index) (Icc 0 horizon))
    (inputsContinuous : ∀ index, ContinuousOn (inputs index) (Icc 0 horizon))
    (sourceContinuous : ContinuousOn source (Icc 0 horizon))
    (targetContinuous : ContinuousOn target (Icc 0 horizon))
    (statesNonnegative : ∀ index time, time ∈ Icc 0 horizon → 0 ≤ states index time)
    (coefficientsNonnegative : ∀ index other time, time ∈ Icc 0 horizon → 0 ≤ coefficients index other time)
    (rowBound : ∀ index time, time ∈ Icc 0 horizon → ∑ other, coefficients index other time ≤ coupling)
    (inputBound : ∀ index time, time ∈ Icc 0 horizon → inputs index time ≤
      source time + coupling * target time + ∑ other, coefficients index other time * states other time)
    (multiplierNonnegative : 0 ≤ multiplier)
    (propagator : ∀ index time, time ∈ Icc 0 horizon → states index time ≤
      multiplier * Real.exp (growth * time) * initial + multiplier *
        ∫ current in (0 : ℝ)..time, Real.exp (growth * (time - current)) * inputs index current) :
    ∀ time ∈ Icc 0 horizon, finiteFollowerEnvelope states time ≤
      multiplier * Real.exp (growth * time) * initial + multiplier *
        ∫ current in (0 : ℝ)..time, Real.exp (growth * (time - current)) *
          (source current + coupling * target current + coupling * finiteFollowerEnvelope states current) := by
  have envelopeContinuous := continuousOn_finiteFollowerEnvelope statesContinuous
  intro time inside
  apply Finset.sup'_le
  intro index _
  apply (propagator index time inside).trans
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_left _ multiplierNonnegative
  have intervalInside : uIcc (0 : ℝ) time ⊆ Icc 0 horizon := by
    rw [uIcc_of_le inside.1]
    exact Icc_subset_Icc le_rfl inside.2
  have kernelContinuous : ContinuousOn (fun current => Real.exp (growth * (time - current))) (uIcc 0 time) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn
  apply intervalIntegral.integral_mono_on inside.1
    ((kernelContinuous.mul ((inputsContinuous index).mono intervalInside)).intervalIntegrable)
    ((kernelContinuous.mul (((sourceContinuous.add (continuousOn_const.mul targetContinuous)).add
      (continuousOn_const.mul envelopeContinuous)).mono intervalInside)).intervalIntegrable)
  intro current currentInside
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have currentInside' : current ∈ Icc 0 horizon := ⟨currentInside.1, currentInside.2.trans inside.2⟩
  exact (inputBound index current currentInside').trans (add_le_add_left
    (finite_follower_row_le (fun other => statesNonnegative other current currentInside')
      (fun other => coefficientsNonnegative index other current currentInside')
      (rowBound index current currentInside')) _)

end EulerNonuniqueness.Section6
