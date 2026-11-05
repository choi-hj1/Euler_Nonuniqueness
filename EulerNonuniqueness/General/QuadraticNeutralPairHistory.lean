import EulerNonuniqueness.General.ZeroGeneratorPairHistory
import EulerNonuniqueness.General.IntegralGronwall

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

def weightedBoundaryPairDistance (weight : ℝ)
    (firstTransverse finalTransverse firstNeutral finalNeutral : Space) : ℝ :=
  ‖finalTransverse - firstTransverse‖ + weight * ‖finalNeutral - firstNeutral‖

theorem quadraticNeutral_pair_history_of_interior
    (group : ℝ → Space →L[ℝ] Space) (generator : Space →L[ℝ] Space)
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first final : ℝ, group (first + final) = (group first).comp (group final))
    (groupDerivative : ∀ time : ℝ, HasDerivAt group ((group time).comp generator) time)
    {groupBound : ℝ} (groupBoundOne : 1 ≤ groupBound)
    (groupBounded : ∀ time : ℝ, ∀ value : Space, ‖group time value‖ ≤ groupBound * ‖value‖)
    {firstTransverse finalTransverse firstNeutral finalNeutral : ℝ → Space}
    {firstTransverseForcing finalTransverseForcing firstNeutralForcing finalNeutralForcing : ℝ → Space}
    {source : ℝ → ℝ} {weight rate horizon : ℝ}
    (weightNonnegative : 0 ≤ weight) (rateNonnegative : 0 ≤ rate) (horizonNonnegative : 0 ≤ horizon)
    (firstTransverseContinuous : ContinuousOn firstTransverse (Icc 0 horizon))
    (finalTransverseContinuous : ContinuousOn finalTransverse (Icc 0 horizon))
    (firstNeutralContinuous : ContinuousOn firstNeutral (Icc 0 horizon))
    (finalNeutralContinuous : ContinuousOn finalNeutral (Icc 0 horizon))
    (firstTransverseForcingContinuous : ContinuousOn firstTransverseForcing (Icc 0 horizon))
    (finalTransverseForcingContinuous : ContinuousOn finalTransverseForcing (Icc 0 horizon))
    (firstNeutralForcingContinuous : ContinuousOn firstNeutralForcing (Icc 0 horizon))
    (finalNeutralForcingContinuous : ContinuousOn finalNeutralForcing (Icc 0 horizon))
    (sourceContinuous : ContinuousOn source (Icc 0 horizon))
    (firstTransverseEquation : ∀ time ∈ Ioo 0 horizon,
      HasDerivAt firstTransverse (generator (firstTransverse time) + firstTransverseForcing time) time)
    (finalTransverseEquation : ∀ time ∈ Ioo 0 horizon,
      HasDerivAt finalTransverse (generator (finalTransverse time) + finalTransverseForcing time) time)
    (firstNeutralEquation : ∀ time ∈ Ioo 0 horizon, HasDerivAt firstNeutral (firstNeutralForcing time) time)
    (finalNeutralEquation : ∀ time ∈ Ioo 0 horizon, HasDerivAt finalNeutral (finalNeutralForcing time) time)
    (forcingBound : ∀ time ∈ Ioo 0 horizon,
      ‖finalTransverseForcing time - firstTransverseForcing time‖ +
        weight * ‖finalNeutralForcing time - firstNeutralForcing time‖ ≤
      rate * weightedBoundaryPairDistance weight (firstTransverse time) (finalTransverse time)
        (firstNeutral time) (finalNeutral time) + source time) :
    ∀ time ∈ Icc 0 horizon,
      weightedBoundaryPairDistance weight (firstTransverse time) (finalTransverse time)
          (firstNeutral time) (finalNeutral time) ≤
        groupBound * weightedBoundaryPairDistance weight (firstTransverse 0) (finalTransverse 0)
          (firstNeutral 0) (finalNeutral 0) +
        ∫ current in (0 : ℝ)..time, groupBound * source current + groupBound * rate *
          weightedBoundaryPairDistance weight (firstTransverse current) (finalTransverse current)
            (firstNeutral current) (finalNeutral current) ∧
      weightedBoundaryPairDistance weight (firstTransverse time) (finalTransverse time)
          (firstNeutral time) (finalNeutral time) ≤ Real.exp (groupBound * rate * time) *
        (groupBound * weightedBoundaryPairDistance weight (firstTransverse 0) (finalTransverse 0)
          (firstNeutral 0) (finalNeutral 0) +
        ∫ current in (0 : ℝ)..time, Real.exp (-(groupBound * rate) * current) * (groupBound * source current)) := by
  have groupNonnegative : 0 ≤ groupBound := by linarith
  have transverseHistory := linearGroup_pair_history_of_interior group generator atZero addition groupDerivative
    groupNonnegative groupBounded horizonNonnegative firstTransverseContinuous finalTransverseContinuous
    firstTransverseForcingContinuous finalTransverseForcingContinuous firstTransverseEquation finalTransverseEquation
  have neutralHistory := zeroGenerator_pair_history_of_interior horizonNonnegative firstNeutralContinuous finalNeutralContinuous
    firstNeutralForcingContinuous finalNeutralForcingContinuous firstNeutralEquation finalNeutralEquation
  let distance := fun time => weightedBoundaryPairDistance weight (firstTransverse time) (finalTransverse time)
    (firstNeutral time) (finalNeutral time)
  let forcing := fun time => ‖finalTransverseForcing time - firstTransverseForcing time‖ +
    weight * ‖finalNeutralForcing time - firstNeutralForcing time‖
  have distanceContinuous : ContinuousOn distance (Icc 0 horizon) :=
    (finalTransverseContinuous.sub firstTransverseContinuous).norm.add
      (continuousOn_const.mul (finalNeutralContinuous.sub firstNeutralContinuous).norm)
  have forcingContinuous : ContinuousOn forcing (Icc 0 horizon) :=
    (finalTransverseForcingContinuous.sub firstTransverseForcingContinuous).norm.add
      (continuousOn_const.mul (finalNeutralForcingContinuous.sub firstNeutralForcingContinuous).norm)
  have sourceAndRateContinuous : ContinuousOn (fun current => groupBound * source current + groupBound * rate * distance current)
      (Icc 0 horizon) := (continuousOn_const.mul sourceContinuous).add (continuousOn_const.mul distanceContinuous)
  have history (time : ℝ) (inside : time ∈ Icc 0 horizon) : distance time ≤ groupBound * distance 0 +
      ∫ current in (0 : ℝ)..time, groupBound * source current + groupBound * rate * distance current := by
    have subset : Icc 0 time ⊆ Icc 0 horizon := fun current currentInside => ⟨currentInside.1, currentInside.2.trans inside.2⟩
    have transverseForcingIntegrable := ((finalTransverseForcingContinuous.sub firstTransverseForcingContinuous).mono subset).norm.intervalIntegrable_of_Icc (μ := volume) inside.1
    have neutralForcingIntegrable := ((finalNeutralForcingContinuous.sub firstNeutralForcingContinuous).mono subset).norm.intervalIntegrable_of_Icc (μ := volume) inside.1
    have forcingIntegrable := (forcingContinuous.mono subset).intervalIntegrable_of_Icc (μ := volume) inside.1
    have targetIntegrable := (sourceAndRateContinuous.mono subset).intervalIntegrable_of_Icc (μ := volume) inside.1
    have neutralEnvelopeNonnegative : 0 ≤ ‖finalNeutral 0 - firstNeutral 0‖ +
        ∫ current in (0 : ℝ)..time, ‖finalNeutralForcing current - firstNeutralForcing current‖ :=
      add_nonneg (norm_nonneg _) (intervalIntegral.integral_nonneg_of_forall inside.1 (fun current => norm_nonneg _))
    have neutralBound := (neutralHistory time inside).2.trans
      (le_mul_of_one_le_left neutralEnvelopeNonnegative groupBoundOne)
    have combined := add_le_add (transverseHistory time inside).2
      (mul_le_mul_of_nonneg_left neutralBound weightNonnegative)
    have regrouped : distance time ≤ groupBound * distance 0 +
        ∫ current in (0 : ℝ)..time, groupBound * forcing current := by
      dsimp only [distance, weightedBoundaryPairDistance] at combined ⊢
      rw [intervalIntegral.integral_const_mul, show
        (∫ current in (0 : ℝ)..time, forcing current) =
        (∫ current in (0 : ℝ)..time, ‖finalTransverseForcing current - firstTransverseForcing current‖) +
          weight * (∫ current in (0 : ℝ)..time, ‖finalNeutralForcing current - firstNeutralForcing current‖) from by
        dsimp only [forcing]
        rw [intervalIntegral.integral_add transverseForcingIntegrable (neutralForcingIntegrable.const_mul weight),
          intervalIntegral.integral_const_mul]]
      nlinarith only [combined]
    have integralBound := intervalIntegral.integral_mono_on_of_le_Ioo inside.1
      (forcingIntegrable.const_mul groupBound) targetIntegrable (fun current currentInside => by
        have actual := mul_le_mul_of_nonneg_left (forcingBound current ⟨currentInside.1, currentInside.2.trans_le inside.2⟩) groupNonnegative
        dsimp only [forcing, distance] at actual ⊢
        nlinarith only [actual])
    exact regrouped.trans (add_le_add_left integralBound _)
  have gronwall := EulerNonuniqueness.integral_gronwall_with_forcing_on_Icc
    distanceContinuous (continuousOn_const.mul sourceContinuous) (mul_nonneg groupNonnegative rateNonnegative)
    horizonNonnegative history
  intro time inside
  exact ⟨history time inside, gronwall time inside⟩

end EulerNonuniqueness.General
