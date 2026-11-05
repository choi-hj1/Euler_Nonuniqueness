import EulerNonuniqueness.General.InteriorDerivativeIntegralMajorant
import EulerNonuniqueness.General.QuadraticNeutralPairHistory

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem quadraticNeutral_pair_history_without_forcing_continuity
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
    (sourceContinuous : ContinuousOn source (Icc 0 horizon))
    (sourceNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ source time)
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
        (groupBound + 1) * groupBound * weightedBoundaryPairDistance weight (firstTransverse 0) (finalTransverse 0)
          (firstNeutral 0) (finalNeutral 0) +
        ∫ current in (0 : ℝ)..time, (groupBound + 1) * groupBound * source current +
          (groupBound + 1) * groupBound * rate *
            weightedBoundaryPairDistance weight (firstTransverse current) (finalTransverse current)
              (firstNeutral current) (finalNeutral current) ∧
      weightedBoundaryPairDistance weight (firstTransverse time) (finalTransverse time)
          (firstNeutral time) (finalNeutral time) ≤
        Real.exp ((groupBound + 1) * groupBound * rate * time) *
          ((groupBound + 1) * groupBound * weightedBoundaryPairDistance weight (firstTransverse 0) (finalTransverse 0)
            (firstNeutral 0) (finalNeutral 0) +
            ∫ current in (0 : ℝ)..time, Real.exp (-((groupBound + 1) * groupBound * rate) * current) *
              ((groupBound + 1) * groupBound * source current)) := by
  have groupNonnegative : 0 ≤ groupBound := zero_le_one.trans groupBoundOne
  have enlargedNonnegative : 0 ≤ groupBound + 1 := by linarith
  let distance := fun time => weightedBoundaryPairDistance weight (firstTransverse time) (finalTransverse time)
    (firstNeutral time) (finalNeutral time)
  let curve := fun time => (group (-time) (finalTransverse time - firstTransverse time),
    weight • (finalNeutral time - firstNeutral time))
  let derivative := fun time => (group (-time) (finalTransverseForcing time - firstTransverseForcing time),
    weight • (finalNeutralForcing time - firstNeutralForcing time))
  let majorant := fun time => groupBound * (rate * distance time + source time)
  have distanceNonnegative (time : ℝ) : 0 ≤ distance time := by
    dsimp only [distance, weightedBoundaryPairDistance]
    positivity
  have distanceContinuous : ContinuousOn distance (Icc 0 horizon) :=
    (finalTransverseContinuous.sub firstTransverseContinuous).norm.add
      (continuousOn_const.mul (finalNeutralContinuous.sub firstNeutralContinuous).norm)
  have groupContinuous : Continuous group :=
    continuous_iff_continuousAt.mpr fun time => (groupDerivative time).continuousAt
  have curveContinuous : ContinuousOn curve (Icc 0 horizon) :=
    (((groupContinuous.comp continuous_neg).continuousOn).clm_apply
      (finalTransverseContinuous.sub firstTransverseContinuous)).prodMk
        ((finalNeutralContinuous.sub firstNeutralContinuous).const_smul weight)
  have majorantContinuous : ContinuousOn majorant (Icc 0 horizon) :=
    continuousOn_const.mul ((continuousOn_const.mul distanceContinuous).add sourceContinuous)
  have equation (time : ℝ) (inside : time ∈ Ioo 0 horizon) : HasDerivAt curve (derivative time) time := by
    have inverseDerivative : HasDerivAt (fun current => group (-current)) (-((group (-time)).comp generator)) time := by
      simpa only [neg_one_smul] using (groupDerivative (-time)).scomp time ((hasDerivAt_id time).neg)
    have raw := (finalTransverseEquation time inside).sub (firstTransverseEquation time inside)
    have first := inverseDerivative.clm_apply raw
    have firstEquation : HasDerivAt (fun current => group (-current) (finalTransverse current - firstTransverse current))
        (group (-time) (finalTransverseForcing time - firstTransverseForcing time)) time := by
      convert first using 1
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply, map_add, map_sub]
      abel
    exact firstEquation.prodMk (((finalNeutralEquation time inside).sub (firstNeutralEquation time inside)).const_smul weight)
  have derivativeBound (time : ℝ) (inside : time ∈ Ioo 0 horizon) : ‖derivative time‖ ≤ majorant time := by
    have raw := forcingBound time inside
    have firstBound := (groupBounded (-time) (finalTransverseForcing time - firstTransverseForcing time)).trans
      (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_right (mul_nonneg weightNonnegative (norm_nonneg _))).trans raw) groupNonnegative)
    have secondBound : ‖weight • (finalNeutralForcing time - firstNeutralForcing time)‖ ≤ majorant time := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg weightNonnegative]
      have bound := (le_add_of_nonneg_left (norm_nonneg (finalTransverseForcing time - firstTransverseForcing time))).trans raw
      exact bound.trans (le_mul_of_one_le_left (add_nonneg (mul_nonneg rateNonnegative (distanceNonnegative time))
        (sourceNonnegative time ⟨inside.1.le, inside.2.le⟩)) groupBoundOne)
    exact max_le firstBound secondBound
  have endpoint (time : ℝ) : distance time ≤ (groupBound + 1) * ‖curve time‖ := by
    have inverse : group time (group (-time) (finalTransverse time - firstTransverse time)) = finalTransverse time - firstTransverse time := by
      rw [← ContinuousLinearMap.comp_apply, ← addition, add_neg_cancel, atZero, ContinuousLinearMap.id_apply]
    have first := (groupBounded time (group (-time) (finalTransverse time - firstTransverse time))).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le (curve time)) groupNonnegative)
    rw [inverse] at first
    have second := norm_snd_le (curve time)
    change ‖weight • (finalNeutral time - firstNeutral time)‖ ≤ ‖curve time‖ at second
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg weightNonnegative] at second
    dsimp only [distance, weightedBoundaryPairDistance]
    nlinarith only [first, second]
  have initial : ‖curve 0‖ ≤ distance 0 := by
    dsimp only [curve, distance, weightedBoundaryPairDistance]
    rw [neg_zero, atZero, ContinuousLinearMap.id_apply, Prod.norm_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg weightNonnegative]
    exact max_le (le_add_of_nonneg_right (mul_nonneg weightNonnegative (norm_nonneg _))) (le_add_of_nonneg_left (norm_nonneg _))
  have history (time : ℝ) (inside : time ∈ Icc 0 horizon) : distance time ≤
      (groupBound + 1) * groupBound * distance 0 +
      ∫ current in (0 : ℝ)..time, (groupBound + 1) * groupBound * source current +
        (groupBound + 1) * groupBound * rate * distance current := by
    have subset : Icc 0 time ⊆ Icc 0 horizon := fun current member => ⟨member.1, member.2.trans inside.2⟩
    have integral := norm_sub_le_integral_of_interior_derivative_majorant inside.1 (curveContinuous.mono subset)
      (majorantContinuous.mono subset)
      (fun current member => mul_nonneg groupNonnegative
        (add_nonneg (mul_nonneg rateNonnegative (distanceNonnegative current)) (sourceNonnegative current (subset member))))
      (fun current member => equation current ⟨member.1, member.2.trans_le inside.2⟩)
      (fun current member => derivativeBound current ⟨member.1, member.2.trans_le inside.2⟩)
    have triangle : ‖curve time‖ ≤ ‖curve time - curve 0‖ + ‖curve 0‖ := by
      simpa only [sub_add_cancel] using norm_add_le (curve time - curve 0) (curve 0)
    have initialEnlarged : (groupBound + 1) * distance 0 ≤ (groupBound + 1) * groupBound * distance 0 := by
      nlinarith only [groupBoundOne, enlargedNonnegative, distanceNonnegative 0, mul_nonneg enlargedNonnegative (distanceNonnegative 0)]
    have result := (endpoint time).trans (mul_le_mul_of_nonneg_left
      (triangle.trans (add_le_add integral initial)) enlargedNonnegative)
    have identity : (groupBound + 1) * (∫ current in (0 : ℝ)..time, majorant current) =
        ∫ current in (0 : ℝ)..time, (groupBound + 1) * groupBound * source current +
          (groupBound + 1) * groupBound * rate * distance current := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext current
      dsimp only [majorant]
      ring
    calc
      distance time ≤ (groupBound + 1) * distance 0 + (groupBound + 1) * (∫ current in (0 : ℝ)..time, majorant current) := by nlinarith only [result]
      _ ≤ _ := by rw [identity]; exact add_le_add_right initialEnlarged _
  have gronwall := EulerNonuniqueness.integral_gronwall_with_forcing_on_Icc distanceContinuous
    (continuousOn_const.mul sourceContinuous) (mul_nonneg (mul_nonneg enlargedNonnegative groupNonnegative) rateNonnegative)
    horizonNonnegative history
  exact fun time inside => ⟨history time inside, gronwall time inside⟩

end EulerNonuniqueness.General
