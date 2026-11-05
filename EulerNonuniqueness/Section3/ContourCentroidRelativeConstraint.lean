import EulerNonuniqueness.Section3.ContourCentroidRelativeTaylor

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance centroidConstraintC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph
local instance centroidConstraintC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem contourCentroidOffset_fderiv (base : PeriodicC1HolderHalf) (small : ‖base‖ < 1 / 3) :
    fderiv ℝ contourCentroidOffset base =
      fderiv ℝ contourCentroidFunctional (standardCircleBanach + base) := by
  have nearby : ‖standardCircleBanach + base - standardCircleBanach‖ < 1 / 3 := by
    simpa only [add_sub_cancel_left] using small
  have outer : HasFDerivAt contourCentroidFunctional
      (fderiv ℝ contourCentroidFunctional (standardCircleBanach + base)) (standardCircleBanach + base) :=
    (analyticAt_contourCentroidFunctional _ nearby).differentiableAt.hasFDerivAt
  have inner : HasFDerivAt (fun current : PeriodicC1HolderHalf => standardCircleBanach + current)
      (ContinuousLinearMap.id ℝ PeriodicC1HolderHalf) base := by
    simpa only [zero_add] using
      (hasFDerivAt_const (𝕜 := ℝ) standardCircleBanach base).add (hasFDerivAt_id (𝕜 := ℝ) base)
  have actual := (outer.comp base inner).fderiv
  simpa only [contourCentroidOffset, ContinuousLinearMap.comp_id] using actual

theorem contourCentroidTaylorRemainder_eq_actual (base increment : PeriodicC1HolderHalf)
    (small : ‖base - standardCircleBanach‖ < 1 / 3) :
    contourCentroidTaylorRemainder (base - standardCircleBanach) increment =
      contourCentroidFunctional (base + increment) - contourCentroidFunctional base -
        fderiv ℝ contourCentroidFunctional base increment := by
  have shiftedBase : standardCircleBanach + (base - standardCircleBanach) = base := by abel
  have shiftedPoint : standardCircleBanach + ((base - standardCircleBanach) + increment) = base + increment := by abel
  unfold contourCentroidTaylorRemainder
  rw [contourCentroidOffset_fderiv _ small]
  simp only [contourCentroidOffset, shiftedBase, shiftedPoint]

theorem contourCentroidDerivative_eq_neg_taylor_of_equal_centroid
    (base increment : PeriodicC1HolderHalf) (small : ‖base - standardCircleBanach‖ < 1 / 3)
    (equalCentroid : contourCentroidFunctional (base + increment) = contourCentroidFunctional base) :
    fderiv ℝ contourCentroidFunctional base increment =
      -contourCentroidTaylorRemainder (base - standardCircleBanach) increment := by
  have remainder := contourCentroidTaylorRemainder_eq_actual base increment small
  rw [equalCentroid, sub_self, zero_sub] at remainder
  simpa only [neg_neg] using congrArg Neg.neg remainder.symm

theorem contourCentroidDerivative_exists_relative_quadratic_constraint_ball :
    ∃ radius > 0, ∃ constant : NNReal,
      ∀ initialBase finalBase initialIncrement finalIncrement : PeriodicC1HolderHalf,
      ‖initialBase - standardCircleBanach‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖finalBase - standardCircleBanach‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      contourCentroidFunctional (initialBase + initialIncrement) = contourCentroidFunctional initialBase →
      contourCentroidFunctional (finalBase + finalIncrement) = contourCentroidFunctional finalBase →
      ‖fderiv ℝ contourCentroidFunctional initialBase initialIncrement -
        fderiv ℝ contourCentroidFunctional finalBase finalIncrement‖ ≤ (constant : ℝ) *
        ((‖initialIncrement‖ + ‖finalIncrement‖) * ‖initialIncrement - finalIncrement‖ +
          ‖initialBase - finalBase‖ * ‖finalIncrement‖ ^ 2) := by
  obtain ⟨radius, positive, constant, bound⟩ := contourCentroidTaylorRemainder_exists_relative_quadratic_ball
  refine ⟨min radius (1 / 6), lt_min positive (by norm_num), constant, ?_⟩
  intro initialBase finalBase initialIncrement finalIncrement initialInside finalInside initialCentroid finalCentroid
  have initialSmall : ‖initialBase - standardCircleBanach‖ < 1 / 3 := by
    have := initialInside.trans (min_le_right radius (1 / 6))
    linarith [norm_nonneg initialIncrement, norm_nonneg finalIncrement]
  have finalSmall : ‖finalBase - standardCircleBanach‖ < 1 / 3 := by
    have := finalInside.trans (min_le_right radius (1 / 6))
    linarith [norm_nonneg initialIncrement, norm_nonneg finalIncrement]
  have first := contourCentroidDerivative_eq_neg_taylor_of_equal_centroid
    initialBase initialIncrement initialSmall initialCentroid
  have second := contourCentroidDerivative_eq_neg_taylor_of_equal_centroid
    finalBase finalIncrement finalSmall finalCentroid
  have actual := bound (initialBase - standardCircleBanach) (finalBase - standardCircleBanach)
    initialIncrement finalIncrement (initialInside.trans (min_le_left _ _)) (finalInside.trans (min_le_left _ _))
  have baseDifference : (initialBase - standardCircleBanach) - (finalBase - standardCircleBanach) =
      initialBase - finalBase := by abel
  rw [baseDifference] at actual
  simpa only [first, second, neg_sub_neg, norm_sub_rev] using actual

end

end EulerNonuniqueness.Paper
