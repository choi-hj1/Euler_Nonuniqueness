import EulerNonuniqueness.Section3.LocalDerivativeLipschitzCalculus

noncomputable section

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Domain Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem norm_increment_base_difference_of_lipschitz_derivative
    (function : Domain → Target) (derivative : Domain → Domain →L[ℝ] Target)
    {radius : ℝ} (constant : NNReal)
    (actual : ∀ point ∈ closedBall (0 : Domain) radius, HasFDerivAt function (derivative point) point)
    (lipschitz : LipschitzOnWith constant derivative (closedBall (0 : Domain) radius))
    (first second increment : Domain)
    (firstInside : ‖first‖ + ‖increment‖ ≤ radius)
    (secondInside : ‖second‖ + ‖increment‖ ≤ radius) :
    ‖(function (first + increment) - function first) -
      (function (second + increment) - function second)‖ ≤
      (constant : ℝ) * ‖increment‖ * ‖first - second‖ := by
  let size := max ‖first‖ ‖second‖
  have sizeBound : size + ‖increment‖ ≤ radius := by
    dsimp only [size]
    rcases le_total ‖first‖ ‖second‖ with ordered | ordered
    · rwa [max_eq_right ordered]
    · rwa [max_eq_left ordered]
  have inside (point : Domain) (member : point ∈ closedBall (0 : Domain) size) :
      point ∈ closedBall (0 : Domain) radius ∧ point + increment ∈ closedBall (0 : Domain) radius := by
    have pointBound := mem_closedBall_zero_iff.mp member
    constructor
    · exact mem_closedBall_zero_iff.mpr (by linarith [norm_nonneg increment])
    · exact mem_closedBall_zero_iff.mpr ((norm_add_le _ _).trans (by linarith))
  let difference := fun point => function (point + increment) - function point
  have derivativeActual (point : Domain) (member : point ∈ closedBall (0 : Domain) size) :
      HasFDerivAt difference (derivative (point + increment) - derivative point) point := by
    have translated := (actual _ (inside point member).2).comp point
      ((hasFDerivAt_id (𝕜 := ℝ) point).add_const increment)
    simpa only [difference, Function.comp_def, ContinuousLinearMap.comp_id] using
      translated.sub (actual _ (inside point member).1)
  have derivativeBound (point : Domain) (member : point ∈ closedBall (0 : Domain) size) :
      ‖derivative (point + increment) - derivative point‖ ≤ (constant : ℝ) * ‖increment‖ := by
    have estimate := lipschitz.norm_sub_le (f := derivative) (inside point member).2 (inside point member).1
    simpa only [add_sub_cancel_left] using estimate
  have firstMember : first ∈ closedBall (0 : Domain) size :=
    mem_closedBall_zero_iff.mpr (le_max_left _ _)
  have secondMember : second ∈ closedBall (0 : Domain) size :=
    mem_closedBall_zero_iff.mpr (le_max_right _ _)
  have estimate := (convex_closedBall (0 : Domain) size).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun point member => (derivativeActual point member).hasFDerivWithinAt)
    derivativeBound firstMember secondMember
  rw [norm_sub_rev (difference second) (difference first), norm_sub_rev second first] at estimate
  exact estimate

theorem exists_relative_linear_increment_ball (function : Domain → Target)
    (regular : HasLipschitzDerivativeNear function (0 : Domain)) :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ first second initial final : Domain,
      ‖first‖ + (‖initial‖ + ‖final‖) ≤ radius →
      ‖second‖ + (‖initial‖ + ‖final‖) ≤ radius →
      ‖(function (first + initial) - function first) -
        (function (second + final) - function second)‖ ≤
        constant * (‖initial - final‖ + ‖first - second‖ * ‖final‖) := by
  obtain ⟨functionConstant, functionDomain, functionNearby, functionLip⟩ := regular.lipschitzNear
  obtain ⟨derivativeConstant, derivativeDomain, derivativeNearby, derivativeLip⟩ := regular.2
  have combined : functionDomain ∩ derivativeDomain ∩ {point | DifferentiableAt ℝ function point} ∈
      𝓝 (0 : Domain) := inter_mem (inter_mem functionNearby derivativeNearby) regular.1
  obtain ⟨outerRadius, outerPositive, contained⟩ := Metric.mem_nhds_iff.mp combined
  have inside (point : Domain) (member : point ∈ closedBall (0 : Domain) (outerRadius / 2)) :
      point ∈ functionDomain ∧ point ∈ derivativeDomain ∧ DifferentiableAt ℝ function point := by
    have bound := mem_closedBall_zero_iff.mp member
    have small : point ∈ ball (0 : Domain) outerRadius := mem_ball_zero_iff.mpr (by linarith)
    exact ⟨(contained small).1.1, (contained small).1.2, (contained small).2⟩
  let constant : ℝ := functionConstant + derivativeConstant
  refine ⟨outerRadius / 2, by positivity, constant, by dsimp only [constant]; positivity, ?_⟩
  intro first second initial final firstInside secondInside
  have shiftedMember (increment : Domain) (bound : ‖increment‖ ≤ ‖initial‖ + ‖final‖) :
      first + increment ∈ closedBall (0 : Domain) (outerRadius / 2) :=
    mem_closedBall_zero_iff.mpr ((norm_add_le _ _).trans ((add_le_add_left bound _).trans firstInside))
  have firstEstimate := functionLip.norm_sub_le (f := function)
    (inside _ (shiftedMember initial (le_add_of_nonneg_right (norm_nonneg _)))).1
    (inside _ (shiftedMember final (le_add_of_nonneg_left (norm_nonneg _)))).1
  rw [add_sub_add_left_eq_sub] at firstEstimate
  have secondEstimate := norm_increment_base_difference_of_lipschitz_derivative function (fderiv ℝ function)
    derivativeConstant (fun point member => (inside point member).2.2.hasFDerivAt)
    (derivativeLip.mono fun point member => (inside point member).2.1) first second final
    (by linarith [norm_nonneg initial]) (by linarith [norm_nonneg initial])
  have initialEstimate : ‖(function (first + initial) - function first) -
      (function (first + final) - function first)‖ ≤ (functionConstant : ℝ) * ‖initial - final‖ := by
    simpa only [sub_sub_sub_cancel_right] using firstEstimate
  apply (norm_sub_le_norm_sub_add_norm_sub (function (first + initial) - function first)
    (function (first + final) - function first) (function (second + final) - function second)).trans
  calc
    _ ≤ (functionConstant : ℝ) * ‖initial - final‖ +
        (derivativeConstant : ℝ) * ‖final‖ * ‖first - second‖ := add_le_add initialEstimate secondEstimate
    _ ≤ constant * ‖initial - final‖ + constant * ‖final‖ * ‖first - second‖ := by
      gcongr <;> dsimp only [constant] <;> linarith [functionConstant.coe_nonneg, derivativeConstant.coe_nonneg]
    _ = _ := by ring

end EulerNonuniqueness.General
