import EulerNonuniqueness.General.RadialTruncation

noncomputable section

open Set Metric
open scoped NNReal

theorem exists_bounded_lipschitz_extension_from_closedBall
    {space : Type*} [NormedAddCommGroup space] [NormedSpace ℝ space]
    {field : space → space} {center : space} {radius : ℝ} (radiusPositive : 0 < radius)
    {constant : ℝ≥0} (lipschitz : LipschitzOnWith constant field (closedBall center radius)) :
    ∃ extension : space → space, LipschitzWith (2 * constant) extension ∧
      (∀ position, ‖extension position‖ ≤ (constant : ℝ) * radius + ‖field center‖) ∧
      EqOn extension field (closedBall center radius) := by
  let projection : space → space := fun position => center + radialTruncation radius (position - center)
  have projectionInside (position : space) : projection position ∈ closedBall center radius := by
    rw [mem_closedBall, dist_eq_norm]
    simpa only [projection, add_sub_cancel_left] using norm_radialTruncation_le radiusPositive (position - center)
  have projectionLipschitz : LipschitzWith 2 projection := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    simpa only [projection, dist_add_left, dist_sub_right] using
      (lipschitzWith_radialTruncation radiusPositive).dist_le_mul (first - center) (second - center)
  let extension : space → space := field ∘ projection
  have extensionLipschitz : LipschitzWith (2 * constant) extension := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    have estimate := lipschitz.dist_le_mul (projection first) (projectionInside first)
      (projection second) (projectionInside second)
    have projectionEstimate := projectionLipschitz.dist_le_mul first second
    change dist (field (projection first)) (field (projection second)) ≤ _
    calc
      _ ≤ (constant : ℝ) * dist (projection first) (projection second) := estimate
      _ ≤ (constant : ℝ) * (2 * dist first second) :=
        mul_le_mul_of_nonneg_left projectionEstimate constant.coe_nonneg
      _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_ofNat]; ring
  have extensionBound (position : space) : ‖extension position‖ ≤ (constant : ℝ) * radius + ‖field center‖ := by
    have estimate := lipschitz.dist_le_mul (projection position) (projectionInside position)
      center (mem_closedBall_self radiusPositive.le)
    have distanceBound : dist (projection position) center ≤ radius := projectionInside position
    have triangle := norm_add_le (field (projection position) - field center) (field center)
    rw [sub_add_cancel, ← dist_eq_norm] at triangle
    exact triangle.trans (add_le_add_right
      (estimate.trans (mul_le_mul_of_nonneg_left distanceBound constant.coe_nonneg)) _)
  refine ⟨extension, extensionLipschitz, extensionBound, ?_⟩
  intro position inside
  have normBound : ‖position - center‖ ≤ radius := by simpa only [mem_closedBall, dist_eq_norm] using inside
  have projectionIdentity : projection position = position := by
    dsimp only [projection]
    rw [radialTruncation_eq_self radiusPositive normBound]
    abel
  change field (projection position) = field position
  rw [projectionIdentity]
