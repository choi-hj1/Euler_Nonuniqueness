import Mathlib

noncomputable section

theorem abs_dist_sub_half_dist_le_of_dist_midpoint_le
    {space : Type*} [NormedAddCommGroup space] [NormedSpace ℝ space]
    {position center first second : space} {localError centerError : ℝ}
    (nearFirst : dist position first ≤ localError)
    (nearCenter : dist center (midpoint ℝ first second) ≤ centerError) :
    |dist position center - dist first second / 2| ≤ localError + centerError := by
  have midpointDistance : dist first (midpoint ℝ first second) = dist first second / 2 := by
    simpa only [dist_left_midpoint, Real.norm_ofNat, inv_mul_eq_div] using
      dist_left_midpoint (𝕜 := ℝ) first second
  have firstChange := abs_dist_sub_le position first center
  have centerChange := abs_dist_sub_le center (midpoint ℝ first second) first
  rw [dist_comm center first, dist_comm (midpoint ℝ first second) first, midpointDistance] at centerChange
  calc
    _ = |(dist position center - dist first center) +
        (dist first center - dist first second / 2)| := by congr 1; ring
    _ ≤ |dist position center - dist first center| + |dist first center - dist first second / 2| := abs_add _ _
    _ ≤ dist position first + dist center (midpoint ℝ first second) := add_le_add firstChange centerChange
    _ ≤ localError + centerError := add_le_add nearFirst nearCenter

theorem dist_annulus_of_dist_midpoint_le
    {space : Type*} [NormedAddCommGroup space] [NormedSpace ℝ space]
    {position center first second : space} {localError centerError : ℝ}
    (nearFirst : dist position first ≤ localError)
    (nearCenter : dist center (midpoint ℝ first second) ≤ centerError) :
    dist first second / 2 - localError - centerError ≤ dist position center ∧
      dist position center ≤ dist first second / 2 + localError + centerError := by
  have estimate := abs_le.mp (abs_dist_sub_half_dist_le_of_dist_midpoint_le nearFirst nearCenter)
  constructor <;> linarith
