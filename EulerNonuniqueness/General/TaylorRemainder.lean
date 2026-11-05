import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Set

namespace EulerNonuniqueness

theorem norm_taylor_remainder_le {Domain Target : Type*}
    [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    {function : Domain → Target} {derivative : Domain → Domain →L[ℝ] Target}
    {region : Set Domain} (convex : Convex ℝ region)
    (differentiable : ∀ point ∈ region, HasFDerivAt function (derivative point) point)
    {first second : Domain} (firstInside : first ∈ region) (secondInside : second ∈ region)
    {error : ℝ} (close : ∀ point ∈ region, ‖derivative point - derivative first‖ ≤ error) :
    ‖function second - function first - derivative first (second - first)‖ ≤
      error * ‖second - first‖ := by
  have estimate := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun point => function point - derivative first point)
    (f' := fun point => derivative point - derivative first)
    (fun point inside => ((differentiable point inside).sub
      (derivative first).hasFDerivAt).hasFDerivWithinAt) close convex firstInside secondInside
  convert estimate using 1
  congr 1
  rw [map_sub]
  simp only [sub_eq_add_neg, neg_add_rev, neg_neg, add_assoc, add_comm, add_left_comm]

end EulerNonuniqueness
