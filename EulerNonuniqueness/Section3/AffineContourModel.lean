import EulerNonuniqueness.Section3.CrossContourNorms

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

local instance affineContourHolderNormedSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance affineContourC1NormedSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance affineContourBoundedSMul : IsBoundedSMul ℝ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℝ) (E := PeriodicC1HolderHalf)

def c1AffineContour (center : ℂ) (radius : ℝ) (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  c1Constant center + radius • data

theorem c1AffineContour_value (center : ℂ) (radius : ℝ) (data : PeriodicC1HolderHalf) (label : ℝ) :
    (c1AffineContour center radius data).val.1 label = center + radius • data.val.1 label := rfl

theorem c1AffineContour_tangent (center : ℂ) (radius : ℝ) (data : PeriodicC1HolderHalf) (label : ℝ) :
    (c1AffineContour center radius data).val.2.val.1 label = radius • data.val.2.val.1 label := by
  change 0 + radius • data.val.2.val.1 label = _
  exact zero_add _

theorem c1AffineContour_norm_bound (center : ℂ) (radius : ℝ) (data : PeriodicC1HolderHalf) :
    ‖c1AffineContour center radius data‖ ≤ ‖center‖ + |radius| * ‖data‖ := by
  exact (norm_add_le _ _).trans (add_le_add (c1Constant_norm_bound center)
    (by rw [norm_smul radius data, Real.norm_eq_abs]))

theorem c1AffineContour_difference_norm (center : ℂ) (radius : ℝ)
    (first second : PeriodicC1HolderHalf) :
    ‖c1AffineContour center radius first - c1AffineContour center radius second‖ =
      |radius| * ‖first - second‖ := by
  have identity : c1AffineContour center radius first - c1AffineContour center radius second =
      radius • (first - second) := by
    unfold c1AffineContour
    rw [smul_sub radius first second]
    abel
  rw [identity, norm_smul radius (first - second), Real.norm_eq_abs]

theorem c1AffineContour_separation_bound (firstCenter secondCenter : ℂ) (firstRadius secondRadius : ℝ)
    (first second : PeriodicC1HolderHalf) (firstLabel secondLabel : ℝ) :
    ‖firstCenter - secondCenter‖ - |firstRadius| * ‖first‖ - |secondRadius| * ‖second‖ ≤
      ‖(c1AffineContour firstCenter firstRadius first).val.1 firstLabel -
        (c1AffineContour secondCenter secondRadius second).val.1 secondLabel‖ := by
  rw [c1AffineContour_value, c1AffineContour_value]
  have identity : firstCenter - secondCenter =
      (firstCenter + firstRadius • first.val.1 firstLabel -
        (secondCenter + secondRadius • second.val.1 secondLabel)) -
      firstRadius • first.val.1 firstLabel + secondRadius • second.val.1 secondLabel := by abel
  have triangle := norm_add_le
    ((firstCenter + firstRadius • first.val.1 firstLabel -
      (secondCenter + secondRadius • second.val.1 secondLabel)) - firstRadius • first.val.1 firstLabel)
    (secondRadius • second.val.1 secondLabel)
  have triangle_sub := norm_sub_le
    (firstCenter + firstRadius • first.val.1 firstLabel -
      (secondCenter + secondRadius • second.val.1 secondLabel)) (firstRadius • first.val.1 firstLabel)
  rw [norm_smul, Real.norm_eq_abs] at triangle_sub
  rw [norm_smul, Real.norm_eq_abs] at triangle
  rw [← identity] at triangle
  have first_bound := mul_le_mul_of_nonneg_left (PeriodicC1HolderHalf.value_bound first firstLabel) (abs_nonneg firstRadius)
  have second_bound := mul_le_mul_of_nonneg_left (PeriodicC1HolderHalf.value_bound second secondLabel) (abs_nonneg secondRadius)
  linarith

end

end EulerNonuniqueness.Paper
