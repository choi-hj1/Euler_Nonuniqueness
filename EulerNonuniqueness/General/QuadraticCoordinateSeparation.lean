import EulerNonuniqueness.General.QuadraticCoordinateChange

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem quadratic_diagonal_sub_norm_le (bilinear : BilinearEnd Space) (first second : Space) :
    ‖bilinear first first - bilinear second second‖ ≤
      ‖bilinear‖ * (‖first‖ + ‖second‖) * ‖first - second‖ := by
  have difference : bilinear first first - bilinear second second =
      bilinear (first - second) first + bilinear second (first - second) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [difference]
  calc
    _ ≤ ‖bilinear (first - second) first‖ + ‖bilinear second (first - second)‖ := norm_add_le _ _
    _ ≤ ‖bilinear‖ * ‖first - second‖ * ‖first‖ + ‖bilinear‖ * ‖second‖ * ‖first - second‖ :=
      add_le_add (bilinear.le_opNorm₂ _ _) (bilinear.le_opNorm₂ _ _)
    _ = _ := by ring

theorem quadraticCoordinate_separation
    (correction : BilinearEnd Space) (frequency : ℝ) (first second : Space) {radius : ℝ}
    (firstInside : ‖first‖ ≤ radius) (secondInside : ‖second‖ ≤ radius)
    (small : (2 * ‖correction‖ / |frequency|) * radius ≤ 1 / 2) :
    ‖first - second‖ / 2 ≤
      ‖quadraticCoordinate correction frequency first - quadraticCoordinate correction frequency second‖ := by
  have difference :
      (quadraticCoordinate correction frequency first - quadraticCoordinate correction frequency second) -
          (first - second) = -(1 / frequency : ℝ) • (correction first first - correction second second) := by
    simp only [quadraticCoordinate, smul_sub, neg_smul]
    abel
  have estimate : ‖(quadraticCoordinate correction frequency first - quadraticCoordinate correction frequency second) -
          (first - second)‖ ≤ (2 * ‖correction‖ / |frequency|) * radius * ‖first - second‖ := by
    rw [difference, norm_smul, Real.norm_eq_abs, abs_neg, abs_div, abs_one]
    calc
      _ ≤ (1 / |frequency|) * (‖correction‖ * (‖first‖ + ‖second‖) * ‖first - second‖) :=
        mul_le_mul_of_nonneg_left (quadratic_diagonal_sub_norm_le correction first second) (by positivity)
      _ ≤ (1 / |frequency|) * (‖correction‖ * (radius + radius) * ‖first - second‖) := by gcongr
      _ = _ := by ring
  have halfBound := mul_le_mul_of_nonneg_right small (norm_nonneg (first - second))
  have reverse := norm_sub_norm_le (first - second)
    (quadraticCoordinate correction frequency first - quadraticCoordinate correction frequency second)
  have reversedNorm : ‖first - second -
      (quadraticCoordinate correction frequency first - quadraticCoordinate correction frequency second)‖ =
      ‖(quadraticCoordinate correction frequency first - quadraticCoordinate correction frequency second) -
        (first - second)‖ := norm_sub_rev _ _
  rw [reversedNorm] at reverse
  nlinarith

theorem quadraticCoordinate_injOn_closedBall
    (correction : BilinearEnd Space) (frequency : ℝ) {radius : ℝ}
    (small : (2 * ‖correction‖ / |frequency|) * radius ≤ 1 / 2) :
    Set.InjOn (quadraticCoordinate correction frequency) (Metric.closedBall (0 : Space) radius) := by
  intro first firstInside second secondInside same
  have firstBound : ‖first‖ ≤ radius := by simpa only [Metric.mem_closedBall, dist_zero_right] using firstInside
  have secondBound : ‖second‖ ≤ radius := by simpa only [Metric.mem_closedBall, dist_zero_right] using secondInside
  have separated := quadraticCoordinate_separation correction frequency first second firstBound secondBound small
  rw [same, sub_self, norm_zero] at separated
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (first - second)]))

end EulerNonuniqueness.General
