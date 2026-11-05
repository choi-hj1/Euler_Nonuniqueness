import EulerNonuniqueness.Section6.MovingPatchStrain

noncomputable section

open Set MeasureTheory Filter Asymptotics

namespace EulerNonuniqueness.Section6

theorem indicator_biotSavart_hasFDerivAt_of_separation {domain : Set ℂ}
    (measurable : MeasurableSet domain) (finite : volume domain < ⊤) (density : ℝ)
    {center : ℂ} {distance : ℝ} (positive : 0 < distance)
    (separated : ∀ source ∈ domain, distance ≤ ‖center - source‖) :
    HasFDerivAt (biotSavart (domain.indicator (fun _ => density)))
      ((density • ∫ source in domain, biotSavartKernelStrain center source) •
        (Complex.conjCLE : ℂ →L[ℝ] ℂ)) center := by
  let coefficient := |density| * volume.real domain / (Real.pi * distance ^ 3)
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro epsilon epsilonPositive
  let radius := min (distance / 2) (epsilon / (coefficient + 1))
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) radiusPositive] with increment member
  have incrementSmall : ‖increment‖ < radius := by
    simpa only [Metric.mem_ball, dist_zero_right] using member
  have near : 2 * ‖center + increment - center‖ ≤ distance := by
    rw [add_sub_cancel_left]
    have upper := incrementSmall.trans_le (min_le_left _ _)
    linarith
  have estimate := indicator_biotSavart_strain_taylor_bound measurable finite density positive separated near
  have coefficientSmall : coefficient * ‖increment‖ ≤ epsilon := by
    have upper := incrementSmall.trans_le (min_le_right _ _)
    have multiplied := (lt_div_iff₀ (by positivity : 0 < coefficient + 1)).mp upper
    nlinarith [norm_nonneg increment]
  change ‖biotSavart (domain.indicator (fun _ => density)) (center + increment) -
    biotSavart (domain.indicator (fun _ => density)) center -
    (density • ∫ source in domain, biotSavartKernelStrain center source) * star increment‖ ≤ epsilon * ‖increment‖
  simp only [add_sub_cancel_left] at estimate
  apply estimate.trans
  calc
    _ = (coefficient * ‖increment‖) * ‖increment‖ := by dsimp only [coefficient]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right coefficientSmall (norm_nonneg increment)

end EulerNonuniqueness.Section6
