import EulerNonuniqueness.Section3.HolderBanachModel
import EulerNonuniqueness.Section3.ContourHolderMapping

open Set
open scoped BoundedContinuousFunction

namespace EulerNonuniqueness.Paper

noncomputable section

theorem standardCircle_periodic : Function.Periodic standardCircle (2 * Real.pi) := by
  intro label
  rw [standardCircle_add]
  have period_value : standardCircle (2 * Real.pi) = 1 := by
    simp only [standardCircle, Complex.ofReal_mul, Complex.ofReal_ofNat]
    exact Complex.exp_two_pi_mul_I
  rw [period_value, mul_one]

theorem standardCircleTangent_periodic : Function.Periodic standardCircleTangent (2 * Real.pi) := by
  intro label
  change Complex.I * standardCircle (label + 2 * Real.pi) = Complex.I * standardCircle label
  rw [standardCircle_periodic label]

theorem standardCircleTangent_holder_global (first second : ℝ) :
    ‖standardCircleTangent first - standardCircleTangent second‖ ≤ 2 * Real.sqrt |first - second| := by
  by_cases near : |first - second| ≤ 1
  · have speed := contour_speed_bound_on_interval
      (lower := min first second) (upper := max first second)
      (fun source _ => standardCircleTangent_derivative source)
      (speed := 1) (fun source _ => by simp [norm_mul, standardCircleTangent_norm])
      (show second ∈ Icc (min first second) (max first second) from ⟨min_le_right _ _, le_max_right _ _⟩)
      (show first ∈ Icc (min first second) (max first second) from ⟨min_le_left _ _, le_max_left _ _⟩)
    have root_le : Real.sqrt |first - second| ≤ 1 := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt near
    have distance_le : |first - second| ≤ Real.sqrt |first - second| := by
      calc
        _ = Real.sqrt |first - second| * Real.sqrt |first - second| := (Real.mul_self_sqrt (abs_nonneg _)).symm
        _ ≤ Real.sqrt |first - second| * 1 := mul_le_mul_of_nonneg_left root_le (Real.sqrt_nonneg _)
        _ = _ := mul_one _
    have speed_bound : ‖standardCircleTangent first - standardCircleTangent second‖ ≤ |first - second| := by
      simpa only [one_mul] using speed
    exact speed_bound.trans (distance_le.trans (by nlinarith [Real.sqrt_nonneg |first - second|]))
  · have root_ge : 1 ≤ Real.sqrt |first - second| := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (le_of_not_ge near)
    have estimate := norm_sub_le (standardCircleTangent first) (standardCircleTangent second)
    rw [standardCircleTangent_norm, standardCircleTangent_norm] at estimate
    linarith

def standardCircleBanach : PeriodicC1HolderHalf :=
  PeriodicC1HolderHalf.ofFunctions standardCircle standardCircleTangent
    (continuous_iff_continuousAt.mpr (fun label => (standardCircle_derivative label).continuousAt))
    (continuous_iff_continuousAt.mpr (fun label => (standardCircleTangent_derivative label).continuousAt))
    1 1 2 (fun label => (standardCircle_norm label).le)
    (fun label => (standardCircleTangent_norm label).le) standardCircleTangent_holder_global
    standardCircle_derivative standardCircle_periodic standardCircleTangent_periodic

theorem standardCircleBanach_norm_bound : ‖standardCircleBanach‖ ≤ 2 := by
  unfold standardCircleBanach
  have estimate := PeriodicC1HolderHalf.ofFunctions_norm_bound standardCircle standardCircleTangent
    (continuous_iff_continuousAt.mpr (fun label => (standardCircle_derivative label).continuousAt))
    (continuous_iff_continuousAt.mpr (fun label => (standardCircleTangent_derivative label).continuousAt))
    (valueBound := 1) (speedBound := 1) (holder := 2)
    (by norm_num) (by norm_num) (by norm_num)
    (fun label => (standardCircle_norm label).le) (fun label => (standardCircleTangent_norm label).le)
    standardCircleTangent_holder_global standardCircle_derivative standardCircle_periodic standardCircleTangent_periodic
  simpa using estimate

theorem PeriodicC1HolderHalf.derivative_close_circle (data : PeriodicC1HolderHalf) (label : ℝ) :
    ‖data.val.2.val.1 label - standardCircleTangent label‖ ≤ ‖data - standardCircleBanach‖ := by
  exact PeriodicC1HolderHalf.speed_bound (data - standardCircleBanach) label

theorem PeriodicC1HolderHalf.chord_bound_near_circle (data : PeriodicC1HolderHalf)
    {target source : ℝ} (nearby : |source - target| ≤ Real.pi) :
    (2 / Real.pi - ‖data - standardCircleBanach‖) * |source - target| ≤
      ‖data.val.1 target - data.val.1 source‖ := by
  exact contour_near_circle_chord_bound (PeriodicC1HolderHalf.hasDerivAt data)
    (PeriodicC1HolderHalf.derivative_close_circle data) nearby

end

end EulerNonuniqueness.Paper
