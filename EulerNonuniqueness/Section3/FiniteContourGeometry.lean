import EulerNonuniqueness.Section3.AffineContourModel

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

structure FiniteContourConfiguration (count : ℕ) where
  center : Fin count → ℂ
  radius : Fin count → ℝ
  density : Fin count → ℝ
  radius_pos : ∀ index, 0 < radius index
  separated : ∀ first second, first ≠ second →
    3 * (radius first + radius second) < ‖center first - center second‖

def FiniteContourConfiguration.physicalContour {count : ℕ} (configuration : FiniteContourConfiguration count)
    (data : Fin count → PeriodicC1HolderHalf) (index : Fin count) : PeriodicC1HolderHalf :=
  c1AffineContour (configuration.center index) (configuration.radius index) (data index)

def FiniteContourConfiguration.crossGap {count : ℕ} (configuration : FiniteContourConfiguration count)
    (first second : Fin count) : ℝ :=
  ‖configuration.center first - configuration.center second‖ - 3 * (configuration.radius first + configuration.radius second)

theorem FiniteContourConfiguration.crossGap_pos {count : ℕ} (configuration : FiniteContourConfiguration count)
    (first second : Fin count) (distinct : first ≠ second) : 0 < configuration.crossGap first second :=
  sub_pos.mpr (configuration.separated first second distinct)

def FiniteContourConfiguration.crossNormBound {count : ℕ} (configuration : FiniteContourConfiguration count)
    (first second : Fin count) : ℝ :=
  max (‖configuration.center first‖ + 3 * configuration.radius first)
    (‖configuration.center second‖ + 3 * configuration.radius second)

theorem FiniteContourConfiguration.physicalContour_norm_bound {count : ℕ}
    (configuration : FiniteContourConfiguration count) (data : Fin count → PeriodicC1HolderHalf)
    (index : Fin count) (bounded : ‖data index‖ ≤ 3) :
    ‖configuration.physicalContour data index‖ ≤ ‖configuration.center index‖ + 3 * configuration.radius index := by
  apply (c1AffineContour_norm_bound _ _ _).trans
  rw [abs_of_pos (configuration.radius_pos index)]
  nlinarith [configuration.radius_pos index]

theorem FiniteContourConfiguration.physicalContour_separated {count : ℕ}
    (configuration : FiniteContourConfiguration count) (data : Fin count → PeriodicC1HolderHalf)
    (first second : Fin count) (first_bounded : ‖data first‖ ≤ 3) (second_bounded : ‖data second‖ ≤ 3)
    (sourceLabel targetLabel : ℝ) :
    configuration.crossGap first second ≤
      ‖(configuration.physicalContour data first).val.1 targetLabel -
        (configuration.physicalContour data second).val.1 sourceLabel‖ := by
  have estimate := c1AffineContour_separation_bound (configuration.center first) (configuration.center second)
    (configuration.radius first) (configuration.radius second) (data first) (data second) targetLabel sourceLabel
  rw [abs_of_pos (configuration.radius_pos first), abs_of_pos (configuration.radius_pos second)] at estimate
  have first_bound := mul_le_mul_of_nonneg_left first_bounded (configuration.radius_pos first).le
  have second_bound := mul_le_mul_of_nonneg_left second_bounded (configuration.radius_pos second).le
  unfold FiniteContourConfiguration.crossGap
  exact (by linarith : ‖configuration.center first - configuration.center second‖ -
    3 * (configuration.radius first + configuration.radius second) ≤
      ‖configuration.center first - configuration.center second‖ - configuration.radius first * ‖data first‖ -
        configuration.radius second * ‖data second‖).trans estimate

theorem FiniteContourConfiguration.physicalContour_parameter_norm {count : ℕ}
    (configuration : FiniteContourConfiguration count) (first second : Fin count → PeriodicC1HolderHalf)
    (index : Fin count) :
    ‖configuration.physicalContour first index - configuration.physicalContour second index‖ =
      configuration.radius index * ‖first index - second index‖ := by
  rw [FiniteContourConfiguration.physicalContour, FiniteContourConfiguration.physicalContour,
    c1AffineContour_difference_norm, abs_of_pos (configuration.radius_pos index)]

end

end EulerNonuniqueness.Paper
