import EulerNonuniqueness.General.CubicSpectralIntertwiner

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem cubicSpectralProjection_generator (generator : Space →L[ℝ] Space)
    (cubic : ∀ value, generator (generator (generator value)) = (-1 / 4 : ℝ) • generator value)
    (value : Space) :
    cubicSpectralProjection generator (generator value) = generator value ∧
      generator (cubicSpectralProjection generator value) = generator value := by
  constructor
  · change (-4 : ℝ) • generator (generator (generator value)) = generator value
    rw [cubic, smul_smul]
    norm_num
  · change generator ((-4 : ℝ) • generator (generator value)) = generator value
    rw [map_smul, cubic, smul_smul]
    norm_num

theorem cubicSpectralProjection_zero_of_generator_zero (generator : Space →L[ℝ] Space)
    (value : Space) (kernel : generator value = 0) : cubicSpectralProjection generator value = 0 := by
  change (-4 : ℝ) • generator (generator value) = 0
  rw [kernel, map_zero, smul_zero]

end EulerNonuniqueness.General
