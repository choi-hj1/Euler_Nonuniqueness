import EulerNonuniqueness.Section6.PhysicalMomentRampCoefficient

noncomputable section

namespace EulerNonuniqueness.Section6

theorem physicalMomentTarget_strain_identity {circulation : ℝ} (nonzero : circulation ≠ 0)
    (moment displacement : ℂ) :
    -3 * Complex.I * ((circulation / (2 * Real.pi) : ℝ) : ℂ) *
        star (moment / (circulation : ℂ)) / star displacement ^ 4 =
      -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (3 * moment / displacement ^ 4) := by
  by_cases displacementZero : displacement = 0
  · simp [displacementZero]
  have starCirculation : star (circulation : ℂ) = (circulation : ℂ) := by
    simp only [Complex.star_def, Complex.conj_ofReal]
  simp only [star_div₀, star_mul, star_pow, star_ofNat, starCirculation, Complex.ofReal_div]
  have factor : (circulation : ℂ) / ((2 * Real.pi : ℝ) : ℂ) * (star moment / (circulation : ℂ)) =
      star moment / ((2 * Real.pi : ℝ) : ℂ) := by
    calc
      _ = (star moment / ((2 * Real.pi : ℝ) : ℂ)) * ((circulation : ℂ) / (circulation : ℂ)) := by ring
      _ = _ := by rw [div_self (Complex.ofReal_ne_zero.mpr nonzero), mul_one]
  calc
    _ = (-3 * Complex.I) * ((circulation : ℂ) / ((2 * Real.pi : ℝ) : ℂ) *
        (star moment / (circulation : ℂ))) / star displacement ^ 4 := by ring
    _ = _ := by rw [factor]; ring

end EulerNonuniqueness.Section6
