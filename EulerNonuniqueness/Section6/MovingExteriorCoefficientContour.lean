import EulerNonuniqueness.Section3.ContourInversePowerSeparation
import EulerNonuniqueness.Section6.MovingExteriorTaylorCoefficient

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

namespace MovingMaterialPatch

def exteriorInversePowerFunctional (path : MovingMaterialPatch) (receiver : ℂ)
    (power : ℕ) (time : ℝ) : ℂ :=
  contourAntiholomorphicFunctional
    (fun position => (star ((receiver - path.center time) -
      ((path.radius : ℂ) * (Circle.exp (path.phase time) : ℂ)) * position))⁻¹ ^ (power + 1))
    (path.shape time)

theorem domain_inverse_power_integral_eq_functional (path : MovingMaterialPatch) (time : ℝ)
    (receiver : ℂ) {distance : ℝ} (positive : 0 < distance) (power : ℕ)
    (separated : 2 * path.radius + distance ≤ ‖receiver - path.center time‖) :
    (∫ position in path.domain time, (star (receiver - position))⁻¹ ^ (power + 1)) =
      path.radius ^ 2 • path.exteriorInversePowerFunctional receiver power time := by
  rw [domain, integral_similarityPatchDomain _ path.radius_positive]
  have scaleNorm : ‖(path.radius : ℂ) * (Circle.exp (path.phase time) : ℂ)‖ = path.radius := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg path.radius_positive.le, Circle.norm_coe, mul_one]
  have gap : 2 * ‖(path.radius : ℂ) * (Circle.exp (path.phase time) : ℂ)‖ + distance ≤
      ‖receiver - path.center time‖ := by simpa only [scaleNorm] using separated
  have actual := integral_nearCircleInterior_conjugate_inverse_power_eq_functional_of_gap
    (path.shape time) (path.nearby time) (receiver - path.center time)
    ((path.radius : ℂ) * (Circle.exp (path.phase time) : ℂ)) positive power gap
  have displacementIdentity (position : ℂ) :
      receiver - (path.center time + path.radius • ((Circle.exp (path.phase time) : ℂ) * position)) =
        (receiver - path.center time) -
          ((path.radius : ℂ) * (Circle.exp (path.phase time) : ℂ)) * position := by
    simp only [Complex.real_smul]
    ring
  simp_rw [displacementIdentity]
  exact congrArg (fun value : ℂ => path.radius ^ 2 • value) actual

end MovingMaterialPatch

theorem FiniteMovingPatchFamily.exteriorTaylorCoefficient_eq_sum_contourFunctionals
    {count : ℕ} (family : FiniteMovingPatchFamily count) (selected : Finset (Fin count))
    (center : ℝ → ℂ) (radius : ℝ) (power : ℕ) (time : ℝ)
    (distance : Fin count → ℝ) (positive : ∀ source ∈ selected, 0 < distance source)
    (separated : ∀ source ∈ selected,
      2 * (family.patch source).radius + distance source ≤ ‖center time - (family.patch source).center time‖) :
    family.exteriorTaylorCoefficient selected center radius power time =
      ((-1 : ℂ) ^ power * Complex.I * (radius : ℂ) ^ (power - 1) / ((2 * Real.pi : ℝ) : ℂ)) *
        ∑ source ∈ selected, family.density source • ((family.patch source).radius ^ 2 •
          (family.patch source).exteriorInversePowerFunctional (center time) power time) := by
  unfold FiniteMovingPatchFamily.exteriorTaylorCoefficient
  congr 1
  apply Finset.sum_congr rfl
  intro source member
  rw [(family.patch source).domain_inverse_power_integral_eq_functional time (center time)
    (positive source member) power (separated source member)]

end EulerNonuniqueness.Paper
