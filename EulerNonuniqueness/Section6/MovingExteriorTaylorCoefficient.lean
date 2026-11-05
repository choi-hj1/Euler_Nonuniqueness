import EulerNonuniqueness.Section6.MovingInversePowerMoment
import EulerNonuniqueness.Section3.FiniteMovingPatchFamily

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

def exteriorTaylorCoefficient {count : ℕ} (family : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) (center : ℝ → ℂ) (radius : ℝ) (power : ℕ) (time : ℝ) : ℂ :=
  ((-1 : ℂ) ^ power * Complex.I * (radius : ℂ) ^ (power - 1) / ((2 * Real.pi : ℝ) : ℂ)) *
    ∑ source ∈ selected, family.density source • ∫ position in (family.patch source).domain time,
      (star (center time - position))⁻¹ ^ (power + 1)

theorem exteriorTaylorCoefficient_hasDerivAt {count : ℕ} (family : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) (center centerVelocity : ℝ → ℂ) (radius : ℝ) (power : ℕ)
    (centerContinuous : Continuous center) (centerVelocityContinuous : Continuous centerVelocity)
    (centerDerivative : ∀ parameter, HasDerivAt center (centerVelocity parameter) parameter)
    {time : ℝ} (inside : ∀ source ∈ selected,
      time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (material : ∀ source ∈ selected, ∀ label,
      (family.patch source).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch source).boundary time label))
    (distance : Fin count → ℝ) (positive : ∀ source ∈ selected, 0 < distance source)
    (separatedNear : ∀ᶠ parameter in 𝓝 time, ∀ source ∈ selected, ∀ position ∈ (family.patch source).domain parameter,
      distance source ≤ ‖center parameter - position‖) :
    HasDerivAt (family.exteriorTaylorCoefficient selected center radius power)
      (((-1 : ℂ) ^ (power + 1) * Complex.I * ((power + 1 : ℕ) : ℂ) *
          (radius : ℂ) ^ (power - 1) / ((2 * Real.pi : ℝ) : ℂ)) *
        ∑ source ∈ selected, family.density source • ∫ position in (family.patch source).domain time,
          star (centerVelocity time - biotSavart (family.vorticity time) position) *
            (star (center time - position))⁻¹ ^ (power + 2)) time := by
  have individual (source : Fin count) (member : source ∈ selected) :=
    ((family.patch source).domain_conjugate_inverse_power_hasDerivAt (inside source member) (positive source member)
      (family.vorticity_integrable time) (family.vorticity_memLp time _) (material source member)
      center centerVelocity centerContinuous centerVelocityContinuous centerDerivative
      (separatedNear.mono (fun _ separated => separated source member)) power).const_smul (family.density source)
  have actual := (HasDerivAt.sum (fun source member => individual source member)).const_mul
    ((-1 : ℂ) ^ power * Complex.I * (radius : ℂ) ^ (power - 1) / ((2 * Real.pi : ℝ) : ℂ))
  convert actual using 1
  rw [pow_succ]
  simp only [Complex.real_smul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro source _
  ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
