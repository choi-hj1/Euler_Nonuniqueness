import EulerNonuniqueness.Section6.MovingExteriorNormalizedCoefficient
import EulerNonuniqueness.Section6.MovingExteriorCoefficientBound

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

namespace MovingMaterialPatch

def sourceTaylorCoefficient (path : MovingMaterialPatch) (density : ℝ) (receiver : ℂ)
    (receiverRadius : ℝ) (power : ℕ) (time : ℝ) : ℂ :=
  ((-1 : ℂ) ^ (power + 1) * Complex.I * (receiverRadius : ℂ) ^ power / ((2 * Real.pi : ℝ) : ℂ)) *
    (density • ∫ position in path.domain time, (star (receiver - position))⁻¹ ^ (power + 2))

theorem sourceTaylorCoefficient_eq_normalized (path : MovingMaterialPatch) (density : ℝ)
    (receiver : ℂ) (receiverRadius : ℝ) (power : ℕ) (time : ℝ) {distance : ℝ}
    (positive : 0 < distance)
    (separated : 2 * path.radius + distance ≤ ‖receiver - path.center time‖)
    (area : volume.real (path.domain time) = Real.pi * path.radius ^ 2) :
    path.sourceTaylorCoefficient density receiver receiverRadius power time =
      ((-1 : ℂ) ^ (power + 1) * Complex.I * (receiverRadius : ℂ) ^ power / ((2 * Real.pi : ℝ) : ℂ)) *
        (density : ℂ) * (path.radius : ℂ) ^ 2 * (star (receiver - path.center time))⁻¹ ^ (power + 2) *
          (contourAntiholomorphicFunctional
            (normalizedExteriorInversePowerKernel
              (((path.radius : ℂ) * (Circle.exp (path.phase time) : ℂ)) / (receiver - path.center time)) (power + 1))
            (path.shape time) + (Real.pi : ℂ)) := by
  unfold sourceTaylorCoefficient
  rw [path.domain_inverse_power_integral_eq_normalized time receiver positive (power + 1) separated area]
  simp only [Nat.add_assoc, Nat.reduceAdd, Complex.real_smul, Complex.ofReal_pow]
  ring

theorem sourceTaylorCoefficient_eq_vorticityCoefficient (path : MovingMaterialPatch) (density : ℝ)
    (receiver : ℂ) (receiverRadius : ℝ) (power : ℕ) (time : ℝ) :
    path.sourceTaylorCoefficient density receiver receiverRadius power time =
      Section6.exteriorVorticityCoefficient ((path.domain time).indicator (fun _ => density))
        receiver receiverRadius power := by
  unfold sourceTaylorCoefficient Section6.exteriorVorticityCoefficient
  congr 1
  rw [← integral_smul]
  rw [← integral_indicator ((path.domain_isOpen time).measurableSet)]
  congr 1
  funext position
  by_cases member : position ∈ path.domain time <;> simp [member]

end MovingMaterialPatch

theorem FiniteMovingPatchFamily.exteriorTaylorCoefficient_eq_sum_sourceTaylorCoefficient
    {count : ℕ} (family : FiniteMovingPatchFamily count) (selected : Finset (Fin count))
    (center : ℝ → ℂ) (radius : ℝ) (power : ℕ) (time : ℝ) :
    family.exteriorTaylorCoefficient selected center radius (power + 1) time =
      ∑ source ∈ selected, (family.patch source).sourceTaylorCoefficient
        (family.density source) (center time) radius power time := by
  unfold exteriorTaylorCoefficient MovingMaterialPatch.sourceTaylorCoefficient
  simp only [Nat.add_sub_cancel, Nat.add_assoc, Nat.reduceAdd, Finset.mul_sum]

end EulerNonuniqueness.Paper
