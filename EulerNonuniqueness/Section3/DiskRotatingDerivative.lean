import EulerNonuniqueness.Section3.StationaryRelabelCurve
import EulerNonuniqueness.Section3.DiskMaterialCoordinates

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance rotatingHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance rotatingC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance rotatingOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance rotatingOperatorSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

def diskRotatingDerivative : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  fderiv ℝ extendedContourVelocity standardCircleBanach -
    c1ProductCLM (c1Constant (Complex.I / 2))

theorem diskRotatingDerivative_apply (direction : PeriodicC1HolderHalf) :
    diskRotatingDerivative direction = fderiv ℝ extendedContourVelocity standardCircleBanach direction -
      (Complex.I / 2) • direction := by
  change fderiv ℝ extendedContourVelocity standardCircleBanach direction -
    c1Product (c1Constant (Complex.I / 2)) direction = _
  congr 1
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rfl

theorem diskRelabel_tangent_eq_material (angular : PeriodicC1HolderHalf) :
    diskRelabelGenerator angular standardCircleBanach = diskMaterialPerturbation 0 angular := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (Complex.I * angular.val.1 label) * standardCircle label =
    standardCircle label * (0 + Complex.I * angular.val.1 label)
  ring

theorem diskRotatingDerivative_relabel_tangent_zero (angular : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label) :
    diskRotatingDerivative (diskRelabelGenerator angular standardCircleBanach) = 0 := by
  have radialZero : diskRadialPart (diskRelabelGenerator angular standardCircleBanach) = 0 := by
    rw [diskRelabel_tangent_eq_material]
    exact diskRadialPart_materialPerturbation 0 angular (fun _ => by change star (0 : ℂ) = 0; simp) realValues
  rw [diskRotatingDerivative_apply, disk_contour_generator, radialZero]
  have hilbertZero : periodicHilbertC1 (0 : PeriodicC1HolderHalf) = 0 := periodicHilbertC1CLM.map_zero
  simp only [hilbertZero, map_zero, smul_zero, sub_zero, sub_self]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change standardCircle label * ((0 : ℂ) - (Complex.I / 2) * (0 - 0)) = 0
  ring

end

end EulerNonuniqueness.Paper
