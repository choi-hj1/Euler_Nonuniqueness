import EulerNonuniqueness.Section3.DiskRotatingDerivative

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance physicalHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance physicalC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance physicalOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance physicalOperatorSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

def diskRelativeCLM : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  c1ProductCLM (c1Conjugate standardCircleBanach)

def diskRadialCLM : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  (1 / 2 : ℝ) • (diskRelativeCLM + c1ConjugateCLM.comp diskRelativeCLM)

def diskAngularCLM : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  (c1ProductCLM (c1Constant (-Complex.I / 2))).comp
    (diskRelativeCLM - c1ConjugateCLM.comp diskRelativeCLM)

def diskNeutralCLM : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  diskAngularCLM + periodicHilbertC1CLM.comp diskRadialCLM

theorem diskRelativeCLM_apply (direction : PeriodicC1HolderHalf) :
    diskRelativeCLM direction = diskRelativeC1 direction := rfl

theorem diskRadialCLM_apply (direction : PeriodicC1HolderHalf) :
    diskRadialCLM direction = diskRadialPart direction := rfl

theorem diskAngularCLM_value (direction : PeriodicC1HolderHalf) (label : ℝ) :
    (diskAngularCLM direction).val.1 label =
      -Complex.I / 2 * ((diskRelativeC1 direction).val.1 label -
        star ((diskRelativeC1 direction).val.1 label)) := rfl

theorem diskAngularCLM_real (direction : PeriodicC1HolderHalf) (label : ℝ) :
    star ((diskAngularCLM direction).val.1 label) = (diskAngularCLM direction).val.1 label := by
  rw [diskAngularCLM_value]
  rw [star_mul, star_sub, star_star]
  have scalar : star (-Complex.I / 2) = Complex.I / 2 := by simp
  rw [scalar]
  ring

theorem diskPhysicalCoordinates_reconstruct (direction : PeriodicC1HolderHalf) :
    diskMaterialPerturbation (diskRadialCLM direction) (diskAngularCLM direction) = direction := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change standardCircle label * ((1 / 2 : ℝ) •
    (star (standardCircle label) * direction.val.1 label +
      star (star (standardCircle label) * direction.val.1 label)) +
    Complex.I * (-Complex.I / 2 * (star (standardCircle label) * direction.val.1 label -
      star (star (standardCircle label) * direction.val.1 label)))) = direction.val.1 label
  simp only [Complex.real_smul]
  push_cast
  have unit : standardCircle label * star (standardCircle label) = 1 := by
    rw [standardCircle_star_eq_inv, mul_inv_cancel₀]
    exact norm_ne_zero_iff.mp (by rw [standardCircle_norm]; norm_num)
  calc
    _ = (standardCircle label * star (standardCircle label)) * direction.val.1 label := by
      have imaginary := Complex.I_sq
      ring_nf
      simp only [imaginary]
      ring
    _ = _ := by rw [unit, one_mul]

theorem diskNeutralCLM_apply (direction : PeriodicC1HolderHalf) :
    diskNeutralCLM direction = diskAngularCLM direction + periodicHilbertC1 (diskRadialPart direction) := rfl

theorem diskAngularCLM_materialPerturbation (radial angular : PeriodicC1HolderHalf)
    (radialReal : ∀ label, star (radial.val.1 label) = radial.val.1 label)
    (angularReal : ∀ label, star (angular.val.1 label) = angular.val.1 label) :
    diskAngularCLM (diskMaterialPerturbation radial angular) = angular := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [diskAngularCLM_value, diskRelativeC1_materialPerturbation]
  change -Complex.I / 2 * (radial.val.1 label + Complex.I * angular.val.1 label -
    star (radial.val.1 label + Complex.I * angular.val.1 label)) = angular.val.1 label
  rw [star_add, star_mul, radialReal, angularReal]
  have imaginary : star Complex.I = -Complex.I := by simp
  rw [imaginary]
  linear_combination -(angular.val.1 label) * Complex.I_sq

theorem diskNeutralCLM_real (direction : PeriodicC1HolderHalf) (label : ℝ) :
    star ((diskNeutralCLM direction).val.1 label) = (diskNeutralCLM direction).val.1 label := by
  rw [diskNeutralCLM_apply]
  change star ((diskAngularCLM direction).val.1 label +
    (periodicHilbertC1 (diskRadialPart direction)).val.1 label) = _
  rw [star_add, diskAngularCLM_real, periodicHilbertC1_value]
  rw [periodicHilbertCLM_real (c1ValueHolder (diskRadialPart direction))
    (fun current => diskRadialPart_real direction current)]
  rfl

end

end EulerNonuniqueness.Paper
