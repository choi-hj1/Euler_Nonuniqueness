import EulerNonuniqueness.Section6.PointSourceDifferentiation
import EulerNonuniqueness.Section6.CoupledQuadrupoleDynamics

noncomputable section

namespace EulerNonuniqueness.Section6

def quadrupoleBlockExternalStrain {count : ℕ} (coefficients : Fin count → ℝ)
    (positions : FiniteQuadrupoleConfiguration count) (block : Fin count) (location : ℂ) : ℂ :=
  ∑ sourceBlock ∈ Finset.univ.erase block,
    fourPointExternalPointStrain (coefficients sourceBlock) (quadrupoleBlock positions sourceBlock) location

theorem quadrupoleBlockExternalField_source_sum {count : ℕ} (coefficients : Fin count → ℝ)
    (positions : FiniteQuadrupoleConfiguration count) (block : Fin count) (location : ℂ) :
    quadrupoleBlockExternalField coefficients positions block location =
      ∑ sourceBlock ∈ Finset.univ.erase block,
        fourPointExternalPointVelocity (coefficients sourceBlock) (quadrupoleBlock positions sourceBlock) location := by
  unfold quadrupoleBlockExternalField
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sourceBlock _
  simp only [fourPointExternalPointVelocity_literal, quadrupoleBlock]

theorem quadrupoleBlockExternalField_hasFDerivAt {count : ℕ} (coefficients : Fin count → ℝ)
    (positions : FiniteQuadrupoleConfiguration count) (block : Fin count) {location : ℂ}
    (noncollision : ∀ sourceBlock, sourceBlock ≠ block → ∀ source, location - positions (sourceBlock, source) ≠ 0) :
    HasFDerivAt (quadrupoleBlockExternalField coefficients positions block)
      (quadrupoleBlockExternalStrain coefficients positions block location •
        (Complex.conjCLE : ℂ →L[ℝ] ℂ)) location := by
  have derivative := HasFDerivAt.sum (u := Finset.univ.erase block)
    (fun sourceBlock member => fourPointExternalPointVelocity_hasFDerivAt (coefficients sourceBlock)
      (quadrupoleBlock positions sourceBlock) (noncollision sourceBlock (Finset.mem_erase.mp member).1))
  have identity : quadrupoleBlockExternalField coefficients positions block = fun current =>
      ∑ sourceBlock ∈ Finset.univ.erase block,
        fourPointExternalPointVelocity (coefficients sourceBlock) (quadrupoleBlock positions sourceBlock) current :=
    funext (quadrupoleBlockExternalField_source_sum coefficients positions block)
  rw [identity]
  convert derivative using 1
  ext increment
  simp [quadrupoleBlockExternalStrain, Finset.sum_mul]
  rw [sub_mul, Finset.sum_mul]

theorem quadrupoleBlockExternalField_fderiv_apply {count : ℕ} (coefficients : Fin count → ℝ)
    (positions : FiniteQuadrupoleConfiguration count) (block : Fin count) {location : ℂ}
    (noncollision : ∀ sourceBlock, sourceBlock ≠ block → ∀ source, location - positions (sourceBlock, source) ≠ 0)
    (increment : ℂ) :
    fderiv ℝ (quadrupoleBlockExternalField coefficients positions block) location increment =
      quadrupoleBlockExternalStrain coefficients positions block location * star increment := by
  rw [(quadrupoleBlockExternalField_hasFDerivAt coefficients positions block noncollision).fderiv]
  rfl

theorem quadrupoleBlockExternalField_contDiffAt {count : ℕ} (coefficients : Fin count → ℝ)
    (positions : FiniteQuadrupoleConfiguration count) (block : Fin count) {location : ℂ}
    (noncollision : ∀ sourceBlock, sourceBlock ≠ block → ∀ source, location - positions (sourceBlock, source) ≠ 0) :
    ContDiffAt ℝ 2 (quadrupoleBlockExternalField coefficients positions block) location := by
  have identity : quadrupoleBlockExternalField coefficients positions block = fun current =>
      ∑ sourceBlock ∈ Finset.univ.erase block,
        fourPointExternalPointVelocity (coefficients sourceBlock) (quadrupoleBlock positions sourceBlock) current :=
    funext (quadrupoleBlockExternalField_source_sum coefficients positions block)
  rw [identity]
  apply ContDiffAt.sum
  intro sourceBlock member
  exact fourPointExternalPointVelocity_contDiffAt (coefficients sourceBlock)
    (quadrupoleBlock positions sourceBlock) (noncollision sourceBlock (Finset.mem_erase.mp member).1)

end EulerNonuniqueness.Section6
