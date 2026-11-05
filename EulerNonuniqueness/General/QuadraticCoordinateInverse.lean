import EulerNonuniqueness.General.QuadraticCoordinateChange
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem quadraticCoordinate_hasStrictFDerivAt_zero
    (correction : BilinearEnd Space) (frequency : ℝ) :
    HasStrictFDerivAt (quadraticCoordinate correction frequency) (ContinuousLinearMap.id ℝ Space) 0 := by
  have quadratic := correction.hasStrictFDerivAt_of_bilinear
    (hasStrictFDerivAt_id (𝕜 := ℝ) (0 : Space)) (hasStrictFDerivAt_id (𝕜 := ℝ) (0 : Space))
  have changed := (hasStrictFDerivAt_id (𝕜 := ℝ) (0 : Space)).sub
    (quadratic.const_smul (1 / frequency : ℝ))
  change HasStrictFDerivAt (fun value : Space => value - (1 / frequency : ℝ) • correction value value)
    (ContinuousLinearMap.id ℝ Space) 0
  simpa [ContinuousLinearMap.precompR, ContinuousLinearMap.precompL] using changed

variable [CompleteSpace Space]

def quadraticCoordinatePartialHomeomorph (correction : BilinearEnd Space) (frequency : ℝ) :
    PartialHomeomorph Space Space :=
  (quadraticCoordinate_hasStrictFDerivAt_zero correction frequency).toPartialHomeomorph
    (quadraticCoordinate correction frequency) (f' := ContinuousLinearEquiv.refl ℝ Space)

theorem quadraticCoordinatePartialHomeomorph_zero_mem_source
    (correction : BilinearEnd Space) (frequency : ℝ) :
    (0 : Space) ∈ (quadraticCoordinatePartialHomeomorph correction frequency).source :=
  (quadraticCoordinate_hasStrictFDerivAt_zero correction frequency).mem_toPartialHomeomorph_source

theorem quadraticCoordinatePartialHomeomorph_apply
    (correction : BilinearEnd Space) (frequency : ℝ) (value : Space) :
    quadraticCoordinatePartialHomeomorph correction frequency value = quadraticCoordinate correction frequency value := rfl

theorem quadraticCoordinatePartialHomeomorph_left_inverse
    (correction : BilinearEnd Space) (frequency : ℝ) {value : Space}
    (inside : value ∈ (quadraticCoordinatePartialHomeomorph correction frequency).source) :
    (quadraticCoordinatePartialHomeomorph correction frequency).symm
      (quadraticCoordinate correction frequency value) = value :=
  (quadraticCoordinatePartialHomeomorph correction frequency).left_inv inside

end

end EulerNonuniqueness.General
