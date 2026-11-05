import EulerNonuniqueness.General.QuadraticCoordinateInverse
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace EulerNonuniqueness.General

open scoped ContDiff

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem quadraticCoordinate_contDiff (correction : BilinearEnd Space) (frequency : ℝ) :
    ContDiff ℝ ∞ (quadraticCoordinate correction frequency) := by
  change ContDiff ℝ ∞ (fun value : Space => value - (1 / frequency : ℝ) • correction value value)
  exact contDiff_id.sub ((correction.contDiff.clm_apply contDiff_id).const_smul (1 / frequency : ℝ))

variable [CompleteSpace Space]

theorem quadraticCoordinate_inverse_contDiffAt_zero (correction : BilinearEnd Space) (frequency : ℝ) :
    ContDiffAt ℝ ∞ (quadraticCoordinatePartialHomeomorph correction frequency).symm (0 : Space) := by
  have derivative := quadraticCoordinate_hasStrictFDerivAt_zero correction frequency
  have target : (0 : Space) ∈ (quadraticCoordinatePartialHomeomorph correction frequency).target := by
    simpa [quadraticCoordinatePartialHomeomorph_apply, quadraticCoordinate] using
      (quadraticCoordinatePartialHomeomorph correction frequency).map_source
        (quadraticCoordinatePartialHomeomorph_zero_mem_source correction frequency)
  have inverseZero : (quadraticCoordinatePartialHomeomorph correction frequency).symm (0 : Space) = 0 := by
    simpa [quadraticCoordinate] using quadraticCoordinatePartialHomeomorph_left_inverse correction frequency
      (quadraticCoordinatePartialHomeomorph_zero_mem_source correction frequency)
  apply (quadraticCoordinatePartialHomeomorph correction frequency).contDiffAt_symm target
    (f₀' := ContinuousLinearEquiv.refl ℝ Space)
  · rw [inverseZero]
    simpa only [quadraticCoordinatePartialHomeomorph, HasStrictFDerivAt.toPartialHomeomorph_coe] using derivative.hasFDerivAt
  · rw [inverseZero]
    simpa only [quadraticCoordinatePartialHomeomorph, HasStrictFDerivAt.toPartialHomeomorph_coe] using
      (quadraticCoordinate_contDiff correction frequency).contDiffAt (x := (0 : Space))

end

end EulerNonuniqueness.General
