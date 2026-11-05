import EulerNonuniqueness.Section3.MovingSimilarityPullback
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

namespace EulerNonuniqueness.Paper

theorem circle_rotation_lipschitz (frequency : ℝ) :
    LipschitzWith ⟨|frequency|, abs_nonneg frequency⟩ (fun time : ℝ => (Circle.exp (frequency * time) : ℂ)) := by
  have derivative (time : ℝ) : HasDerivAt (fun current : ℝ => (Circle.exp (frequency * current) : ℂ))
      ((Complex.I * (frequency : ℂ)) * (Circle.exp (frequency * time) : ℂ)) time := by
    apply hasDerivAt_circle_phase
    simpa only [id_eq, mul_one] using (hasDerivAt_id time).const_mul frequency
  apply lipschitzWith_of_nnnorm_deriv_le (fun time => (derivative time).differentiableAt)
  intro time
  apply NNReal.coe_le_coe.mp
  rw [NNReal.coe_mk, coe_nnnorm, (derivative time).deriv,
    norm_mul, norm_mul, Complex.norm_I, Circle.norm_coe, one_mul, mul_one, Complex.norm_real, Real.norm_eq_abs]

end EulerNonuniqueness.Paper
