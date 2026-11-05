import EulerNonuniqueness.Section3.DiskForcingPrimitive
import Mathlib.Analysis.Complex.Circle

namespace EulerNonuniqueness.Paper

noncomputable section

theorem diskForcingPhase_eq_rotation_power (degree : ℕ) (frequency time : ℝ) :
    (((Circle.exp (frequency * time / 2) : Circle) : ℂ)⁻¹) ^ (degree + 2) =
      diskForcingPhase degree frequency time := by
  rw [Circle.coe_exp, ← Complex.exp_neg, ← Complex.exp_nat_mul]
  unfold diskForcingPhase
  congr 1
  push_cast
  ring

end

end EulerNonuniqueness.Paper
