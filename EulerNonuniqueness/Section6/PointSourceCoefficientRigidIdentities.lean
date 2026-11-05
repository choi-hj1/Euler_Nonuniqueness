import EulerNonuniqueness.Section6.PointSourceRelativeCoefficient
import EulerNonuniqueness.Section6.NegativeLabelBridge

noncomputable section

namespace EulerNonuniqueness.Section6

theorem pointSourceTaylorCoefficient_translate
    (circulation receiverRadius : ℝ) (positions : FourPointConfiguration) (receiver center : ℂ) (power : ℕ) :
    pointSourceTaylorCoefficient circulation receiverRadius (fun patch => positions patch - center)
        (receiver - center) power =
      pointSourceTaylorCoefficient circulation receiverRadius positions receiver power := by
  simp only [pointSourceTaylorCoefficient, sub_sub_sub_cancel_right]

theorem pointSourceTaylorCoefficient_negativeLabelSwap
    (circulation receiverRadius : ℝ) (positions : FourPointConfiguration) (receiver : ℂ) (power : ℕ) :
    pointSourceTaylorCoefficient circulation receiverRadius (relabelNegativePoints positions) receiver power =
      pointSourceTaylorCoefficient circulation receiverRadius positions receiver power := by
  simp [pointSourceTaylorCoefficient, relabelNegativePoints, negativeLabelSwap,
    Equiv.swap_apply_def, fourPointSign, Fin.sum_univ_succ]
  ring <;> simp

end EulerNonuniqueness.Section6
