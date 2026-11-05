import EulerNonuniqueness.Section6.NegativeLabelBridge

noncomputable section

namespace EulerNonuniqueness.Section6

theorem relabelNegativePoints_forced_equation
    {trajectory : ℝ → FourPointConfiguration} {coefficient time : ℝ}
    {external : ℂ → ℂ} {residual : FourPointConfiguration}
    (equation : ∀ target, HasDerivAt (fun current => trajectory current target)
      (fourPointField coefficient (trajectory time) target +
        external (trajectory time target) + residual target) time) :
    ∀ target, HasDerivAt (fun current => relabelNegativePoints (trajectory current) target)
      (fourPointField coefficient (relabelNegativePoints (trajectory time)) target +
        external (relabelNegativePoints (trajectory time) target) +
        relabelNegativePoints residual target) time := by
  intro target
  have fieldIdentity := congrFun (fourPointField_negativeLabelSwap coefficient (trajectory time)) target
  rw [fieldIdentity]
  exact equation (negativeLabelSwap target)

theorem twoDipoleConfiguration_reconstruction (positions : FourPointConfiguration) :
    twoDipoleConfiguration ((positions 0 + positions 2) / 2) ((positions 1 + positions 3) / 2)
      (positions 0 - positions 2) (positions 1 - positions 3) = positions := by
  funext target
  fin_cases target <;> simp [twoDipoleConfiguration] <;> ring

end EulerNonuniqueness.Section6
