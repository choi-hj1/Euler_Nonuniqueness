import EulerNonuniqueness.General.MovingQuadraticForcingSplit
import EulerNonuniqueness.General.ScaledQuadraticFamilyDerivative

namespace EulerNonuniqueness.General

noncomputable section

open Filter
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

attribute [local instance] cubicCoefficientEndGroup cubicCoefficientEndSpace
  cubicCoefficientBilinearGroup cubicCoefficientBilinearSpace

theorem frozenProjectedQuadraticVelocity_self_smul
    (projection generator : Space →L[ℝ] Space)
    (quadratic correction : Space → BilinearEnd Space) (field : Space → Space)
    (frequency : ℝ) (state : Space) :
    frozenProjectedQuadraticVelocity projection (frequency • generator)
      (fun parameter => frequency • quadratic parameter) correction
      (fun parameter => frequency • field parameter) state 0 =
      frequency • frozenProjectedQuadraticVelocity projection generator quadratic correction field state 0 := by
  simp only [frozenProjectedQuadraticVelocity, ContinuousLinearMap.smul_apply,
    map_smul, map_zero, add_zero, smul_sub, smul_add, map_add, map_sub,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]

theorem moving_projected_quadratic_scaled_eventually_hasDerivAt
    (projection neutral generator : Space →L[ℝ] Space)
    (quadratic correction : Space → BilinearEnd Space) (field : Space → Space)
    (homological : ∀ parameter, quadraticCommutator generator (correction parameter) = quadratic parameter)
    (neutralParameter : ∀ state, correction (neutral state) = correction state)
    (regular : ∀ᶠ state in 𝓝 (0 : Space), DifferentiableAt ℝ correction state)
    (frequency : ℝ) :
    ∀ᶠ state in 𝓝 (0 : Space),
    ∀ (trajectory : ℝ → Space) (time : ℝ) (forcing : Space),
    trajectory time = state → HasDerivAt trajectory (frequency • field state + forcing) time →
    HasDerivAt (fun current =>
      let value := projection (trajectory current)
      value - correction (neutral (trajectory current)) value value)
      (frequency • (frozenProjectedQuadraticVelocity projection generator quadratic correction field state 0 -
          fderiv ℝ correction (neutral state) (neutral (field state)) (projection state) (projection state)) +
        (projection forcing - (correction state (projection forcing) (projection state) +
          correction state (projection state) (projection forcing)) -
          fderiv ℝ correction (neutral state) (neutral forcing) (projection state) (projection state))) time := by
  have scaledHomological : ∀ parameter, quadraticCommutator (frequency • generator) (correction parameter) =
      frequency • quadratic parameter := by
    intro parameter
    rw [quadraticCommutator_generator_smul, homological]
  have actual := moving_projected_quadratic_family_eventually_hasDerivAt projection neutral (frequency • generator)
    (fun parameter => frequency • quadratic parameter) correction (fun parameter => frequency • field parameter)
    scaledHomological neutralParameter regular
  filter_upwards [actual] with state derivative
  intro trajectory time forcing stateEquation equation
  apply (derivative trajectory time forcing stateEquation equation).congr_deriv
  rw [movingProjectedQuadraticVelocity_forcing_split, frozenProjectedQuadraticVelocity_self_smul]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_sub]

end

end EulerNonuniqueness.General
