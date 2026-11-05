import EulerNonuniqueness.General.MovingQuadraticDerivative
import EulerNonuniqueness.General.ProjectedQuadraticFamilyDerivative
import EulerNonuniqueness.General.CubicFiberCoefficient

namespace EulerNonuniqueness.General

noncomputable section

open Filter
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

attribute [local instance] cubicCoefficientEndGroup cubicCoefficientEndSpace
  cubicCoefficientBilinearGroup cubicCoefficientBilinearSpace

def frozenProjectedQuadraticVelocity
    (projection generator : Space →L[ℝ] Space)
    (quadratic correction : Space → BilinearEnd Space) (field : Space → Space)
    (state forcing : Space) : Space :=
  let value := projection state
  let remainder := projection (field state) - generator value - quadratic state value value + projection forcing
  generator (quadraticCoordinate (correction state) 1 value) +
    (remainder - (correction state (quadratic state value value + remainder) value +
      correction state value (quadratic state value value + remainder)))

theorem moving_projected_quadratic_family_eventually_hasDerivAt
    (projection neutral generator : Space →L[ℝ] Space)
    (quadratic correction : Space → BilinearEnd Space) (field : Space → Space)
    (homological : ∀ parameter, quadraticCommutator generator (correction parameter) = quadratic parameter)
    (neutralParameter : ∀ state, correction (neutral state) = correction state)
    (regular : ∀ᶠ state in 𝓝 (0 : Space), DifferentiableAt ℝ correction state) :
    ∀ᶠ state in 𝓝 (0 : Space),
    ∀ (trajectory : ℝ → Space) (time : ℝ) (forcing : Space),
    trajectory time = state → HasDerivAt trajectory (field state + forcing) time →
    HasDerivAt (fun current =>
      let value := projection (trajectory current)
      value - correction (neutral (trajectory current)) value value)
      (frozenProjectedQuadraticVelocity projection generator quadratic correction field state forcing -
        fderiv ℝ correction (neutral state) (neutral (field state + forcing))
          (projection state) (projection state)) time := by
  have continuousNeutral : Tendsto neutral (𝓝 (0 : Space)) (𝓝 0) := by
    simpa only [map_zero] using neutral.continuous.tendsto (0 : Space)
  filter_upwards [continuousNeutral.eventually regular] with state differentiable
  intro trajectory time forcing stateEquation equation
  subst state
  have projected : HasDerivAt (fun current => projection (trajectory current))
      (projection (field (trajectory time) + forcing)) time :=
    projection.hasFDerivAt.comp_hasDerivAt time equation
  have neutralEquation : HasDerivAt (fun current => neutral (trajectory current))
      (neutral (field (trajectory time) + forcing)) time :=
    neutral.hasFDerivAt.comp_hasDerivAt time equation
  have frozen := projected_quadratic_family_hasDerivAt projection generator quadratic correction field
    homological equation
  have frozenEquation : HasDerivAt (fun current => projection (trajectory current) -
      correction (neutral (trajectory time)) (projection (trajectory current)) (projection (trajectory current)))
      (frozenProjectedQuadraticVelocity projection generator quadratic correction field (trajectory time) forcing) time := by
    simpa only [neutralParameter, quadraticCoordinate, div_self (one_ne_zero : (1 : ℝ) ≠ 0), one_smul,
      frozenProjectedQuadraticVelocity] using frozen
  have coefficientDerivative : HasFDerivAt correction
      (fderiv ℝ correction (neutral (trajectory time))) (neutral (trajectory time)) :=
    differentiable.hasFDerivAt
  exact moving_quadratic_coordinate_hasDerivAt_of_frozen coefficientDerivative
    neutralEquation projected frozenEquation

end

end EulerNonuniqueness.General
