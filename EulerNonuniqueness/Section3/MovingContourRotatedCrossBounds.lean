import EulerNonuniqueness.Section3.MovingContourCrossFieldBounds

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingRotatedCrossHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingRotatedCrossC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem complexSMulC1_norm (scalar : ℂ) (data : PeriodicC1HolderHalf) :
    ‖scalar • data‖ = ‖scalar‖ * ‖data‖ := by
  change ‖scalar • data.val‖ = _
  exact norm_smul scalar data.val

def FiniteContourConfiguration.movingCrossNormBound {count : ℕ}
    (configuration : FiniteContourConfiguration count) (centerBound gap : ℝ) : ℝ :=
  4 * crossContourPhaseBound (configuration.movingPhysicalUniformBound centerBound) gap *
    configuration.movingPhysicalUniformBound centerBound

def FiniteContourConfiguration.movingCrossLipschitzBound {count : ℕ}
    (configuration : FiniteContourConfiguration count) (centerBound gap : ℝ) (target source : Fin count) : ℝ :=
  (crossContourIntegrandLipschitzBound (configuration.movingPhysicalUniformBound centerBound) gap / 2) *
    (configuration.movingPhysicalLipschitzConstant target + configuration.movingPhysicalLipschitzConstant source)

def FiniteContourConfiguration.movingRotatedCrossField {count : ℕ}
    (configuration : FiniteContourConfiguration count) (state : MovingContourState count) (target source : Fin count) :
    PeriodicC1HolderHalf :=
  (((configuration.movingStatePhase state target)⁻¹ : Circle) : ℂ) •
    extendedCrossContourVelocity (configuration.movingStatePhysicalContour state target)
      (configuration.movingStatePhysicalContour state source)

theorem FiniteContourConfiguration.movingRotatedCrossField_uniform_norm_bound {count : ℕ}
    (configuration : FiniteContourConfiguration count) {centerBound shapeRadius gap : ℝ}
    (positive : 0 < gap) (shapeSmall : shapeRadius ≤ 1) {state : MovingContourState count}
    (inside : state ∈ configuration.movingStateAdmissible centerBound shapeRadius gap)
    (target source : Fin count) (distinct : target ≠ source) :
    ‖configuration.movingRotatedCrossField state target source‖ ≤ configuration.movingCrossNormBound centerBound gap := by
  rw [FiniteContourConfiguration.movingRotatedCrossField, unitRotationC1_norm]
  exact configuration.movingCross_uniform_norm_bound positive shapeSmall inside target source distinct

theorem FiniteContourConfiguration.movingRotatedCrossField_parameter_norm_bound {count : ℕ}
    (configuration : FiniteContourConfiguration count) {centerBound shapeRadius gap : ℝ}
    (positive : 0 < gap) (centerNonnegative : 0 ≤ centerBound) (shapeSmall : shapeRadius ≤ 1)
    {first second : MovingContourState count}
    (firstInside : first ∈ configuration.movingStateAdmissible centerBound shapeRadius gap)
    (secondInside : second ∈ configuration.movingStateAdmissible centerBound shapeRadius gap)
    (target source : Fin count) (distinct : target ≠ source) :
    ‖configuration.movingRotatedCrossField first target source - configuration.movingRotatedCrossField second target source‖ ≤
      (configuration.movingCrossLipschitzBound centerBound gap target source +
        |configuration.density target / 2| * configuration.movingCrossNormBound centerBound gap) * ‖first - second‖ := by
  have actual := unitRotationC1_parameter_norm_bound
    ((configuration.movingStatePhase first target)⁻¹) ((configuration.movingStatePhase second target)⁻¹)
    (extendedCrossContourVelocity (configuration.movingStatePhysicalContour first target) (configuration.movingStatePhysicalContour first source))
    (extendedCrossContourVelocity (configuration.movingStatePhysicalContour second target) (configuration.movingStatePhysicalContour second source))
  have phaseBound := configuration.movingStateInversePhase_parameter_norm_bound first second target
  have fieldBound := configuration.movingCross_uniform_norm_bound positive shapeSmall secondInside target source distinct
  have fieldDifference := configuration.movingCross_parameter_norm_bound positive centerNonnegative shapeSmall
    firstInside secondInside target source distinct
  have productBound := mul_le_mul phaseBound fieldBound (norm_nonneg _) (by positivity)
  change ‖configuration.movingRotatedCrossField first target source - configuration.movingRotatedCrossField second target source‖ ≤ _ at actual
  apply actual.trans
  apply (add_le_add fieldDifference productBound).trans_eq
  unfold FiniteContourConfiguration.movingCrossLipschitzBound FiniteContourConfiguration.movingCrossNormBound
  ring

end EulerNonuniqueness.Paper
