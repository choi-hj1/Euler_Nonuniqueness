import EulerNonuniqueness.Section3.DiskForcingPrimitive
import EulerNonuniqueness.Section3.DiskPhysicalRateGroup

namespace EulerNonuniqueness.Paper

noncomputable section

open MeasureTheory Set

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  physicalGeneratorC1ContinuousAdd physicalGeneratorC1UniformAdd

local instance forcingResponseC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

local instance forcingResponseTopologicalAdd : IsTopologicalAddGroup PeriodicC1HolderHalf :=
  IsUniformAddGroup.to_topologicalAddGroup

local instance forcingResponseComplexBoundedSMul : IsBoundedSMul ℂ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℂ) (E := PeriodicC1HolderHalf)

theorem diskForcingPrimitive_response_bound (degree : ℕ) {frequency horizon time : ℝ}
    (nonzero : frequency ≠ 0) {amplitude amplitudeDerivative : ℝ → ℂ}
    {trajectory : ℝ → PeriodicC1HolderHalf}
    (amplitudeEquation : ∀ current ∈ Icc 0 horizon,
      HasDerivAt amplitude (amplitudeDerivative current) current)
    (derivativeContinuous : ContinuousOn amplitudeDerivative (Icc 0 horizon))
    (equation : ∀ current ∈ Icc 0 horizon,
      HasDerivAt trajectory (frequency • diskRotatingDerivative (trajectory current) +
        (amplitude current * diskForcingPhase degree frequency current) •
          c1Conjugate (diskCircleMode (degree + 1))) current)
    (inside : time ∈ Icc 0 horizon) :
    ‖trajectory time‖ ≤ ‖diskForcingPrimitive degree frequency amplitude time‖ +
      diskPhysicalGroupBound * (‖trajectory 0 - diskForcingPrimitive degree frequency amplitude 0‖ +
        ∫ current in (0 : ℝ)..time,
          ‖diskForcingPrimitive degree frequency amplitudeDerivative current‖) := by
  let primitive := diskForcingPrimitive degree frequency amplitude
  let residual := diskForcingPrimitive degree frequency amplitudeDerivative
  let corrected := fun current => trajectory current - primitive current
  have primitiveEquation (current : ℝ) (member : current ∈ Icc 0 horizon) :
      HasDerivAt primitive (frequency • diskRotatingDerivative (primitive current) +
        (amplitude current * diskForcingPhase degree frequency current) •
          c1Conjugate (diskCircleMode (degree + 1)) + residual current) current :=
    diskForcingPrimitive_hasDerivAt degree nonzero (amplitudeEquation current member)
  have phaseContinuous : Continuous (diskForcingPhase degree frequency) :=
    continuous_iff_continuousAt.mpr (fun current => (diskForcingPhase_hasDerivAt degree frequency current).continuousAt)
  have amplitudeContinuous : ContinuousOn amplitude (Icc 0 horizon) :=
    fun current member => (amplitudeEquation current member).continuousAt.continuousWithinAt
  have primitiveContinuous : ContinuousOn primitive (Icc 0 horizon) := by
    exact ((continuousOn_const.mul amplitudeContinuous).mul phaseContinuous.continuousOn).smul continuousOn_const
  have trajectoryContinuous : ContinuousOn trajectory (Icc 0 horizon) := by
    intro current member
    have actual : ContinuousAt trajectory current := by
      with_reducible
        exact HasDerivAt.continuousAt (𝕜 := ℝ) (F := PeriodicC1HolderHalf)
          (f := trajectory) (x := current) (equation current member)
    exact actual.continuousWithinAt
  have residualContinuous : ContinuousOn residual (Icc 0 horizon) := by
    exact ((continuousOn_const.mul derivativeContinuous).mul phaseContinuous.continuousOn).smul continuousOn_const
  have correctedEquation (current : ℝ) (member : current ∈ Icc 0 horizon) :
      HasDerivAt corrected ((frequency • diskRotatingDerivative) (corrected current) + -residual current) current := by
    have actual := HasDerivAt.sub (𝕜 := ℝ) (F := PeriodicC1HolderHalf)
      (equation current member) (primitiveEquation current member)
    convert actual using 1
    change frequency • diskRotatingDerivative (trajectory current - primitive current) - residual current = _
    rw [map_sub, smul_sub]
    abel
  have bound := diskPhysicalRateGroup_response_bound frequency
    (trajectoryContinuous.sub primitiveContinuous) residualContinuous.neg correctedEquation inside
  simp only [norm_neg] at bound
  calc
    ‖trajectory time‖ ≤ ‖primitive time‖ + ‖corrected time‖ := by
      have identity : trajectory time = primitive time + corrected time := by dsimp only [corrected]; abel
      rw [identity]
      exact norm_add_le (primitive time) (corrected time)
    _ ≤ _ := add_le_add_left bound _

end

end EulerNonuniqueness.Paper
