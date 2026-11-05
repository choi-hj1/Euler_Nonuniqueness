import EulerNonuniqueness.Section3.ContourVelocityFrechet

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance derivativeValueHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance derivativeValueC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem contourVelocityHolderDerivativeCLM_value (data direction : PeriodicC1HolderHalf) {radius : ℝ}
    (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) (target : ℝ) :
    (contourVelocityHolderDerivativeCLM data near small direction).val.1 target =
      Complex.I / 4 * direction.val.1 target - (1 / (4 * Real.pi) : ℂ) * star
        ((contourCauchyDirectionalDerivative data direction (holderConjugate (c1ValueHolder data))).val.1 target +
          (contourCauchyOperatorCLM data (near.trans small) (holderConjugate (c1ValueHolder direction))).val.1 target) := rfl

theorem fderiv_extendedContourVelocity_value (data direction : PeriodicC1HolderHalf) {radius : ℝ}
    (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) (target : ℝ) :
    (fderiv ℝ extendedContourVelocity data direction).val.1 target =
      (contourVelocityHolderDerivativeCLM data near small direction).val.1 target := by
  have actual : HasFDerivAt extendedContourVelocity (fderiv ℝ extendedContourVelocity data) data :=
    DifferentiableAt.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
      (differentiableAt_extendedContourVelocity data (near.trans small))
  have composed : HasFDerivAt (fun current : PeriodicC1HolderHalf => c1ValueHolder (extendedContourVelocity current))
      (c1ValueHolderRealCLM.comp (fderiv ℝ extendedContourVelocity data)) data := by
    exact HasFDerivAt.comp (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (G := PeriodicHolderHalf)
      (f := extendedContourVelocity) (f' := fderiv ℝ extendedContourVelocity data)
      (g := c1ValueHolder) (g' := c1ValueHolderRealCLM) data
      (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) c1ValueHolderRealCLM) actual
  have equality : holderContourVelocity =ᶠ[𝓝 data]
      (fun current : PeriodicC1HolderHalf => c1ValueHolder (extendedContourVelocity current)) := by
    have positive : 0 < radius - ‖data - standardCircleBanach‖ := sub_pos.mpr near
    filter_upwards [Metric.ball_mem_nhds data positive] with current member
    rw [mem_ball, dist_eq_norm current data] at member
    have triangle := dist_triangle current data standardCircleBanach
    rw [dist_eq_norm current standardCircleBanach, dist_eq_norm current data,
      dist_eq_norm data standardCircleBanach] at triangle
    have current_near : ‖current - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by linarith
    apply PeriodicHolderHalf.ext_value
    intro label
    rw [extendedContourVelocity_eq current current_near]
    exact holderContourVelocity_value current current_near label
  have composed_equal : HasFDerivAt holderContourVelocity
      (c1ValueHolderRealCLM.comp (fderiv ℝ extendedContourVelocity data)) data := by
    exact HasFDerivAt.congr_of_eventuallyEq (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) composed equality
  have holder : HasFDerivAt holderContourVelocity (contourVelocityHolderDerivativeCLM data near small) data := by
    exact hasFDerivAt_holderContourVelocity data near small
  have operators := HasFDerivAt.unique (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) composed_equal holder
  exact congrArg (fun operator : PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf => (operator direction).val.1 target) operators

end

end EulerNonuniqueness.Paper
