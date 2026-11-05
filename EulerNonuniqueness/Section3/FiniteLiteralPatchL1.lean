import EulerNonuniqueness.Section3.FiniteLiteralPatchArea
import EulerNonuniqueness.Section3.FiniteLiteralPatchMeasurability
import EulerNonuniqueness.Section3.IndicatorL1Continuity

open Set MeasureTheory Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

namespace FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem domain_persistence (flow : FiniteLiteralPatchFlow configuration) (time : ℝ)
    (index : Fin count) (position : ℂ) (member : position ∈ flow.domain time index) :
    ∀ᶠ parameter in 𝓝 time, position ∈ flow.domain parameter index := by
  let normalized := (contourAffineHomeomorph (configuration.center index)
    (configuration.radius_pos index)).symm position
  let small := fun parameter => (flow.nearby parameter index).trans_le (min_le_left _ _)
  have profile_continuous := (continuous_nearCircleRadialProfile_joint
    (fun parameter => flow.shape parameter index) ((continuous_apply index).comp flow.continuous) small).comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => Complex.arg normalized)))
  have strict : ‖normalized‖ < nearCircleRadialProfile (flow.shape time index) (small time)
      (Complex.arg normalized) := by
    exact (affinePatchDomain_mem_iff (configuration.center index) (configuration.radius_pos index)
      (flow.shape time index) (small time) position).mp member
  have eventual := (isOpen_lt continuous_const profile_continuous).mem_nhds strict
  filter_upwards [eventual] with parameter inequality
  exact (affinePatchDomain_mem_iff (configuration.center index) (configuration.radius_pos index)
    (flow.shape parameter index) (small parameter) position).mpr inequality

theorem tendsto_integral_norm_domain_indicator_sub (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) :
    Tendsto (fun parameter => ∫ position,
      ‖(flow.domain parameter index).indicator (fun _ => (1 : ℝ)) position -
        (flow.domain time index).indicator (fun _ => (1 : ℝ)) position‖) (𝓝 time) (𝓝 0) := by
  apply tendsto_integral_norm_indicator_sub_of_persistence (fun parameter => flow.domain parameter index) time
    (fun parameter => (flow.domain_isOpen parameter index).measurableSet)
    (fun parameter => (flow.domain_isBounded parameter index).measure_lt_top.ne)
    (flow.domain_persistence time index)
  filter_upwards [isOpen_Ioo.mem_nhds inside] with parameter member
  rw [flow.domain_area member index, flow.domain_area inside index]

end FiniteLiteralPatchFlow

end

end EulerNonuniqueness.Paper
