import EulerNonuniqueness.Section3.DiskSpectralRelativeNeutralUniform
import EulerNonuniqueness.Section3.DiskSpectralSelfBounds

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

local instance neutralVelocityBoundsC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskSpectralNeutralField_exists_eventual_quadratic_bound :
    ∃ constant ≥ 0, ∀ᶠ state in 𝓝 (0 : PeriodicC1HolderHalf),
      diskSpectralTubularArea state = Real.pi →
      ‖diskRelabelNeutralCLM (diskSpectralTubularEulerField state)‖ ≤
        constant * ‖diskPhysicalTransverseProjection state‖ ^ 2 := by
  obtain ⟨radius, positive, _, _, _, _, _, _, constant, nonnegative, bounds⟩ :=
    diskSpectral_exists_uniform_projected_self_bounds
  refine ⟨constant, nonnegative, ?_⟩
  let relative : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    ContinuousLinearMap.id ℝ PeriodicC1HolderHalf - diskRelabelNeutralCLM
  have absoluteContinuous : ContinuousAt (fun state => ‖diskRelabelNeutralCLM state‖ + ‖relative state‖)
      (0 : PeriodicC1HolderHalf) :=
    diskRelabelNeutralCLM.continuous.continuousAt.norm.add relative.continuous.continuousAt.norm
  have small : ∀ᶠ state in 𝓝 (0 : PeriodicC1HolderHalf),
      ‖diskRelabelNeutralCLM state‖ + ‖relative state‖ < radius :=
    absoluteContinuous.eventually (gt_mem_nhds (by simpa only [map_zero, norm_zero, zero_add] using positive))
  have transverseSmall : ∀ᶠ state in 𝓝 (0 : PeriodicC1HolderHalf), ‖diskPhysicalTransverseProjection state‖ < 1 :=
    diskPhysicalTransverseProjection.continuous.continuousAt.norm.eventually
      (gt_mem_nhds (by simp only [map_zero, norm_zero]; norm_num))
  filter_upwards [small, transverseSmall] with state inside transverse area
  exact (bounds state inside.le area).2.2.2 transverse.le

end

end EulerNonuniqueness.Paper
