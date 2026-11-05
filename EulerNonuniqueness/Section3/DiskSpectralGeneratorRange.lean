import EulerNonuniqueness.Section3.DiskPhysicalSpectralGenerator

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance spectralGeneratorRangeC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

theorem diskPhysicalSpectralInverseDerivative_eventually_generator_range_neutral_zero :
    ∀ᶠ point in 𝓝 (0 : PeriodicC1HolderHalf), diskRelabelNeutralCLM point = point →
      ∀ preimage : PeriodicC1HolderHalf,
        diskRelabelNeutralCLM
          (diskPhysicalSpectralInverseDerivative (diskPhysicalSpectralChart point)
            (relabeledDiskDerivative (diskNeutralCLM point) preimage)) = 0 := by
  filter_upwards [diskPhysicalSpectralChart_eventually_generator_equivalence]
    with point equivalence neutral preimage
  obtain ⟨coordinates, _, inverseIdentity, intertwining⟩ := equivalence neutral
  rw [inverseIdentity]
  have actual := EulerNonuniqueness.General.inverse_intertwined_range_neutral_zero
      diskRelabelNeutralCLM diskRotatingDerivative (relabeledDiskDerivative (diskNeutralCLM point))
      coordinates diskRelabelNeutralCLM_rotatingDerivative_zero intertwining preimage
  simpa only [ContinuousLinearEquiv.coe_coe] using actual

end EulerNonuniqueness.Paper
