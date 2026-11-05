import EulerNonuniqueness.Section3.HolderBanachModel

open Set MeasureTheory
open scoped BoundedContinuousFunction

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

def complexPeriodicHolderGraph : Submodule ℂ HolderGraphAmbient where
  carrier := periodicHolderGraph
  zero_mem' := periodicHolderGraph.zero_mem
  add_mem' := periodicHolderGraph.add_mem
  smul_mem' := by
    intro scalar data membership
    constructor
    · intro pair
      change (Real.sqrt |pair.val.1 - pair.val.2| : ℂ) * (scalar * data.2 pair) =
        scalar * data.1 pair.val.1 - scalar * data.1 pair.val.2
      rw [← mul_assoc, mul_comm _ scalar, mul_assoc, membership.1 pair, mul_sub]
    · intro label
      change scalar * data.1 _ = scalar * data.1 _
      rw [membership.2 label]

instance complexHolderNormedSpace : NormedSpace ℂ PeriodicHolderHalf :=
  Submodule.normedSpace complexPeriodicHolderGraph

theorem complexHolder_smul_value (scalar : ℂ) (data : PeriodicHolderHalf) (label : ℝ) :
    (scalar • data).val.1 label = scalar * data.val.1 label := rfl

def complexPeriodicC1HolderGraph : Submodule ℂ C1HolderGraphAmbient where
  carrier := periodicC1HolderGraph
  zero_mem' := periodicC1HolderGraph.zero_mem
  add_mem' := periodicC1HolderGraph.add_mem
  smul_mem' := by
    intro scalar data membership
    constructor
    · intro label
      change scalar * data.1 label - scalar * data.1 0 =
        ∫ source in (0 : ℝ)..label, scalar • data.2.val.1 source
      rw [intervalIntegral.integral_smul]
      change scalar * data.1 label - scalar * data.1 0 =
        scalar * boundedIntervalIntegral 0 label data.2.val.1
      rw [← membership.1 label, mul_sub]
    · intro label
      change scalar * data.1 _ = scalar * data.1 _
      rw [membership.2 label]

instance complexC1HolderNormedSpace : NormedSpace ℂ PeriodicC1HolderHalf :=
  Submodule.normedSpace complexPeriodicC1HolderGraph

theorem complexC1Holder_smul_value (scalar : ℂ) (data : PeriodicC1HolderHalf) (label : ℝ) :
    (scalar • data).val.1 label = scalar * data.val.1 label := rfl

theorem complexC1Holder_smul_tangent (scalar : ℂ) (data : PeriodicC1HolderHalf) (label : ℝ) :
    (scalar • data).val.2.val.1 label = scalar * data.val.2.val.1 label := rfl

instance complexHolderScalarTower : IsScalarTower ℝ ℂ PeriodicHolderHalf where
  smul_assoc real_scalar complex_scalar data := by
    apply PeriodicHolderHalf.ext_value
    intro label
    change (real_scalar • complex_scalar) * data.val.1 label = real_scalar • (complex_scalar * data.val.1 label)
    exact smul_mul_assoc real_scalar complex_scalar _

instance complexC1HolderScalarTower : IsScalarTower ℝ ℂ PeriodicC1HolderHalf where
  smul_assoc real_scalar complex_scalar data := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change (real_scalar • complex_scalar) * data.val.1 label = real_scalar • (complex_scalar * data.val.1 label)
    exact smul_mul_assoc real_scalar complex_scalar _

end

end EulerNonuniqueness.Paper
