import EulerNonuniqueness.Section3.DiskPhysicalCoordinates

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance realGroupHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance realGroupC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

theorem periodicHilbertC1_real (density : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (density.val.1 label) = density.val.1 label) (label : ℝ) :
    star ((periodicHilbertC1 density).val.1 label) = (periodicHilbertC1 density).val.1 label :=
  periodicHilbertCLM_real (c1ValueHolder density) realValues label

theorem periodicMeanProjection_real (density : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (density.val.1 label) = density.val.1 label) (label : ℝ) :
    star ((periodicMeanProjectionCCLM density).val.1 label) =
      (periodicMeanProjectionCCLM density).val.1 label := by
  rw [periodicMeanProjectionCCLM_value]
  simp only [Complex.star_def, map_mul, Complex.conj_ofReal]
  congr 1
  simp only [intervalIntegral, map_sub, ← integral_conj]
  simp_rw [← Complex.star_def, realValues]

theorem periodicHilbertFlow_real (time : ℝ) (density : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (density.val.1 label) = density.val.1 label) (label : ℝ) :
    star ((periodicHilbertFlow time density).val.1 label) =
      (periodicHilbertFlow time density).val.1 label := by
  change star ((periodicMeanProjectionCCLM density).val.1 label +
    Real.cos (time / 2) • (density.val.1 label - (periodicMeanProjectionCCLM density).val.1 label) +
    (-Real.sin (time / 2)) • (periodicHilbertC1 density).val.1 label) = _
  simp only [star_add, star_sub, star_smul, star_trivial,
    periodicMeanProjection_real density realValues, realValues,
    periodicHilbertC1_real density realValues]
  rfl

theorem diskLinearFlow_real (time : ℝ) (radial angular : PeriodicC1HolderHalf)
    (radialReal : ∀ label, star (radial.val.1 label) = radial.val.1 label)
    (angularReal : ∀ label, star (angular.val.1 label) = angular.val.1 label) :
    (∀ label, star ((diskLinearFlow time radial angular).1.val.1 label) =
      (diskLinearFlow time radial angular).1.val.1 label) ∧
    (∀ label, star ((diskLinearFlow time radial angular).2.val.1 label) =
      (diskLinearFlow time radial angular).2.val.1 label) := by
  constructor
  · exact periodicHilbertFlow_real time radial radialReal
  · intro label
    change star (angular.val.1 label + (periodicHilbertC1 radial).val.1 label -
      (periodicHilbertC1 (periodicHilbertFlow time radial)).val.1 label) = _
    rw [star_sub, star_add, angularReal,
      periodicHilbertC1_real radial radialReal,
      periodicHilbertC1_real _ (periodicHilbertFlow_real time radial radialReal)]
    rfl

end

end EulerNonuniqueness.Paper
