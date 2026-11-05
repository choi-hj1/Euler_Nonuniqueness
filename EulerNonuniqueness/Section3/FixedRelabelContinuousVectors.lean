import EulerNonuniqueness.Section3.ContourContinuousComposition
import EulerNonuniqueness.Section3.FixedRelabelEquivalence

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] continuousFourierC1Group holderContinuousRealSpace
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem periodicForwardLabelMap_slope_mem (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (member : angular ∈ contourContinuousVectorSubmodule) :
    (periodicForwardLabelMap angular small).slopeHolder ∈ holderContinuousVectorSubmodule := by
  have tangentMember := contourContinuousVector_tangent angular member
  have realMember := holderContinuousVectorSubmodule_realPart angular.val.2 tangentMember
  have constantMember := c1ValueHolder_mem_holderContinuousVectorSubmodule (c1Constant 1)
  have identity : (periodicForwardLabelMap angular small).slopeHolder =
      c1ValueHolder (c1Constant 1) + holderRealPart angular.val.2 := by
    apply PeriodicHolderHalf.ext_value
    intro label
    rw [PeriodicC1LabelMap.slopeHolder_value]
    change ((periodicLabelSlope angular label : ℝ) : ℂ) = 1 + (holderRealPart angular.val.2).val.1 label
    rw [holderRealPart_coe_re_value]
    simp only [periodicLabelSlope, Complex.ofReal_add, Complex.ofReal_one]
  rw [identity]
  exact holderContinuousVectorSubmodule.add_mem constantMember realMember

theorem periodicInverseLabelMap_slope_mem (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (member : angular ∈ contourContinuousVectorSubmodule) :
    (periodicInverseLabelMap angular small).slopeHolder ∈ holderContinuousVectorSubmodule := by
  let density := (periodicInverseLabelMap angular small).composeHolderCLM
    (periodicForwardLabelMap angular small).slopeHolder
  have densityMember : density ∈ holderContinuousVectorSubmodule :=
    (periodicInverseLabelMap angular small).composeHolder_mem_continuousVector _
      (periodicForwardLabelMap_slope_mem angular small member)
  have lower (label : ℝ) : (1 / 2 : ℝ) ≤ ‖density.val.1 label‖ := by
    change (1 / 2 : ℝ) ≤ ‖((periodicLabelSlope angular
      ((periodicLabelHomeomorph angular (small.trans (by norm_num))).symm label) : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs]
    have estimate := periodicLabelSlope_lower angular
      ((periodicLabelHomeomorph angular (small.trans (by norm_num))).symm label)
    have positive : 0 ≤ periodicLabelSlope angular
        ((periodicLabelHomeomorph angular (small.trans (by norm_num))).symm label) := by linarith
    rw [abs_of_nonneg positive]
    linarith
  have inverseMember := holderContinuousVectorSubmodule_inverse density densityMember (by norm_num : (0 : ℝ) < 1 / 2) lower
  have identity : (periodicInverseLabelMap angular small).slopeHolder = extendedHolderInverse density := by
    rw [extendedHolderInverse_eq density (by norm_num : (0 : ℝ) < 1 / 2) lower]
    apply PeriodicHolderHalf.ext_value
    intro label
    change (((periodicLabelSlope angular
      ((periodicLabelHomeomorph angular (small.trans (by norm_num))).symm label))⁻¹ : ℝ) : ℂ) =
      (((periodicLabelSlope angular
        ((periodicLabelHomeomorph angular (small.trans (by norm_num))).symm label)) : ℝ) : ℂ)⁻¹
    simp only [Complex.ofReal_inv]
  rw [identity]
  exact inverseMember

theorem fixedRelabelEquivalence_mem_continuousVector (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (angularMember : angular ∈ contourContinuousVectorSubmodule) (data : PeriodicC1HolderHalf)
    (member : data ∈ contourContinuousVectorSubmodule) :
    fixedRelabelEquivalence angular small data ∈ contourContinuousVectorSubmodule := by
  exact (periodicForwardLabelMap angular small).composeCLM_mem_continuousVector
    (periodicForwardLabelMap_slope_mem angular small angularMember) data member

theorem fixedRelabelEquivalence_symm_mem_continuousVector (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (angularMember : angular ∈ contourContinuousVectorSubmodule) (data : PeriodicC1HolderHalf)
    (member : data ∈ contourContinuousVectorSubmodule) :
    (fixedRelabelEquivalence angular small).symm data ∈ contourContinuousVectorSubmodule := by
  exact (periodicInverseLabelMap angular small).composeCLM_mem_continuousVector
    (periodicInverseLabelMap_slope_mem angular small angularMember) data member

end EulerNonuniqueness.Paper
