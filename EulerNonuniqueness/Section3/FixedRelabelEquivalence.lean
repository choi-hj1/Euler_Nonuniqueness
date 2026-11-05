import EulerNonuniqueness.Section3.PeriodicLabelMaps
import EulerNonuniqueness.Section3.StationaryRelabelCurve

noncomputable section

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance fixedRelabelEquivalenceRealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

def fixedRelabelEquivalence (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2) :
    PeriodicC1HolderHalf ≃L[ℝ] PeriodicC1HolderHalf :=
  ContinuousLinearEquiv.equivOfInverse (periodicForwardLabelMap angular small).composeCLM
    (periodicInverseLabelMap angular small).composeCLM
    (fun data => by
      apply PeriodicC1HolderHalf.ext_value
      intro label
      change data.val.1 (periodicLabelHomeomorph angular (small.trans (by norm_num))
        ((periodicLabelHomeomorph angular (small.trans (by norm_num))).symm label)) = data.val.1 label
      rw [(periodicLabelHomeomorph angular (small.trans (by norm_num))).apply_symm_apply])
    (fun data => by
      apply PeriodicC1HolderHalf.ext_value
      intro label
      change data.val.1 ((periodicLabelHomeomorph angular (small.trans (by norm_num))).symm
        (periodicLabelHomeomorph angular (small.trans (by norm_num)) label)) = data.val.1 label
      rw [(periodicLabelHomeomorph angular (small.trans (by norm_num))).symm_apply_apply])

theorem fixedRelabelEquivalence_value (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (data : PeriodicC1HolderHalf) (label : ℝ) :
    (fixedRelabelEquivalence angular small data).val.1 label = data.val.1 (periodicLabelShift angular label) := rfl

theorem fixedRelabelEquivalence_tangent (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (data : PeriodicC1HolderHalf) (label : ℝ) :
    (fixedRelabelEquivalence angular small data).val.2.val.1 label =
      (periodicLabelSlope angular label : ℂ) * data.val.2.val.1 (periodicLabelShift angular label) := rfl

theorem fixedRelabelEquivalence_symm_value (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (data : PeriodicC1HolderHalf) (label : ℝ) :
    ((fixedRelabelEquivalence angular small).symm data).val.1 label =
      data.val.1 ((periodicLabelHomeomorph angular (small.trans (by norm_num))).symm label) := rfl

theorem fixedRelabelEquivalence_norm_bound (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (data : PeriodicC1HolderHalf) : ‖fixedRelabelEquivalence angular small data‖ ≤ 8 * ‖data‖ := by
  have bound := (periodicForwardLabelMap angular small).compose_norm_bound data
  have root : Real.sqrt (2 : ℝ) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have coefficient : (periodicForwardLabelMap angular small).operatorBound ≤ 8 := by
    dsimp only [PeriodicC1LabelMap.operatorBound, periodicForwardLabelMap]
    linarith
  exact bound.trans (mul_le_mul_of_nonneg_right coefficient (norm_nonneg data))

theorem fixedRelabelEquivalence_symm_norm_bound (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (data : PeriodicC1HolderHalf) : ‖(fixedRelabelEquivalence angular small).symm data‖ ≤ 12 * ‖data‖ := by
  have bound := (periodicInverseLabelMap angular small).compose_norm_bound data
  have root : Real.sqrt (2 : ℝ) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have coefficient : (periodicInverseLabelMap angular small).operatorBound ≤ 12 := by
    dsimp only [PeriodicC1LabelMap.operatorBound, periodicInverseLabelMap]
    linarith
  exact bound.trans (mul_le_mul_of_nonneg_right coefficient (norm_nonneg data))

theorem fixedRelabelEquivalence_complex_smul (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (scalar : ℂ) (data : PeriodicC1HolderHalf) :
    fixedRelabelEquivalence angular small (scalar • data) = scalar • fixedRelabelEquivalence angular small data := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rfl

theorem fixedRelabelEquivalence_circle (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label) :
    fixedRelabelEquivalence angular small standardCircleBanach = diskRelabelCurve angular 1 := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  have imaginaryZero : (angular.val.1 label).im = 0 := by
    have imaginary := congrArg Complex.im (realValues label)
    simp only [Complex.star_def, Complex.conj_im] at imaginary
    linarith
  have realIdentity : angular.val.1 label = ((angular.val.1 label).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using imaginaryZero
  rw [fixedRelabelEquivalence_value, diskRelabelCurve_value]
  change standardCircle (label + (angular.val.1 label).re) = _
  rw [standardCircle_add, realIdentity]
  simp only [Complex.ofReal_one, one_mul, standardCircle, Complex.ofReal_re,
    mul_comm (((angular.val.1 label).re : ℝ) : ℂ) Complex.I]
  ring

end EulerNonuniqueness.Paper
