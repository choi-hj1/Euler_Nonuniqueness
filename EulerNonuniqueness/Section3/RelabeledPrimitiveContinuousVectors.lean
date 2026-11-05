import EulerNonuniqueness.Section3.ContourContinuousPolynomial
import EulerNonuniqueness.Section3.FixedRelabelContinuousVectors
import EulerNonuniqueness.Section3.RelabeledForcingPrimitiveSeries

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] continuousFourierC1Group holderContinuousRealSpace
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem diskRelabelCurve_mem_contourContinuousVectorSubmodule (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2) (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (member : angular ∈ contourContinuousVectorSubmodule) :
    diskRelabelCurve angular 1 ∈ contourContinuousVectorSubmodule := by
  rw [← fixedRelabelEquivalence_circle angular small realValues]
  exact fixedRelabelEquivalence_mem_continuousVector angular small member standardCircleBanach
    standardCircle_mem_contourContinuousVectorSubmodule

theorem relabeledForcingPrimitiveSeries_mem_contourContinuousVectorSubmodule
    (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (member : angular ∈ contourContinuousVectorSubmodule)
    {frequency : ℝ} (nonzero : frequency ≠ 0) (amplitude : ℕ → ℝ → ℂ) (time : ℝ)
    (weighted : Summable (fun degree => (2 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖)) :
    relabeledForcingPrimitiveSeries angular frequency amplitude time ∈ contourContinuousVectorSubmodule := by
  have summableTerms : Summable (fun degree => relabeledDiskForcingPrimitive angular degree frequency (amplitude degree) time) :=
    Summable.of_norm_bounded _ (weighted.mul_left (32 / |frequency|))
      (fun degree => relabeledDiskForcingPrimitive_weighted_bound angular small realValues degree nonzero _ time)
  apply contourContinuousVectorSubmodule_tsum _ summableTerms
  intro degree
  apply contourContinuousPolynomial_complex_smul
  apply contourContinuousPolynomial_conjugate
  exact contourContinuousVectorSubmodule_naturalPower _
    (diskRelabelCurve_mem_contourContinuousVectorSubmodule angular small realValues member) _

namespace FiniteMovingPatchFamily

theorem relabeledExteriorForcingPrimitive_mem_contourContinuousVectorSubmodule {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2) (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (member : angular ∈ contourContinuousVectorSubmodule)
    {frequency time distance : ℝ} (nonzero : frequency ≠ 0) (positive : 0 < distance)
    (ratio : 2 * (family.patch index).radius / distance < 1)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖) :
    family.relabeledExteriorForcingPrimitive index angular frequency time ∈ contourContinuousVectorSubmodule := by
  exact relabeledForcingPrimitiveSeries_mem_contourContinuousVectorSubmodule angular small realValues member
    nonzero _ time (family.summable_weighted_exteriorTaylorCoefficient (Finset.univ.erase index)
      (family.patch index).center (family.patch index).radius time (family.patch index).radius_positive.le
      positive separated ratio)

end FiniteMovingPatchFamily

end EulerNonuniqueness.Paper
