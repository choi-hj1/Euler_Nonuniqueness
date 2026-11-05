import EulerNonuniqueness.Section3.RelabeledExteriorForcingRange

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] relabeledForcingValueC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

theorem canonicalProjectedExteriorContourField_relabel_mem_generator_range {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance : ℝ)
    (positive : 0 < distance) (small : 8 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (ratio : 24 * (family.patch index).radius / distance < 1)
    (angular : PeriodicC1HolderHalf) (angularSmall : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (nearby : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi)))) (phase : Circle) :
    ∃ preimage : PeriodicC1HolderHalf,
      fderiv ℝ diskEulerRotatingField (diskRelabelCurve angular 1) preimage =
        family.canonicalProjectedExteriorContourField index time distance positive small separated phase
          (diskRelabelCurve angular 1) := by
  let coefficient := fun power => family.exteriorTaylorCoefficient (Finset.univ.erase index)
    (family.patch index).center (family.patch index).radius (power + 1) time
  have weighted : Summable (fun power => (24 : ℝ) ^ (power + 1) * ‖coefficient power‖) := by
    dsimp only [coefficient]
    simp_rw [family.exteriorTaylorCoefficient_eq_vorticityCoefficient (Finset.univ.erase index)
      (family.patch index).center (family.patch index).radius time _ positive separated]
    exact EulerNonuniqueness.Section6.summable_exteriorVorticityCoefficient_weight
      (family.subfamilyVorticity_integrable (Finset.univ.erase index) time) _
      (family.patch index).radius_positive.le positive (by norm_num)
      (family.subfamily_support_separated (Finset.univ.erase index) _ time distance separated) ratio
  obtain ⟨preimage, inverse⟩ := projectedExteriorSeries_relabel_mem_generator_range angular angularSmall
    realValues nearby phase coefficient weighted
  have series := family.canonicalProjectedExteriorContourField_eq_series index time distance positive small separated phase
    (diskRelabelCurve angular 1 - standardCircleBanach) (lt_min_iff.mp nearby).1 ratio
  have centered : standardCircleBanach + (diskRelabelCurve angular 1 - standardCircleBanach) =
      diskRelabelCurve angular 1 := by abel
  rw [centered] at series
  dsimp only [circleBasedProjectedExteriorSeries, circleBasedCentroidProjection] at series
  rw [centered] at series
  exact ⟨preimage, inverse.trans series.symm⟩

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
