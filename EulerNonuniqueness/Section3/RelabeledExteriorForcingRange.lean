import EulerNonuniqueness.Section3.RelabeledAntiholomorphicSpectrum
import EulerNonuniqueness.Section3.RelabeledCentroidSpectralProjection
import EulerNonuniqueness.Section3.CanonicalProjectedExteriorSeries

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] relabeledForcingValueC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

theorem projectedExteriorSeries_relabel_mem_generator_range (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (nearby : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi))))
    (phase : Circle) (coefficient : ℕ → ℂ)
    (weighted : Summable (fun power => (24 : ℝ) ^ (power + 1) * ‖coefficient power‖)) :
    ∃ preimage : PeriodicC1HolderHalf,
      fderiv ℝ diskEulerRotatingField (diskRelabelCurve angular 1) preimage =
        contourCentroidGaugeProjection (diskRelabelCurve angular 1)
          (exteriorContourPowerSeries phase coefficient (diskRelabelCurve angular 1)) := by
  let data := diskRelabelCurve angular 1
  let generator := fderiv ℝ diskEulerRotatingField data
  let projection := contourCentroidGaugeProjection data
  let terms := fun power => rotatedExteriorPower phase data power (coefficient power)
  have bound : ‖data‖ ≤ 3 := by
    have triangle := norm_add_le (data - standardCircleBanach) standardCircleBanach
    rw [sub_add_cancel] at triangle
    linarith [(lt_min_iff.mp nearby).1, standardCircleBanach_norm_bound]
  have summable : Summable terms := rotatedExteriorPower_summable phase data bound coefficient weighted
  have scaled : Summable (fun power => (2 * Complex.I) • terms power) := summable.const_smul _
  have inverse (power : ℕ) : generator ((2 * Complex.I) • terms power) = terms power := by
    change fderiv ℝ diskEulerRotatingField (diskRelabelCurve angular 1)
      ((2 * Complex.I) • (((phase : ℂ)⁻¹ ^ (power + 2) * coefficient power) •
        relabeledDiskForcingMode angular power)) = _
    rw [smul_smul]
    exact diskEulerRotatingField_relabel_forcing_mode_range angular small realValues (lt_min_iff.mp nearby).2 power _
  have rawRange : generator (∑' power, (2 * Complex.I) • terms power) = ∑' power, terms power := by
    rw [generator.map_tsum scaled]
    exact tsum_congr inverse
  have commutation := contourCentroidGaugeProjection_relabeled_circle_commutes angular small
    (by simpa only [fixedRelabelEquivalence_circle angular small realValues] using nearby)
  rw [fixedRelabelEquivalence_circle angular small realValues] at commutation
  have commutes (direction : PeriodicC1HolderHalf) : generator (projection direction) = projection (generator direction) := by
    exact (congrArg (fun operator : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf => operator direction) commutation).symm
  refine ⟨projection (∑' power, (2 * Complex.I) • terms power), ?_⟩
  rw [commutes, rawRange]
  rfl

end EulerNonuniqueness.Paper
