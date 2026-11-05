import EulerNonuniqueness.Section3.ContourMomentFirstJetLipschitz
import EulerNonuniqueness.Section3.DiskSpectralSmallFunctionalGeometry

noncomputable section

open Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace
  c1InverseAnalyticOperatorGroup c1InverseAnalyticOperatorSpace

theorem contourPolynomialMoment_exists_spectral_relative_ball :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ initial final : PeriodicC1HolderHalf, initial ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      ∀ degree : ℕ,
      ‖contourPolynomialMoment (degree + 1) (diskPhysicalSpectralChart initial) -
        contourPolynomialMoment (degree + 1) (diskPhysicalSpectralChart final)‖ ≤
        constant * (96 : ℝ) ^ (degree + 1) *
          (‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
            (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
              ‖diskNeutralCLM initial - diskNeutralCLM final‖) := by
  obtain ⟨radius, positive, geometryConstant, geometryNonnegative, geometryBound⟩ :=
    diskPhysicalSpectral_exists_small_functional_pair_geometry
  obtain ⟨functionalConstant, one, functionalBound⟩ := conjugateContourMoment_exists_relative_increment
  refine ⟨radius, positive, functionalConstant * geometryConstant, by positivity, ?_⟩
  intro initial final initialInside finalInside initialArea finalArea degree
  have geometry := geometryBound initial final initialInside finalInside initialArea finalArea
  have actual := functionalBound (degree + 1)
    (diskStationaryChart (diskRelabelNeutralCLM initial)) (diskStationaryChart (diskRelabelNeutralCLM final))
    (diskPhysicalSpectralDefect initial) (diskPhysicalSpectralDefect final) geometry.2.2.1 geometry.2.2.2.1
  have reconstruction (state : PeriodicC1HolderHalf) :
      diskStationaryChart (diskRelabelNeutralCLM state) + diskPhysicalSpectralDefect state =
        diskPhysicalSpectralChart state := by unfold diskPhysicalSpectralDefect; abel
  rw [reconstruction, reconstruction,
    contourPolynomialMoment_stationary_base_positive initial geometry.1 degree,
    contourPolynomialMoment_stationary_base_positive final geometry.2.1 degree,
    star_zero, sub_zero, sub_zero, ← star_sub, norm_star] at actual
  exact actual.trans ((mul_le_mul_of_nonneg_left geometry.2.2.2.2 (by positivity)).trans_eq (by ring))

end EulerNonuniqueness.Paper
