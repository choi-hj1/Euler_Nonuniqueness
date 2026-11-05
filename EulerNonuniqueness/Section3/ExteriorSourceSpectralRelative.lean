import EulerNonuniqueness.Section3.NormalizedExteriorFunctionalRelative
import EulerNonuniqueness.Section3.StationaryContourFunctional
import EulerNonuniqueness.Section3.DiskNeutralIdentification
import EulerNonuniqueness.General.RelativeFunctionalGeometryBudget

noncomputable section

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace
  c1InverseAnalyticOperatorGroup c1InverseAnalyticOperatorSpace
  antiholomorphicPairOperatorGroup antiholomorphicPairOperatorSpace

theorem exteriorSourceFunctional_exists_spectral_relative_ball :
    ∃ radius > (0 : ℝ), ∃ parameterRadius > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ initial final : PeriodicC1HolderHalf, initial ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      ∀ parameter : ℂ, ‖parameter‖ ≤ parameterRadius → ∀ power : ℕ,
      ‖contourAntiholomorphicFunctional (normalizedExteriorInversePowerKernel parameter power)
          (diskPhysicalSpectralChart initial) -
        contourAntiholomorphicFunctional (normalizedExteriorInversePowerKernel parameter power)
          (diskPhysicalSpectralChart final)‖ ≤ constant * (96 : ℝ) ^ (power + 1) * ‖parameter‖ *
        (‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
          (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
            ‖diskNeutralCLM initial - diskNeutralCLM final‖) := by
  obtain ⟨functionalRadius, functionalPositive, functionalConstant, functionalOne, functionalBound⟩ :=
    normalizedExteriorFunctional_exists_relative_increment
  obtain ⟨reciprocalRadius, reciprocalPositive, reciprocalConstant, reciprocalOne, reciprocalBound⟩ :=
    normalizedC1Reciprocal_exists_uniform_bounds
  obtain ⟨domainRadius, domainPositive, domainBound⟩ :=
    movingStrainSpectral_exists_relabel_domain (by norm_num : (0 : ℝ) < 1 / 6)
  obtain ⟨absoluteRadius, absolutePositive, absoluteConstant, absoluteNonnegative, absoluteBound⟩ :=
    diskPhysicalSpectralDefect_exists_transverse_bound
  obtain ⟨relativeRadius, relativePositive, relativeConstant, relativeNonnegative, relativeBound⟩ :=
    diskPhysicalSpectralDefect_exists_relative_physical_ball
  obtain ⟨baseRadius, basePositive, baseConstant, baseNonnegative, baseBound⟩ :=
    diskStationaryChart_exists_neutral_base_difference_bound
  have neutralNear : ∀ᶠ state in 𝓝 (0 : PeriodicC1HolderHalf), ‖diskRelabelNeutralCLM state‖ < baseRadius := by
    have actual : ContinuousAt (fun state => diskRelabelNeutralCLM state) (0 : PeriodicC1HolderHalf) :=
      diskRelabelNeutralCLM.continuous.continuousAt
    have convergence : Tendsto (fun state => ‖diskRelabelNeutralCLM state‖)
        (𝓝 (0 : PeriodicC1HolderHalf)) (𝓝 (0 : ℝ)) := by
      simpa only [map_zero, norm_zero] using actual.norm.tendsto
    exact convergence.eventually (eventually_lt_nhds basePositive)
  obtain ⟨neutralRadius, neutralPositive, neutralContained⟩ := Metric.eventually_nhds_iff.mp neutralNear
  let radius := min domainRadius (min absoluteRadius (min relativeRadius neutralRadius))
  let parameterRadius := min functionalRadius (min reciprocalRadius (1 / 4))
  let shapeConstant := absoluteConstant + relativeConstant + 1
  let embeddingConstant := 1 + ‖diskMaterialNeutralEmbeddingCLM‖
  let geometryConstant := shapeConstant * (1 + baseConstant) * embeddingConstant
  have shapeNonnegative : 0 ≤ shapeConstant := by dsimp only [shapeConstant]; positivity
  have absoluteLe : absoluteConstant ≤ shapeConstant := by dsimp only [shapeConstant]; linarith
  have relativeLe : relativeConstant ≤ shapeConstant := by dsimp only [shapeConstant]; linarith
  have embeddingOne : 1 ≤ embeddingConstant := by dsimp only [embeddingConstant]; linarith [norm_nonneg diskMaterialNeutralEmbeddingCLM]
  have geometryNonnegative : 0 ≤ geometryConstant := by dsimp only [geometryConstant]; positivity
  refine ⟨radius, by dsimp only [radius]; positivity, parameterRadius,
    by dsimp only [parameterRadius]; positivity,
    functionalConstant * geometryConstant, mul_nonneg (by linarith) geometryNonnegative, ?_⟩
  intro initial final initialInside finalInside initialArea finalArea parameter parameterSmall power
  have restrict {state : PeriodicC1HolderHalf} (inside : state ∈ ball 0 radius)
      {outer : ℝ} (ordered : radius ≤ outer) : state ∈ ball 0 outer := ball_subset_ball ordered inside
  have absoluteRadiusLe : radius ≤ absoluteRadius := (min_le_right _ _).trans (min_le_left _ _)
  have relativeRadiusLe : radius ≤ relativeRadius :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have neutralRadiusLe : radius ≤ neutralRadius :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have firstDomain := domainBound initial (restrict initialInside (min_le_left _ _))
  have finalDomain := domainBound final (restrict finalInside (min_le_left _ _))
  have firstAbsolute := (absoluteBound initial (restrict initialInside absoluteRadiusLe) initialArea).trans
    (mul_le_mul_of_nonneg_right absoluteLe (norm_nonneg _))
  have finalAbsolute := (absoluteBound final (restrict finalInside absoluteRadiusLe) finalArea).trans
    (mul_le_mul_of_nonneg_right absoluteLe (norm_nonneg _))
  have relative := (relativeBound initial final (restrict initialInside relativeRadiusLe)
    (restrict finalInside relativeRadiusLe) initialArea finalArea).trans
    (mul_le_mul_of_nonneg_right relativeLe (by positivity))
  have firstNeutral := neutralContained (by simpa only [mem_ball] using restrict initialInside neutralRadiusLe)
  have finalNeutral := neutralContained (by simpa only [mem_ball] using restrict finalInside neutralRadiusLe)
  have bases := baseBound initial final firstNeutral.le finalNeutral.le
  have functionalSmall : ‖parameter‖ ≤ functionalRadius := parameterSmall.trans (min_le_left _ _)
  have reciprocalSmall : ‖parameter‖ ≤ reciprocalRadius :=
    parameterSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have parameterQuarter : ‖parameter‖ ≤ 1 / 4 :=
    parameterSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have kernelContinuous : Continuous (fun label =>
      normalizedExteriorInversePowerKernel parameter power (standardCircle label)) := by
    have actual := normalizedExteriorInversePowerKernel_continuous_comp standardCircleBanach
      (by norm_num) 1 parameter (distance := 1 / 2) (by norm_num)
      (by rw [norm_one]; linarith) power
    simpa only [div_one] using actual
  have reconstruction (state : PeriodicC1HolderHalf) :
      diskStationaryChart (diskRelabelNeutralCLM state) + diskPhysicalSpectralDefect state =
        diskPhysicalSpectralChart state := by unfold diskPhysicalSpectralDefect; abel
  have firstBaseNorm : ‖diskStationaryChart (diskRelabelNeutralCLM initial)‖ ≤ 13 / 6 := by
    have triangle := norm_add_le (diskStationaryChart (diskRelabelNeutralCLM initial) - standardCircleBanach) standardCircleBanach
    rw [sub_add_cancel] at triangle
    linarith [firstDomain.2.2.1, standardCircleBanach_norm_bound]
  have finalBaseNorm : ‖diskStationaryChart (diskRelabelNeutralCLM final)‖ ≤ 13 / 6 := by
    have triangle := norm_add_le (diskStationaryChart (diskRelabelNeutralCLM final) - standardCircleBanach) standardCircleBanach
    rw [sub_add_cancel] at triangle
    linarith [finalDomain.2.2.1, standardCircleBanach_norm_bound]
  have firstPhysicalNorm : ‖diskPhysicalSpectralChart initial‖ ≤ 3 := by
    rw [← reconstruction initial]
    exact (norm_add_le _ _).trans (by linarith [firstDomain.2.2.2])
  have finalPhysicalNorm : ‖diskPhysicalSpectralChart final‖ ≤ 3 := by
    rw [← reconstruction final]
    exact (norm_add_le _ _).trans (by linarith [finalDomain.2.2.2])
  have agreement (data : PeriodicC1HolderHalf) (bounded : ‖data‖ ≤ 3) :=
    normalizedExteriorFunctional_eq_contour parameter power data
      (((reciprocalBound parameter reciprocalSmall).1 data bounded).1)
  have firstStationary := contourAntiholomorphicFunctional_stationary_base
    (normalizedExteriorInversePowerKernel parameter power) initial firstDomain.1 kernelContinuous
  have finalStationary := contourAntiholomorphicFunctional_stationary_base
    (normalizedExteriorInversePowerKernel parameter power) final finalDomain.1 kernelContinuous
  rw [← agreement _ (firstBaseNorm.trans (by norm_num))] at firstStationary
  rw [← agreement _ (finalBaseNorm.trans (by norm_num))] at finalStationary
  have actual := functionalBound parameter functionalSmall power
    (diskStationaryChart (diskRelabelNeutralCLM initial)) (diskStationaryChart (diskRelabelNeutralCLM final))
    (diskPhysicalSpectralDefect initial) (diskPhysicalSpectralDefect final)
    (by linarith [firstDomain.2.2.2, finalDomain.2.2.2])
    (by linarith [firstDomain.2.2.2, finalDomain.2.2.2])
  rw [reconstruction, reconstruction, firstStationary, finalStationary,
    sub_sub_sub_cancel_right, agreement _ firstPhysicalNorm, agreement _ finalPhysicalNorm] at actual
  have finalDefect : ‖diskPhysicalSpectralDefect final‖ ≤ shapeConstant *
      (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) :=
    finalAbsolute.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) shapeNonnegative)
  have geometry := EulerNonuniqueness.General.relative_functional_geometry_budget
    (norm_nonneg _) (by positivity) (norm_nonneg _) shapeNonnegative baseNonnegative (norm_nonneg _)
    (norm_nonneg _) relative bases finalDefect
  have embedding := diskRelabelNeutralCLM_difference_norm_le initial final
  have neutralBound : ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖ ≤
      embeddingConstant * ‖diskNeutralCLM initial - diskNeutralCLM final‖ :=
    embedding.trans (mul_le_mul_of_nonneg_right (by dsimp only [embeddingConstant]; linarith) (norm_nonneg _))
  apply actual.trans
  have finalGeometry :
      ‖diskPhysicalSpectralDefect initial - diskPhysicalSpectralDefect final‖ +
        ‖diskStationaryChart (diskRelabelNeutralCLM initial) - diskStationaryChart (diskRelabelNeutralCLM final)‖ *
          ‖diskPhysicalSpectralDefect final‖ ≤ geometryConstant *
        (‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
          (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
            ‖diskNeutralCLM initial - diskNeutralCLM final‖) := by
    apply geometry.trans
    dsimp only [geometryConstant]
    calc
      _ ≤ shapeConstant * (1 + baseConstant) *
          (embeddingConstant * ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
            (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
              (embeddingConstant * ‖diskNeutralCLM initial - diskNeutralCLM final‖)) := by
        gcongr
        exact le_mul_of_one_le_left (norm_nonneg _) embeddingOne
      _ = _ := by ring
  exact (mul_le_mul_of_nonneg_left finalGeometry (by positivity)).trans_eq (by ring)

end EulerNonuniqueness.Paper
