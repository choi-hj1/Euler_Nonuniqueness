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

local instance spectralFunctionalGeometryC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph
local instance spectralFunctionalGeometryC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem diskPhysicalSpectral_exists_functional_pair_geometry :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ initial final : PeriodicC1HolderHalf, initial ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      ‖diskNeutralCLM initial‖ < 1 / 2 ∧ ‖diskNeutralCLM final‖ < 1 / 2 ∧
      ‖diskStationaryChart (diskRelabelNeutralCLM initial)‖ +
        (‖diskPhysicalSpectralDefect initial‖ + ‖diskPhysicalSpectralDefect final‖) ≤ 3 ∧
      ‖diskStationaryChart (diskRelabelNeutralCLM final)‖ +
        (‖diskPhysicalSpectralDefect initial‖ + ‖diskPhysicalSpectralDefect final‖) ≤ 3 ∧
      ‖diskPhysicalSpectralDefect initial - diskPhysicalSpectralDefect final‖ +
        ‖diskStationaryChart (diskRelabelNeutralCLM initial) - diskStationaryChart (diskRelabelNeutralCLM final)‖ *
          ‖diskPhysicalSpectralDefect final‖ ≤ constant *
        (‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
          (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
            ‖diskNeutralCLM initial - diskNeutralCLM final‖) := by
  obtain ⟨domainRadius, domainPositive, domainBound⟩ :=
    movingStrainSpectral_exists_relabel_domain (by norm_num : (0 : ℝ) < 1 / 6)
  obtain ⟨absoluteRadius, absolutePositive, absoluteConstant, absoluteNonnegative, absoluteBound⟩ :=
    diskPhysicalSpectralDefect_exists_transverse_bound
  obtain ⟨relativeRadius, relativePositive, relativeConstant, relativeNonnegative, relativeBound⟩ :=
    diskPhysicalSpectralDefect_exists_relative_physical_ball
  obtain ⟨baseRadius, basePositive, baseConstant, baseNonnegative, baseBound⟩ :=
    diskStationaryChart_exists_neutral_base_difference_bound
  have neutralNear : ∀ᶠ state in 𝓝 (0 : PeriodicC1HolderHalf), ‖diskRelabelNeutralCLM state‖ < baseRadius := by
    have actual := diskRelabelNeutralCLM.continuous.continuousAt (x := (0 : PeriodicC1HolderHalf))
    have convergence : Tendsto (fun state => ‖diskRelabelNeutralCLM state‖)
        (𝓝 (0 : PeriodicC1HolderHalf)) (𝓝 (0 : ℝ)) := by
      simpa only [map_zero, norm_zero] using actual.norm.tendsto
    exact convergence.eventually (eventually_lt_nhds basePositive)
  obtain ⟨neutralRadius, neutralPositive, neutralContained⟩ := Metric.eventually_nhds_iff.mp neutralNear
  let radius := min domainRadius (min absoluteRadius (min relativeRadius neutralRadius))
  let shapeConstant := absoluteConstant + relativeConstant + 1
  let embeddingConstant := 1 + ‖diskMaterialNeutralEmbeddingCLM‖
  let constant := shapeConstant * (1 + baseConstant) * embeddingConstant
  have shapeNonnegative : 0 ≤ shapeConstant := by dsimp only [shapeConstant]; positivity
  have absoluteLe : absoluteConstant ≤ shapeConstant := by dsimp only [shapeConstant]; linarith
  have relativeLe : relativeConstant ≤ shapeConstant := by dsimp only [shapeConstant]; linarith
  have embeddingOne : 1 ≤ embeddingConstant := by dsimp only [embeddingConstant]; linarith [norm_nonneg diskMaterialNeutralEmbeddingCLM]
  refine ⟨radius, by dsimp only [radius]; positivity, constant, by dsimp only [constant]; positivity, ?_⟩
  intro initial final initialInside finalInside initialArea finalArea
  have restrict {state : PeriodicC1HolderHalf} (inside : state ∈ ball 0 radius)
      {outer : ℝ} (ordered : radius ≤ outer) : state ∈ ball 0 outer := ball_subset_ball ordered inside
  have absoluteRadiusLe : radius ≤ absoluteRadius := (min_le_right _ _).trans (min_le_left _ _)
  have relativeRadiusLe : radius ≤ relativeRadius :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have neutralRadiusLe : radius ≤ neutralRadius :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have firstDomain := domainBound initial (restrict initialInside (min_le_left _ _))
  have finalDomain := domainBound final (restrict finalInside (min_le_left _ _))
  have finalAbsolute := (absoluteBound final (restrict finalInside absoluteRadiusLe) finalArea).trans
    (mul_le_mul_of_nonneg_right absoluteLe (norm_nonneg _))
  have relative := (relativeBound initial final (restrict initialInside relativeRadiusLe)
    (restrict finalInside relativeRadiusLe) initialArea finalArea).trans
    (mul_le_mul_of_nonneg_right relativeLe (by positivity))
  have firstNeutral := neutralContained (by simpa only [mem_ball] using restrict initialInside neutralRadiusLe)
  have finalNeutral := neutralContained (by simpa only [mem_ball] using restrict finalInside neutralRadiusLe)
  have bases := baseBound initial final firstNeutral.le finalNeutral.le
  have baseNorm (state : PeriodicC1HolderHalf)
      (nearby : ‖diskStationaryChart (diskRelabelNeutralCLM state) - standardCircleBanach‖ < 1 / 6) :
      ‖diskStationaryChart (diskRelabelNeutralCLM state)‖ ≤ 13 / 6 := by
    have triangle := norm_add_le (diskStationaryChart (diskRelabelNeutralCLM state) - standardCircleBanach) standardCircleBanach
    rw [sub_add_cancel] at triangle
    linarith [standardCircleBanach_norm_bound]
  refine ⟨firstDomain.1, finalDomain.1, ?_, ?_, ?_⟩
  · linarith [baseNorm initial firstDomain.2.2.1, firstDomain.2.2.2, finalDomain.2.2.2]
  · linarith [baseNorm final finalDomain.2.2.1, firstDomain.2.2.2, finalDomain.2.2.2]
  · have finalDefect : ‖diskPhysicalSpectralDefect final‖ ≤ shapeConstant *
        (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) :=
      finalAbsolute.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) shapeNonnegative)
    have geometry := EulerNonuniqueness.General.relative_functional_geometry_budget
      (norm_nonneg _) (by positivity) (norm_nonneg _) shapeNonnegative baseNonnegative (norm_nonneg _)
      (norm_nonneg _) relative bases finalDefect
    have neutralBound : ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖ ≤
        embeddingConstant * ‖diskNeutralCLM initial - diskNeutralCLM final‖ :=
      (diskRelabelNeutralCLM_difference_norm_le initial final).trans
        (mul_le_mul_of_nonneg_right (by dsimp only [embeddingConstant]; linarith) (norm_nonneg _))
    apply geometry.trans
    dsimp only [constant]
    calc
      _ ≤ shapeConstant * (1 + baseConstant) *
          (embeddingConstant * ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
            (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
              (embeddingConstant * ‖diskNeutralCLM initial - diskNeutralCLM final‖)) := by
        gcongr
        exact le_mul_of_one_le_left (norm_nonneg _) embeddingOne
      _ = _ := by ring

end EulerNonuniqueness.Paper
