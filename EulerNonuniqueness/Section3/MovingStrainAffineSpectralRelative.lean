import EulerNonuniqueness.Section3.MovingStrainAffineAmplitudeRelative
import EulerNonuniqueness.Section3.MovingStrainSpectralRelabelDomain
import EulerNonuniqueness.General.AffinePhysicalRelativeBudget

noncomputable section

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

theorem movingStrainAffineResidual_exists_spectral_relative_ball :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : PeriodicC1HolderHalf,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      initial ∈ contourContinuousVectorSubmodule → final ∈ contourContinuousVectorSubmodule →
      diskPhysicalSpectralChart initial ∈ contourContinuousVectorSubmodule →
      diskPhysicalSpectralChart final ∈ contourContinuousVectorSubmodule →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      contourCentroidFunctional (diskPhysicalSpectralChart initial) = 0 →
      contourCentroidFunctional (diskPhysicalSpectralChart final) = 0 →
      ∀ firstCoefficient finalCoefficient : ℂ,
      ‖movingStrainAffineResidual (diskStationaryChart (diskRelabelNeutralCLM initial)) firstCoefficient
          (diskPhysicalSpectralChart initial) -
        movingStrainAffineResidual (diskStationaryChart (diskRelabelNeutralCLM final)) finalCoefficient
          (diskPhysicalSpectralChart final)‖ ≤ constant *
        (‖firstCoefficient‖ *
          ((‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
              ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
            (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) ^ 2 *
              ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖) +
          ‖firstCoefficient - finalCoefficient‖ * ‖diskPhysicalTransverseProjection final‖ ^ 2) := by
  obtain ⟨rawRadius, rawPositive, rawConstant, rawNonnegative, rawBound⟩ :=
    movingStrainAffineResidual_exists_amplitude_relative_quadratic_ball
  obtain ⟨domainRadius, domainPositive, domainBound⟩ :=
    movingStrainSpectral_exists_relabel_domain (show 0 < rawRadius / 4 by positivity)
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
  let shapeConstant := absoluteConstant + relativeConstant + 1
  let factor := shapeConstant ^ 2 * (1 + baseConstant)
  have shapeNonnegative : 0 ≤ shapeConstant := by dsimp [shapeConstant]; positivity
  have absoluteLe : absoluteConstant ≤ shapeConstant := by dsimp [shapeConstant]; linarith
  have relativeLe : relativeConstant ≤ shapeConstant := by dsimp [shapeConstant]; linarith
  have factorNonnegative : 0 ≤ factor := by dsimp [factor]; positivity
  have squareLe : shapeConstant ^ 2 ≤ factor := by
    dsimp [factor]
    nlinarith [sq_nonneg shapeConstant]
  refine ⟨radius, by dsimp [radius]; positivity, rawConstant * factor, mul_nonneg rawNonnegative factorNonnegative, ?_⟩
  intro initial final initialInside finalInside initialMember finalMember initialPhysicalMember finalPhysicalMember
    initialArea finalArea initialCentered finalCentered firstCoefficient finalCoefficient
  have restrict {state : PeriodicC1HolderHalf} (inside : state ∈ ball 0 radius)
      {outer : ℝ} (bound : radius ≤ outer) : state ∈ ball 0 outer := by
    exact ball_subset_ball bound inside
  have initialDomain := domainBound initial (restrict initialInside (min_le_left _ _))
  have finalDomain := domainBound final (restrict finalInside (min_le_left _ _))
  have absoluteRadiusLe : radius ≤ absoluteRadius := (min_le_right _ _).trans (min_le_left _ _)
  have relativeRadiusLe : radius ≤ relativeRadius :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have neutralRadiusLe : radius ≤ neutralRadius :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
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
  have initialBaseEquality := movingStrainSpectral_stationary_base_eq_fixedRelabel initial initialDomain.1
  have finalBaseEquality := movingStrainSpectral_stationary_base_eq_fixedRelabel final finalDomain.1
  have firstReconstruction : diskStationaryChart (diskRelabelNeutralCLM initial) +
      diskPhysicalSpectralDefect initial = diskPhysicalSpectralChart initial := by
    unfold diskPhysicalSpectralDefect
    abel
  have finalReconstruction : diskStationaryChart (diskRelabelNeutralCLM final) +
      diskPhysicalSpectralDefect final = diskPhysicalSpectralChart final := by
    unfold diskPhysicalSpectralDefect
    abel
  have firstDefectMember : diskPhysicalSpectralDefect initial ∈ contourContinuousVectorSubmodule :=
    contourContinuousVectorSubmodule.sub_mem initialPhysicalMember
      (diskStationaryNeutral_mem_contourContinuousVectorSubmodule initial initialMember)
  have finalDefectMember : diskPhysicalSpectralDefect final ∈ contourContinuousVectorSubmodule :=
    contourContinuousVectorSubmodule.sub_mem finalPhysicalMember
      (diskStationaryNeutral_mem_contourContinuousVectorSubmodule final finalMember)
  have firstCentroid : contourCentroidFunctional
      (diskStationaryChart (diskRelabelNeutralCLM initial) + diskPhysicalSpectralDefect initial) =
        contourCentroidFunctional (diskStationaryChart (diskRelabelNeutralCLM initial)) := by
    rw [firstReconstruction, initialCentered, initialBaseEquality,
      contourCentroidFunctional_fixedRelabel, contourCentroidFunctional_standardCircle_zero]
  have finalCentroid : contourCentroidFunctional
      (diskStationaryChart (diskRelabelNeutralCLM final) + diskPhysicalSpectralDefect final) =
        contourCentroidFunctional (diskStationaryChart (diskRelabelNeutralCLM final)) := by
    rw [finalReconstruction, finalCentered, finalBaseEquality,
      contourCentroidFunctional_fixedRelabel, contourCentroidFunctional_standardCircle_zero]
  have firstJoint : ‖diskStationaryChart (diskRelabelNeutralCLM initial) - standardCircleBanach‖ +
      (‖diskPhysicalSpectralDefect initial‖ + ‖diskPhysicalSpectralDefect final‖) ≤ rawRadius := by
    linarith [initialDomain.2.2.1, initialDomain.2.2.2, finalDomain.2.2.2]
  have finalJoint : ‖diskStationaryChart (diskRelabelNeutralCLM final) - standardCircleBanach‖ +
      (‖diskPhysicalSpectralDefect initial‖ + ‖diskPhysicalSpectralDefect final‖) ≤ rawRadius := by
    linarith [finalDomain.2.2.1, initialDomain.2.2.2, finalDomain.2.2.2]
  have raw := rawBound (diskNeutralCLM initial) (diskNeutralCLM final) initialDomain.1 finalDomain.1
    (diskNeutralCLM_mem_contourContinuousVectorSubmodule initial initialMember)
    (diskNeutralCLM_mem_contourContinuousVectorSubmodule final finalMember)
    (by simpa only [← initialBaseEquality] using initialDomain.2.1)
    (by simpa only [← finalBaseEquality] using finalDomain.2.1)
    (diskPhysicalSpectralDefect initial) (diskPhysicalSpectralDefect final) firstDefectMember finalDefectMember
    (by simpa only [← initialBaseEquality] using firstJoint)
    (by simpa only [← finalBaseEquality] using finalJoint)
    (by simpa only [← initialBaseEquality] using firstCentroid)
    (by simpa only [← finalBaseEquality] using finalCentroid) firstCoefficient finalCoefficient
  rw [← initialBaseEquality, ← finalBaseEquality, firstReconstruction, finalReconstruction] at raw
  have budget := EulerNonuniqueness.General.affine_physical_relative_quadratic_budget
    ‖diskPhysicalSpectralDefect initial‖ ‖diskPhysicalSpectralDefect final‖
    (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖)
    ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖
    ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖
    ‖diskPhysicalSpectralDefect initial - diskPhysicalSpectralDefect final‖
    ‖diskStationaryChart (diskRelabelNeutralCLM initial) - diskStationaryChart (diskRelabelNeutralCLM final)‖
    shapeConstant baseConstant (norm_nonneg _) (norm_nonneg _) (by positivity)
    (norm_nonneg _) (norm_nonneg _) shapeNonnegative baseNonnegative
    (by nlinarith [firstAbsolute, finalAbsolute]) relative bases
  have square : ‖diskPhysicalSpectralDefect final‖ ^ 2 ≤
      factor * ‖diskPhysicalTransverseProjection final‖ ^ 2 := by
    have squared := pow_le_pow_left₀ (norm_nonneg _) finalAbsolute 2
    nlinarith [mul_nonneg (sub_nonneg.mpr squareLe) (sq_nonneg ‖diskPhysicalTransverseProjection final‖)]
  apply raw.trans
  calc
    _ ≤ rawConstant * (‖firstCoefficient‖ *
        (factor * ((‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
            ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
          (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) ^ 2 *
            ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖)) +
        ‖firstCoefficient - finalCoefficient‖ * (factor * ‖diskPhysicalTransverseProjection final‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left budget (norm_nonneg _))
        (mul_le_mul_of_nonneg_left square (norm_nonneg _))) rawNonnegative
    _ = _ := by ring

end EulerNonuniqueness.Paper
