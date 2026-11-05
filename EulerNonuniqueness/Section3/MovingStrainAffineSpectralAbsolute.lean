import EulerNonuniqueness.Section3.MovingStrainAffineSpectralRelative

noncomputable section

open Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

theorem movingStrainAffineResidual_exists_spectral_absolute_ball :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ state : PeriodicC1HolderHalf,
      state ∈ ball 0 radius → state ∈ contourContinuousVectorSubmodule →
      diskPhysicalSpectralChart state ∈ contourContinuousVectorSubmodule →
      diskSpectralTubularArea state = Real.pi →
      contourCentroidFunctional (diskPhysicalSpectralChart state) = 0 →
      ∀ coefficient : ℂ,
      ‖movingStrainAffineResidual (diskStationaryChart (diskRelabelNeutralCLM state)) coefficient
          (diskPhysicalSpectralChart state)‖ ≤
        constant * ‖coefficient‖ * ‖diskPhysicalTransverseProjection state‖ ^ 2 := by
  obtain ⟨radius, positive, constant, nonnegative, difference⟩ :=
    movingStrainAffineResidual_exists_spectral_relative_ball
  refine ⟨min radius 1, lt_min positive (by norm_num),
    constant * (1 + ‖diskRelabelNeutralCLM‖), by positivity, ?_⟩
  intro state inside member physicalMember area centered coefficient
  have normInside : ‖state‖ < min radius 1 := by simpa only [mem_ball, dist_zero_right] using inside
  have stateInside : state ∈ ball 0 radius := ball_subset_ball (min_le_left _ _) inside
  have neutralBound : ‖diskRelabelNeutralCLM state‖ ≤ ‖diskRelabelNeutralCLM‖ :=
    (diskRelabelNeutralCLM.le_opNorm state).trans
      (mul_le_of_le_one_right (norm_nonneg _) (normInside.trans_le (min_le_right radius 1)).le)
  have areaZero : diskSpectralTubularArea (0 : PeriodicC1HolderHalf) = Real.pi := by
    rw [diskSpectralTubularArea, diskSpectralTubularChart_zero, diskStationaryArea_zero]
  have circleZero : movingStrainAffineResidual standardCircleBanach coefficient standardCircleBanach = 0 := by
    have small : ‖(0 : PeriodicC1HolderHalf)‖ < 1 / 2 := by simp only [norm_zero]; norm_num
    have base : fixedRelabelEquivalence 0 small standardCircleBanach = standardCircleBanach := by
      rw [fixedRelabelEquivalence_circle 0 small (by intro label; change star (0 : ℂ) = 0; simp)]
      apply PeriodicC1HolderHalf.ext_value
      intro label
      rw [diskRelabelCurve_value]
      change Complex.exp ((1 : ℂ) * (Complex.I * 0)) * standardCircle label = standardCircle label
      simp
    have actual := movingStrainAffineResidual_relabel_base_zero 0 small
      (by rw [base]; simp only [sub_self, norm_zero]; positivity) coefficient
    simpa only [base] using actual
  have estimate := difference state 0 stateInside (by simpa only [mem_ball, dist_self] using positive)
    member contourContinuousVectorSubmodule.zero_mem physicalMember
    (by simpa only [diskPhysicalSpectralChart_zero] using standardCircle_mem_contourContinuousVectorSubmodule)
    area areaZero centered (by simpa only [diskPhysicalSpectralChart_zero] using contourCentroidFunctional_standardCircle_zero)
    coefficient coefficient
  have simplified :
      ‖movingStrainAffineResidual (diskStationaryChart (diskRelabelNeutralCLM state)) coefficient
        (diskPhysicalSpectralChart state)‖ ≤ constant *
          (‖coefficient‖ * (‖diskPhysicalTransverseProjection state‖ * ‖diskPhysicalTransverseProjection state‖ +
            ‖diskPhysicalTransverseProjection state‖ ^ 2 * ‖diskRelabelNeutralCLM state‖)) := by
    with_reducible_and_instances
      simpa only [map_zero, diskPhysicalSpectralChart_zero, diskStationaryChart_zero, circleZero,
        sub_zero, norm_zero, add_zero, sub_self, zero_mul] using estimate
  apply simplified.trans
  nlinarith [mul_nonneg (mul_nonneg nonnegative (norm_nonneg coefficient))
    (mul_nonneg (sq_nonneg ‖diskPhysicalTransverseProjection state‖) (sub_nonneg.mpr neutralBound))]

end EulerNonuniqueness.Paper
