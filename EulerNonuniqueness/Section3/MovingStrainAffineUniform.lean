import EulerNonuniqueness.Section3.MovingStrainAffinePointwiseBound
import EulerNonuniqueness.Section3.MovingStrainRealUniform
import EulerNonuniqueness.Section3.DiskRotatingUniformTaylor
import EulerNonuniqueness.Section3.ContourGaugeOperatorUniform

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityBilinearGroup secondIdentityBilinearModule

theorem movingStrainAffineResidual_exists_uniform_quadratic_bound :
    ∃ radius > 0, ∃ constant ≥ 1, ∀ angular : PeriodicC1HolderHalf,
      ‖angular‖ ≤ radius → angular ∈ contourContinuousVectorSubmodule →
      (∀ label, star (angular.val.1 label) = angular.val.1 label) →
      ∀ (coefficient : ℂ) (direction : PeriodicC1HolderHalf),
      ‖diskRelabelCurve angular 1 - standardCircleBanach‖ + ‖direction‖ ≤ radius →
      direction ∈ contourContinuousVectorSubmodule →
      contourCentroidFunctional (diskRelabelCurve angular 1 + direction) = contourCentroidFunctional (diskRelabelCurve angular 1) →
      ‖movingStrainAffineResidual (diskRelabelCurve angular 1) coefficient (diskRelabelCurve angular 1 + direction)‖ ≤
        constant * ‖coefficient‖ * ‖direction‖ ^ 2 := by
  obtain ⟨correctionRadius, correctionPositive, correctionConstant, correctionOne, correctionBounds, _⟩ :=
    movingStrainRealCorrectionCLM_exists_uniform_relabel_bounds
  obtain ⟨rawRadius, rawPositive, _, rawConstant, rawOne, rawBounds⟩ := diskEulerRotatingField_exists_uniform_firstJet_bounds
  obtain ⟨gaugeRadius, gaugePositive, _, gaugeConstant, gaugeOne, gaugeBounds, _, _⟩ :=
    circleBasedCentroidProjection_exists_uniform_firstJet_bounds
  obtain ⟨centroidRadius, centroidPositive, centroidConstant, centroidNonnegative, centroidBounds⟩ :=
    contourCentroidGaugeProjection_exists_uniform_quadratic_deviation
  let threshold := min 1 (2 / (3 * Real.pi))
  have thresholdPositive : 0 < threshold := by dsimp [threshold]; positivity
  let radius := min correctionRadius (min rawRadius (min gaugeRadius
    (min centroidRadius (min (1 / 6) (threshold / 2)))))
  let constant := movingStrainAffineBoundConstant rawConstant gaugeConstant correctionConstant centroidConstant + 1
  have radiusPositive : 0 < radius := by dsimp [radius]; positivity
  have radiusCorrection : radius ≤ correctionRadius := min_le_left _ _
  have radiusRaw : radius ≤ rawRadius := (min_le_right _ _).trans (min_le_left _ _)
  have radiusGauge : radius ≤ gaugeRadius := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have radiusCentroid : radius ≤ centroidRadius :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have radiusSixth : radius ≤ 1 / 6 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have radiusThreshold : radius ≤ threshold / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have rawNonnegative : 0 ≤ rawConstant := by linarith
  have correctionNonnegative : 0 ≤ correctionConstant := by linarith
  have gaugeNonnegative : 0 ≤ gaugeConstant := by linarith
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ movingStrainAffineBoundConstant rawConstant gaugeConstant correctionConstant centroidConstant := by
      unfold movingStrainAffineBoundConstant
      positivity
    dsimp [constant]
    linarith
  refine ⟨radius, radiusPositive, constant, constantOne, ?_⟩
  intro angular angularSmall angularMember realValues coefficient direction inside member centered
  have angularHalf : ‖angular‖ < 1 / 2 := lt_of_le_of_lt (angularSmall.trans radiusSixth) (by norm_num)
  let base := fixedRelabelEquivalence angular angularHalf standardCircleBanach
  have circleIdentity := fixedRelabelEquivalence_circle angular angularHalf realValues
  have insideBase : ‖base - standardCircleBanach‖ + ‖direction‖ ≤ radius := by
    simpa only [base, circleIdentity] using inside
  have baseSmall : ‖base - standardCircleBanach‖ ≤ radius := by linarith [norm_nonneg direction]
  have directionBound : ‖direction‖ ≤ 1 := by linarith [norm_nonneg (base - standardCircleBanach)]
  have nearby : ‖base - standardCircleBanach‖ < min (1 / 3) threshold := by
    apply lt_min
    · linarith [baseSmall.trans radiusSixth]
    · linarith [baseSmall.trans radiusThreshold]
  have nextSmall : ‖base + direction - standardCircleBanach‖ < 1 / 3 := by
    rw [show base + direction - standardCircleBanach = (base - standardCircleBanach) + direction by abel]
    exact (norm_add_le _ _).trans_lt (lt_of_le_of_lt (insideBase.trans radiusSixth) (by norm_num))
  have centeredBase : contourCentroidFunctional (base + direction) = contourCentroidFunctional base := by
    simpa only [base, circleIdentity] using centered
  have baseBound : ‖base‖ ≤ 3 := by
    have triangle := norm_add_le (base - standardCircleBanach) standardCircleBanach
    rw [sub_add_cancel] at triangle
    linarith [baseSmall.trans radiusSixth, standardCircleBanach_norm_bound]
  have gauge : ‖contourCentroidGaugeProjection base‖ ≤ gaugeConstant := by
    have actual := (gaugeBounds (base - standardCircleBanach) (baseSmall.trans radiusGauge)).1
    have center : standardCircleBanach + (base - standardCircleBanach) = base := by abel
    simpa only [circleBasedCentroidProjection, center] using actual
  have correctionBound := correctionBounds angular (angularSmall.trans radiusCorrection) coefficient
  have partnerBound := correctionBounds angular (angularSmall.trans radiusCorrection) (-Complex.I * coefficient)
  rw [← circleIdentity] at correctionBound partnerBound
  simp only [norm_mul, norm_neg, Complex.norm_I, one_mul] at partnerBound
  have actual := movingStrainAffineResidual_pointwise_quadratic_bound angular angularHalf angularMember nearby
    coefficient direction member rawNonnegative gaugeNonnegative correctionNonnegative centroidNonnegative
    directionBound baseBound nextSmall centeredBase gauge correctionBound partnerBound
    (centroidBounds base direction (insideBase.trans radiusCentroid) centeredBase)
    (rawBounds base direction (insideBase.trans radiusRaw))
  rw [circleIdentity] at actual
  refine actual.trans ?_
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖direction‖)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg coefficient)
  dsimp [constant]
  linarith

end EulerNonuniqueness.Paper
