import EulerNonuniqueness.Section3.CanonicalExteriorCommonBoundaryForcingRate

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd

open EulerNonuniqueness.General

local instance commonBoundaryHistoryC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

def canonicalExteriorCommonBoundaryDistance {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (frequency time radius : ℝ) (first final : PeriodicC1HolderHalf) : ℝ :=
  weightedBoundaryPairDistance radius
    (family.canonicalExteriorCommonQuadraticCoordinate index frequency time (diskPhysicalSpectralChart first))
    (family.canonicalExteriorCommonQuadraticCoordinate index frequency time (diskPhysicalSpectralChart final))
    (family.canonicalExteriorCommonTrueAngularCoordinate index frequency time (diskPhysicalSpectralChart first))
    (family.canonicalExteriorCommonTrueAngularCoordinate index frequency time (diskPhysicalSpectralChart final))

def canonicalExteriorCoefficientPairSeries {firstCount finalCount : ℕ}
    (firstFamily : FiniteMovingPatchFamily firstCount) (finalFamily : FiniteMovingPatchFamily finalCount)
    (firstIndex : Fin firstCount) (finalIndex : Fin finalCount) (time : ℝ) : ℝ :=
  ∑' degree, (96 : ℝ) ^ (degree + 1) *
    ‖firstFamily.canonicalExteriorStaticCoefficient firstIndex time degree - finalFamily.canonicalExteriorStaticCoefficient finalIndex time degree‖

theorem exists_canonical_common_boundary_original_time_history :
    ∃ caps : CanonicalCommonBoundaryRateCaps, ∃ physicalRadius > 0, ∃ spectralRadius > 0, ∃ constant ≥ 1,
      ∀ {firstCount finalCount : ℕ} (firstFamily : FiniteMovingPatchFamily firstCount)
        (finalFamily : FiniteMovingPatchFamily finalCount) (firstIndex : Fin firstCount) (finalIndex : Fin finalCount)
        (frequency firstDistance finalDistance weight mass radius horizon : ℝ)
        (firstRaw finalRaw firstResidual finalResidual sourceDifference : ℝ → PeriodicC1HolderHalf),
      0 ≤ radius → 0 ≤ horizon →
      ContinuousOn (fun time => firstFamily.canonicalExteriorCommonQuadraticCoordinate firstIndex frequency time (diskPhysicalSpectralChart (firstRaw time))) (Icc 0 horizon) →
      ContinuousOn (fun time => firstFamily.canonicalExteriorCommonQuadraticCoordinate firstIndex frequency time (diskPhysicalSpectralChart (finalRaw time))) (Icc 0 horizon) →
      ContinuousOn (fun time => firstFamily.canonicalExteriorCommonTrueAngularCoordinate firstIndex frequency time (diskPhysicalSpectralChart (firstRaw time))) (Icc 0 horizon) →
      ContinuousOn (fun time => firstFamily.canonicalExteriorCommonTrueAngularCoordinate firstIndex frequency time (diskPhysicalSpectralChart (finalRaw time))) (Icc 0 horizon) →
      ContinuousOn (fun time => firstFamily.canonicalExteriorCommonQuadraticMaterialForcing firstIndex frequency time
        (diskPhysicalSpectralChart (firstRaw time)) (firstResidual time) 0) (Icc 0 horizon) →
      ContinuousOn (fun time => firstFamily.canonicalExteriorCommonQuadraticMaterialForcing firstIndex frequency time
        (diskPhysicalSpectralChart (finalRaw time)) (finalResidual time) (sourceDifference time)) (Icc 0 horizon) →
      ContinuousOn (fun time => firstFamily.canonicalExteriorCommonTrueAngularForcing firstIndex frequency time
        (diskPhysicalSpectralChart (firstRaw time)) (firstResidual time) 0) (Icc 0 horizon) →
      ContinuousOn (fun time => firstFamily.canonicalExteriorCommonTrueAngularForcing firstIndex frequency time
        (diskPhysicalSpectralChart (finalRaw time)) (finalResidual time) (sourceDifference time)) (Icc 0 horizon) →
      ContinuousOn (canonicalExteriorCoefficientPairSeries firstFamily finalFamily firstIndex finalIndex) (Icc 0 horizon) →
      (∀ time ∈ Ioo 0 horizon,
        ∃ comparison : CanonicalCommonBoundaryPairAt caps firstFamily finalFamily firstIndex finalIndex
          frequency time firstDistance finalDistance weight mass radius (firstRaw time) (finalRaw time),
        firstResidual time = comparison.firstResidual ∧ finalResidual time = comparison.finalResidual ∧
        sourceDifference time = comparison.sourceDifference ∧
        ‖firstFamily.canonicalExteriorCommonPhysicalCoordinate firstIndex frequency time (diskPhysicalSpectralChart (firstRaw time)) - standardCircleBanach‖ ≤ physicalRadius ∧
        ‖firstFamily.canonicalExteriorCommonPhysicalCoordinate firstIndex frequency time (diskPhysicalSpectralChart (finalRaw time)) - standardCircleBanach‖ ≤ physicalRadius ∧
        ‖firstFamily.canonicalExteriorCommonNormalizedPhysicalCoordinate firstIndex frequency time (diskPhysicalSpectralChart (firstRaw time))‖ ≤ spectralRadius ∧
        ‖firstFamily.canonicalExteriorCommonNormalizedPhysicalCoordinate firstIndex frequency time (diskPhysicalSpectralChart (finalRaw time))‖ ≤ spectralRadius ∧
        HasDerivAt (fun current => firstFamily.canonicalExteriorCommonPhysicalCoordinate firstIndex frequency current (diskPhysicalSpectralChart (firstRaw current)))
          (frequency • diskEulerRotatingField (firstFamily.canonicalExteriorCommonPhysicalCoordinate firstIndex frequency time (diskPhysicalSpectralChart (firstRaw time))) + firstResidual time) time ∧
        HasDerivAt (fun current => firstFamily.canonicalExteriorCommonPhysicalCoordinate firstIndex frequency current (diskPhysicalSpectralChart (finalRaw current)))
          (frequency • diskEulerRotatingField (firstFamily.canonicalExteriorCommonPhysicalCoordinate firstIndex frequency time (diskPhysicalSpectralChart (finalRaw time))) +
            finalResidual time + firstFamily.canonicalExteriorCommonPhysicalDerivative firstIndex frequency time (diskPhysicalSpectralChart (finalRaw time)) (sourceDifference time)) time) →
      ∀ time ∈ Icc 0 horizon,
        firstFamily.canonicalExteriorCommonBoundaryDistance firstIndex frequency time radius (firstRaw time) (finalRaw time) ≤
          constant * firstFamily.canonicalExteriorCommonBoundaryDistance firstIndex frequency 0 radius (firstRaw 0) (finalRaw 0) +
          ∫ current in (0 : ℝ)..time,
            constant * canonicalExteriorCoefficientPairSeries firstFamily finalFamily firstIndex finalIndex current +
            constant * |frequency| * radius ^ 2 *
              firstFamily.canonicalExteriorCommonBoundaryDistance firstIndex frequency current radius (firstRaw current) (finalRaw current) ∧
        firstFamily.canonicalExteriorCommonBoundaryDistance firstIndex frequency time radius (firstRaw time) (finalRaw time) ≤
          Real.exp (constant * |frequency| * radius ^ 2 * time) *
            (constant * firstFamily.canonicalExteriorCommonBoundaryDistance firstIndex frequency 0 radius (firstRaw 0) (finalRaw 0) +
              ∫ current in (0 : ℝ)..time, Real.exp (-(constant * |frequency| * radius ^ 2) * current) *
                (constant * canonicalExteriorCoefficientPairSeries firstFamily finalFamily firstIndex finalIndex current)) := by
  obtain ⟨caps, pointConstant, pointOne, points⟩ := exists_canonical_common_boundary_forcing_rate
  obtain ⟨quadraticPhysical, quadraticPhysicalPositive, spectralRadius, spectralPositive, _, _, quadraticEvolution⟩ :=
    canonicalExteriorCommonQuadraticCoordinate_exists_material_evolution_ball
  obtain ⟨angularPhysical, angularPhysicalPositive, _, _, angularEvolution⟩ :=
    canonicalExteriorCommonNormalizedPhysicalCoordinate_exists_material_evolution_ball
  let physicalRadius := min quadraticPhysical angularPhysical
  let groupBound := diskPhysicalGroupBound + 1
  let constant := groupBound * pointConstant
  have groupOne : 1 ≤ groupBound := by dsimp only [groupBound]; linarith [diskPhysicalGroupBound_nonnegative]
  have groupNonnegative : 0 ≤ groupBound := by linarith
  have pointNonnegative : 0 ≤ pointConstant := by linarith
  have constantOne : 1 ≤ constant := by
    have scaled := mul_le_mul_of_nonneg_left pointOne groupNonnegative
    dsimp only [constant]
    nlinarith only [scaled, groupOne]
  have groupLe : groupBound ≤ constant := by
    have scaled := mul_le_mul_of_nonneg_left pointOne groupNonnegative
    simpa only [mul_one, constant] using scaled
  refine ⟨caps, physicalRadius, lt_min quadraticPhysicalPositive angularPhysicalPositive,
    spectralRadius, spectralPositive, constant, constantOne, ?_⟩
  intro firstCount finalCount firstFamily finalFamily firstIndex finalIndex frequency firstDistance finalDistance weight mass radius horizon
    firstRaw finalRaw firstResidual finalResidual sourceDifference radiusNonnegative horizonNonnegative
    firstQuadraticContinuous finalQuadraticContinuous firstAngularContinuous finalAngularContinuous
    firstQuadraticForcingContinuous finalQuadraticForcingContinuous firstAngularForcingContinuous finalAngularForcingContinuous
    coefficientContinuous actual
  have quadraticEquation (raw : ℝ → PeriodicC1HolderHalf) (residual source : PeriodicC1HolderHalf) (time : ℝ)
      (physicalInside : ‖firstFamily.canonicalExteriorCommonPhysicalCoordinate firstIndex frequency time (diskPhysicalSpectralChart (raw time)) - standardCircleBanach‖ ≤ physicalRadius)
      (spectralInside : ‖firstFamily.canonicalExteriorCommonNormalizedPhysicalCoordinate firstIndex frequency time (diskPhysicalSpectralChart (raw time))‖ ≤ spectralRadius)
      (equation : HasDerivAt (fun current => firstFamily.canonicalExteriorCommonPhysicalCoordinate firstIndex frequency current (diskPhysicalSpectralChart (raw current)))
        (frequency • diskEulerRotatingField (firstFamily.canonicalExteriorCommonPhysicalCoordinate firstIndex frequency time (diskPhysicalSpectralChart (raw time))) +
          residual + firstFamily.canonicalExteriorCommonPhysicalDerivative firstIndex frequency time (diskPhysicalSpectralChart (raw time)) source) time) :
      HasDerivAt (fun current => firstFamily.canonicalExteriorCommonQuadraticCoordinate firstIndex frequency current (diskPhysicalSpectralChart (raw current)))
        ((frequency • diskRotatingDerivative) (firstFamily.canonicalExteriorCommonQuadraticCoordinate firstIndex frequency time (diskPhysicalSpectralChart (raw time))) +
          firstFamily.canonicalExteriorCommonQuadraticMaterialForcing firstIndex frequency time (diskPhysicalSpectralChart (raw time)) residual source) time := by
    have transformed := by
      with_reducible_and_instances
        exact quadraticEvolution firstFamily firstIndex
          (curve := fun current => diskPhysicalSpectralChart (raw current)) (frequency := frequency) (time := time)
          residual source (physicalInside.trans (min_le_left _ _)) spectralInside equation
    with_reducible_and_instances
      simpa only [canonicalExteriorCommonQuadraticMaterialForcing, ContinuousLinearMap.smul_apply, add_assoc] using transformed.2.1
  have angularEquation (raw : ℝ → PeriodicC1HolderHalf) (residual source : PeriodicC1HolderHalf) (time : ℝ)
      (physicalInside : ‖firstFamily.canonicalExteriorCommonPhysicalCoordinate firstIndex frequency time (diskPhysicalSpectralChart (raw time)) - standardCircleBanach‖ ≤ physicalRadius)
      (equation : HasDerivAt (fun current => firstFamily.canonicalExteriorCommonPhysicalCoordinate firstIndex frequency current (diskPhysicalSpectralChart (raw current)))
        (frequency • diskEulerRotatingField (firstFamily.canonicalExteriorCommonPhysicalCoordinate firstIndex frequency time (diskPhysicalSpectralChart (raw time))) +
          residual + firstFamily.canonicalExteriorCommonPhysicalDerivative firstIndex frequency time (diskPhysicalSpectralChart (raw time)) source) time) :
      HasDerivAt (fun current => firstFamily.canonicalExteriorCommonTrueAngularCoordinate firstIndex frequency current (diskPhysicalSpectralChart (raw current)))
        (firstFamily.canonicalExteriorCommonTrueAngularForcing firstIndex frequency time (diskPhysicalSpectralChart (raw time)) residual source) time := by
    have transformed := by
      with_reducible_and_instances
        exact (angularEvolution firstFamily firstIndex
          (curve := fun current => diskPhysicalSpectralChart (raw current)) (frequency := frequency) (time := time)
          residual source (physicalInside.trans (min_le_right _ _)) equation).2.1
    have composed := by
      with_reducible_and_instances
        exact diskNeutralCLM.hasFDerivAt.comp_hasDerivAt time transformed
    with_reducible_and_instances
      simpa only [canonicalExteriorCommonTrueAngularCoordinate, canonicalExteriorCommonTrueAngularForcing, Function.comp_def, map_add, map_smul] using composed
  have groupZero : diskPhysicalScaledGroup frequency 0 = ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
    simpa only [diskPhysicalScaledGroup, mul_zero] using diskPhysicalGroup_zero
  have groupAddition (first final : ℝ) : diskPhysicalScaledGroup frequency (first + final) =
      (diskPhysicalScaledGroup frequency first).comp (diskPhysicalScaledGroup frequency final) := by
    simpa only [diskPhysicalScaledGroup, mul_add] using diskPhysicalGroup_add (frequency * first) (frequency * final)
  have groupEstimate (time : ℝ) (value : PeriodicC1HolderHalf) : ‖diskPhysicalScaledGroup frequency time value‖ ≤ groupBound * ‖value‖ :=
    (diskPhysicalScaledGroup_norm_bound frequency time value).trans
      (mul_le_mul_of_nonneg_right (by dsimp only [groupBound]; linarith : diskPhysicalGroupBound ≤ groupBound) (norm_nonneg value))
  have history := quadraticNeutral_pair_history_of_interior
    (source := fun current => pointConstant * canonicalExteriorCoefficientPairSeries firstFamily finalFamily firstIndex finalIndex current)
    (rate := pointConstant * |frequency| * radius ^ 2)
    (diskPhysicalScaledGroup frequency) (frequency • diskRotatingDerivative) groupZero groupAddition
    (diskPhysicalScaledGroup_generator frequency) groupOne groupEstimate radiusNonnegative
    (by positivity : 0 ≤ pointConstant * |frequency| * radius ^ 2) horizonNonnegative
    firstQuadraticContinuous finalQuadraticContinuous firstAngularContinuous finalAngularContinuous
    firstQuadraticForcingContinuous finalQuadraticForcingContinuous firstAngularForcingContinuous finalAngularForcingContinuous
    (continuousOn_const.mul coefficientContinuous)
    (fun time inside => by
      obtain ⟨comparison, firstLiteral, finalLiteral, sourceLiteral, firstPhysical, finalPhysical, firstSpectral, finalSpectral, firstEquation, finalEquation⟩ := actual time inside
      exact quadraticEquation firstRaw (firstResidual time) 0 time firstPhysical firstSpectral (by simpa only [map_zero, add_zero] using firstEquation))
    (fun time inside => by
      obtain ⟨comparison, firstLiteral, finalLiteral, sourceLiteral, firstPhysical, finalPhysical, firstSpectral, finalSpectral, firstEquation, finalEquation⟩ := actual time inside
      exact quadraticEquation finalRaw (finalResidual time) (sourceDifference time) time finalPhysical finalSpectral finalEquation)
    (fun time inside => by
      obtain ⟨comparison, firstLiteral, finalLiteral, sourceLiteral, firstPhysical, finalPhysical, firstSpectral, finalSpectral, firstEquation, finalEquation⟩ := actual time inside
      exact angularEquation firstRaw (firstResidual time) 0 time firstPhysical (by simpa only [map_zero, add_zero] using firstEquation))
    (fun time inside => by
      obtain ⟨comparison, firstLiteral, finalLiteral, sourceLiteral, firstPhysical, finalPhysical, firstSpectral, finalSpectral, firstEquation, finalEquation⟩ := actual time inside
      exact angularEquation finalRaw (finalResidual time) (sourceDifference time) time finalPhysical finalEquation)
    (fun time inside => by
      obtain ⟨comparison, firstLiteral, finalLiteral, sourceLiteral, firstPhysical, finalPhysical, firstSpectral, finalSpectral, firstEquation, finalEquation⟩ := actual time inside
      have bound := points firstFamily finalFamily firstIndex finalIndex frequency time firstDistance finalDistance weight mass radius (firstRaw time) (finalRaw time) comparison
      rw [← firstLiteral, ← finalLiteral, ← sourceLiteral] at bound
      exact bound.trans_eq (by
        simp only [CanonicalCommonBoundaryPairAt.boundaryDistance, CanonicalCommonBoundaryPairAt.coefficientDifferenceSeries,
          canonicalExteriorCoefficientPairSeries]
        ring))
  intro time inside
  have bound := history time inside
  have initialNonnegative : 0 ≤ firstFamily.canonicalExteriorCommonBoundaryDistance firstIndex frequency 0 radius (firstRaw 0) (finalRaw 0) := by
    unfold canonicalExteriorCommonBoundaryDistance weightedBoundaryPairDistance
    positivity
  have initialBound := mul_le_mul_of_nonneg_right groupLe initialNonnegative
  have integralResult := bound.1.trans (add_le_add_right initialBound _)
  have exponentialResult := bound.2.trans (mul_le_mul_of_nonneg_left (add_le_add_right initialBound _) (Real.exp_pos _).le)
  with_reducible_and_instances
    constructor
    · simpa only [canonicalExteriorCommonBoundaryDistance, constant, mul_assoc] using integralResult
    · simpa only [canonicalExteriorCommonBoundaryDistance, constant, mul_assoc] using exponentialResult

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
