import EulerNonuniqueness.Section3.CanonicalExteriorCommonC1CurveEquation
import EulerNonuniqueness.Section3.MovingContourInteriorMaterialNeighborhood
import EulerNonuniqueness.Section3.MovingCanonicalShapeEquation

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

local instance movingCommonPairEquationC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

open EulerNonuniqueness.Section6

theorem exists_uniform_actual_common_pair_equation_radius :
    ∃ radius > 0,
    ∀ {firstCount finalCount : ℕ} {firstConfiguration : FiniteContourConfiguration firstCount}
      {finalConfiguration : FiniteContourConfiguration finalCount}
      {firstCenter firstShape firstGap firstMargin firstBackward firstForward : ℝ}
      {finalCenter finalShape finalGap finalMargin finalBackward finalForward : ℝ}
      {firstInitial : MovingContourState firstCount} {finalInitial : MovingContourState finalCount}
      (firstTrajectory : MovingCentroidGaugeTrajectory firstConfiguration firstCenter firstShape firstGap firstMargin firstBackward firstForward firstInitial)
      (finalTrajectory : MovingCentroidGaugeTrajectory finalConfiguration finalCenter finalShape finalGap finalMargin finalBackward finalForward finalInitial)
      (firstIndex : Fin firstCount) (finalIndex : Fin finalCount)
      {horizon time firstDistance finalDistance weight mass : ℝ},
    (∀ index, firstInitial.2.2 index = standardCircleBanach) →
    (∀ index, finalInitial.2.2 index = standardCircleBanach) → finalInitial.1 = 0 →
    0 < firstMargin → 0 < finalMargin → horizon < firstForward → horizon < finalForward →
    (∀ current ∈ Icc 0 horizon, firstMargin ≤ infDist (firstTrajectory.curve current)
      (firstConfiguration.movingStateAdmissible firstCenter firstShape firstGap)ᶜ) →
    (∀ current ∈ Icc 0 horizon, finalMargin ≤ infDist (finalTrajectory.curve current)
      (finalConfiguration.movingStateAdmissible finalCenter finalShape finalGap)ᶜ) →
    firstConfiguration.density firstIndex ≠ 0 → finalConfiguration.density finalIndex = firstConfiguration.density firstIndex →
    ∀ (member : time ∈ Ioo 0 horizon) (firstPositive : 0 < firstDistance) (finalPositive : 0 < finalDistance),
    0 ≤ weight → 0 ≤ mass →
    ∀ (firstScale : 192 * (firstTrajectory.movingFamily.patch firstIndex).radius ≤ firstDistance)
      (finalScale : 192 * (finalTrajectory.movingFamily.patch finalIndex).radius ≤ finalDistance),
    (∀ᶠ current in 𝓝 time,
      (∀ source ∈ Finset.univ.erase firstIndex, firstDistance + 3 * (firstTrajectory.movingFamily.patch source).radius ≤
        ‖(firstTrajectory.movingFamily.patch firstIndex).center current - (firstTrajectory.movingFamily.patch source).center current‖) ∧
      (∫ position, inverseSquareVorticityWeight
        (firstTrajectory.movingFamily.subfamilyVorticity (Finset.univ.erase firstIndex) current)
        ((firstTrajectory.movingFamily.patch firstIndex).center current) position) ≤ weight ∧
      (∫ position, |firstTrajectory.movingFamily.patchVorticity current firstIndex position|) ≤ mass) →
    ∀ (finalSeparated : ∀ source ∈ Finset.univ.erase finalIndex, ∀ position ∈ (finalTrajectory.movingFamily.patch source).domain time,
      finalDistance ≤ ‖(finalTrajectory.movingFamily.patch finalIndex).center time - position‖),
    ‖(finalTrajectory.curve time).2.2 finalIndex - standardCircleBanach‖ < radius →
    ∃ (firstSeparated : ∀ source ∈ Finset.univ.erase firstIndex, ∀ position ∈ (firstTrajectory.movingFamily.patch source).domain time,
        firstDistance ≤ ‖(firstTrajectory.movingFamily.patch firstIndex).center time - position‖)
      (angularSmall : ‖diskNeutralCLM (diskPhysicalSpectralCoordinate ((finalTrajectory.curve time).2.2 finalIndex))‖ < 1 / 2),
    HasDerivAt (fun current => firstTrajectory.movingFamily.canonicalExteriorCommonPhysicalCoordinate firstIndex
        (firstConfiguration.density firstIndex) current ((finalTrajectory.curve current).2.2 finalIndex))
      ((firstConfiguration.density firstIndex) • diskEulerRotatingField
          (firstTrajectory.movingFamily.canonicalExteriorCommonPhysicalCoordinate firstIndex
            (firstConfiguration.density firstIndex) time ((finalTrajectory.curve time).2.2 finalIndex)) +
        firstTrajectory.movingFamily.canonicalExteriorCommonMaterialResidual firstIndex (firstConfiguration.density firstIndex)
          time firstDistance firstPositive (by linarith [(firstTrajectory.movingFamily.patch firstIndex).radius_positive])
          firstSeparated ((finalTrajectory.curve time).2.2 finalIndex) angularSmall +
        firstTrajectory.movingFamily.canonicalExteriorCommonPhysicalDerivative firstIndex (firstConfiguration.density firstIndex)
          time ((finalTrajectory.curve time).2.2 finalIndex)
          (finalTrajectory.movingFamily.canonicalProjectedExteriorContourField finalIndex time finalDistance finalPositive
              (by linarith [(finalTrajectory.movingFamily.patch finalIndex).radius_positive]) finalSeparated
              (Circle.exp (firstConfiguration.density firstIndex * time / 2)) ((finalTrajectory.curve time).2.2 finalIndex) -
            firstTrajectory.movingFamily.canonicalProjectedExteriorContourField firstIndex time firstDistance firstPositive
              (by linarith [(firstTrajectory.movingFamily.patch firstIndex).radius_positive]) firstSeparated
              (Circle.exp (firstConfiguration.density firstIndex * time / 2)) ((finalTrajectory.curve time).2.2 finalIndex))) time := by
  obtain ⟨radius, radiusPositive, equations⟩ :=
    FiniteMovingPatchFamily.canonicalExteriorCommonPhysicalCoordinate_exists_actual_C1_equation_radius
  refine ⟨radius, radiusPositive, ?_⟩
  intro firstCount finalCount firstConfiguration finalConfiguration firstCenter firstShape firstGap firstMargin firstBackward firstForward
    finalCenter finalShape finalGap finalMargin finalBackward finalForward firstInitial finalInitial firstTrajectory finalTrajectory
    firstIndex finalIndex horizon time firstDistance finalDistance weight mass firstCircles finalCircles finalClock
    firstMarginPositive finalMarginPositive firstBefore finalBefore firstSafe finalSafe nonzero densityIdentity member
    firstPositive finalPositive weightNonnegative massNonnegative firstScale finalScale geometry finalSeparated small
  obtain ⟨neighborhood⟩ := firstTrajectory.exists_materialNeighborhood_of_interior_nonstrict_margin
    firstCircles firstMarginPositive firstIndex member firstBefore firstSafe geometry
  let left := max neighborhood.left 0
  let right := min neighborhood.right horizon
  have nextMember : time ∈ Ioo left right :=
    ⟨max_lt neighborhood.member.1 member.1, lt_min neighborhood.member.2 member.2⟩
  have inNeighborhood {current : ℝ} (inside : current ∈ Ioo left right) : current ∈ Ioo neighborhood.left neighborhood.right :=
    ⟨(le_max_left _ _).trans_lt inside.1, inside.2.trans_le (min_le_left _ _)⟩
  have inHorizon {current : ℝ} (inside : current ∈ Ioo left right) : current ∈ Ioo 0 horizon :=
    ⟨(le_max_right _ _).trans_lt inside.1, inside.2.trans_le (min_le_right _ _)⟩
  let curve := fun current => (finalTrajectory.curve current).2.2 finalIndex
  let velocity := fun current => (finalTrajectory.velocity current).2.2 finalIndex
  have curveContinuous : Continuous curve :=
    (continuous_apply finalIndex).comp (continuous_snd.comp (continuous_snd.comp finalTrajectory.continuous))
  have velocityContinuous : Continuous velocity :=
    (continuous_apply finalIndex).comp (continuous_snd.comp (continuous_snd.comp finalTrajectory.velocity_continuous))
  have curveEquation (current : ℝ) (inside : current ∈ Ioo left right) : HasDerivAt curve (velocity current) current :=
    finalTrajectory.shape_component_hasDerivAt
      ⟨by linarith [(inHorizon inside).1, finalTrajectory.backward_positive], (inHorizon inside).2.trans finalBefore⟩ finalIndex
  obtain ⟨angularSmall, actual⟩ := equations firstTrajectory.movingFamily firstIndex curve velocity curveContinuous velocityContinuous
    nonzero nextMember curveEquation small firstPositive weightNonnegative massNonnegative firstScale
    (fun current inside => neighborhood.inside current (inNeighborhood inside))
    (fun current inside => neighborhood.material current (inNeighborhood inside))
    (fun current inside => neighborhood.centered current (inNeighborhood inside))
    (fun current inside => neighborhood.centerGaps current (inNeighborhood inside))
    (fun current inside => neighborhood.weightBound current (inNeighborhood inside))
    (fun current inside => neighborhood.massBound current (inNeighborhood inside))
  have finalCentered : ∀ index, contourCentroidFunctional (finalInitial.2.2 index) = 0 := by
    intro index
    rw [finalCircles index, contourCentroidFunctional_standardCircle_zero]
  have rawEquation := finalTrajectory.shape_hasDerivAt_canonical_of_margin finalClock finalCentered finalMarginPositive
    (show time ∈ Ioo (-finalBackward) finalForward from
      ⟨by linarith [member.1, finalTrajectory.backward_positive], member.2.trans finalBefore⟩)
    ⟨member.1.le, member.2.le⟩ finalSafe finalIndex finalPositive
    (by linarith [(finalTrajectory.movingFamily.patch finalIndex).radius_positive]) finalSeparated
  rw [densityIdentity] at rawEquation
  have velocityIdentity := (curveEquation time nextMember).unique rawEquation
  rw [velocityIdentity] at actual
  have firstSeparated := firstTrajectory.movingFamily.exterior_domain_gap_of_center_gaps firstIndex
    (neighborhood.centerGaps time neighborhood.member)
  refine ⟨firstSeparated, angularSmall, ?_⟩
  with_reducible_and_instances
    simpa only [curve, velocity, add_sub_cancel_left] using actual

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
