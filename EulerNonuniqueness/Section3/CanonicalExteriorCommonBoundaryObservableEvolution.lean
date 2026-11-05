import EulerNonuniqueness.Section3.CanonicalExteriorCommonBoundaryForcingRate

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

local instance commonBoundaryObservableEvolutionC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem canonicalExteriorCommonPhysicalCoordinate_exists_joint_observable_evolution_ball :
    ∃ physicalRadius > 0, ∃ spectralRadius > 0,
    ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
      (curve : ℝ → PeriodicC1HolderHalf) {frequency time : ℝ} (residual source : PeriodicC1HolderHalf),
    ‖family.canonicalExteriorCommonPhysicalCoordinate index frequency time (curve time) - standardCircleBanach‖ ≤ physicalRadius →
    ‖family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (curve time)‖ ≤ spectralRadius →
    HasDerivAt (fun current => family.canonicalExteriorCommonPhysicalCoordinate index frequency current (curve current))
      (frequency • diskEulerRotatingField (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (curve time)) +
        residual + family.canonicalExteriorCommonPhysicalDerivative index frequency time (curve time) source) time →
    HasDerivAt (fun current => family.canonicalExteriorCommonQuadraticCoordinate index frequency current (curve current))
      ((frequency • diskRotatingDerivative) (family.canonicalExteriorCommonQuadraticCoordinate index frequency time (curve time)) +
        family.canonicalExteriorCommonQuadraticMaterialForcing index frequency time (curve time) residual source) time ∧
    HasDerivAt (fun current => family.canonicalExteriorCommonTrueAngularCoordinate index frequency current (curve current))
      (family.canonicalExteriorCommonTrueAngularForcing index frequency time (curve time) residual source) time := by
  obtain ⟨quadraticRadius, quadraticPositive, spectralRadius, spectralPositive, _, _, quadraticEvolution⟩ :=
    canonicalExteriorCommonQuadraticCoordinate_exists_material_evolution_ball
  obtain ⟨angularRadius, angularPositive, _, _, angularEvolution⟩ :=
    canonicalExteriorCommonNormalizedPhysicalCoordinate_exists_material_evolution_ball
  refine ⟨min quadraticRadius angularRadius, lt_min quadraticPositive angularPositive, spectralRadius, spectralPositive, ?_⟩
  intro count family index curve frequency time residual source physicalInside spectralInside equation
  have quadratic := by
    with_reducible_and_instances
      exact (quadraticEvolution family index (curve := curve) (frequency := frequency) (time := time)
        residual source (physicalInside.trans (min_le_left _ _)) spectralInside equation).2.1
  have angular := by
    with_reducible_and_instances
      exact (angularEvolution family index (curve := curve) (frequency := frequency) (time := time)
        residual source (physicalInside.trans (min_le_right _ _)) equation).2.1
  have composed := by
    with_reducible_and_instances
      exact diskNeutralCLM.hasFDerivAt.comp_hasDerivAt time angular
  with_reducible_and_instances
    constructor
    · simpa only [canonicalExteriorCommonQuadraticMaterialForcing, ContinuousLinearMap.smul_apply, add_assoc] using quadratic
    · simpa only [canonicalExteriorCommonTrueAngularCoordinate, canonicalExteriorCommonTrueAngularForcing,
        Function.comp_def, map_add, map_smul] using composed

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
