import EulerNonuniqueness.Section3.MovingStrainAngularCorrectionDerivative
import EulerNonuniqueness.Section3.RelabeledPrimitiveAngularDerivative
import EulerNonuniqueness.Section3.CanonicalExteriorStaticPairRelative
import EulerNonuniqueness.General.CommonMovingAffineCoordinate

noncomputable section

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  powerFirstJetOperatorGroup exteriorPowerSeriesOperatorSpace gaugeOperatorUniformSecondGroup
  affineCoefficientOperatorGroup affineCoefficientOperatorModule affineCoefficientOperatorSpace

def canonicalExteriorAffineAngularDerivative {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (angular : PeriodicC1HolderHalf) (frequency time : ℝ)
    (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  -relabeledPrimitiveAngularDerivative frequency
      (fun degree => family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
        (family.patch index).radius (degree + 1)) time angular -
    (ContinuousLinearMap.apply ℝ PeriodicC1HolderHalf (data - diskRelabelCurve angular 1)).comp
      (frequency⁻¹ • movingStrainAngularCorrectionDerivative angular
        (family.exteriorStrainModulatedCoefficient index frequency time)) +
    (family.exteriorStrainPhysicalCorrection index angular frequency time).comp
      (fderiv ℝ (fun current => diskRelabelCurve current 1) angular)

theorem canonicalExteriorAffineAngularDerivative_apply {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (angular : PeriodicC1HolderHalf) (frequency time : ℝ)
    (data velocity : PeriodicC1HolderHalf) :
    family.canonicalExteriorAffineAngularDerivative index angular frequency time data velocity =
      -relabeledPrimitiveAngularDerivative frequency
        (fun degree => family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
          (family.patch index).radius (degree + 1)) time angular velocity -
      frequency⁻¹ • (movingStrainAngularCorrectionDerivative angular
        (family.exteriorStrainModulatedCoefficient index frequency time) velocity
        (data - diskRelabelCurve angular 1)) +
      family.exteriorStrainPhysicalCorrection index angular frequency time
        (fderiv ℝ (fun current => diskRelabelCurve current 1) angular velocity) := by
  with_reducible_and_instances
    simp only [canonicalExteriorAffineAngularDerivative, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply]

theorem exteriorStrainPhysicalCorrection_hasFDerivAt_angular {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (angular : PeriodicC1HolderHalf)
    (frequency time : ℝ) (regular : DifferentiableAt ℝ movingStrainAngularCoefficient angular) :
    HasFDerivAt (fun current => family.exteriorStrainPhysicalCorrection index current frequency time)
      (frequency⁻¹ • movingStrainAngularCorrectionDerivative angular
        (family.exteriorStrainModulatedCoefficient index frequency time)) angular := by
  exact (movingStrainRealCorrectionCLM_hasFDerivAt_angular angular
    (family.exteriorStrainModulatedCoefficient index frequency time) regular).const_smul frequency⁻¹

theorem canonicalExteriorAffineCoordinate_hasFDerivAt_angular {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (angular : PeriodicC1HolderHalf)
    {frequency time : ℝ} (nonzero : frequency ≠ 0) (data : PeriodicC1HolderHalf)
    (bounded : ‖diskRelabelCurve angular 1‖ < 3)
    (weighted : Summable (fun degree => (96 : ℝ) ^ (degree + 1) *
      ‖family.canonicalExteriorStaticCoefficient index time degree‖))
    (regular : DifferentiableAt ℝ movingStrainAngularCoefficient angular) :
    HasFDerivAt (fun current => family.canonicalExteriorAffineCoordinate index current frequency time data)
      (family.canonicalExteriorAffineAngularDerivative index angular frequency time data) angular := by
  have primitive := relabeledForcingPrimitiveSeries_hasFDerivAt_angular nonzero
    (fun degree => family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
      (family.patch index).radius (degree + 1)) time angular bounded weighted
  have correction := family.exteriorStrainPhysicalCorrection_hasFDerivAt_angular index angular frequency time regular
  have base := (diskRelabelMap_analyticAt angular).differentiableAt.hasFDerivAt
  have actual := ((hasFDerivAt_const data angular).sub primitive).sub
    (correction.clm_apply ((hasFDerivAt_const data angular).sub base))
  with_reducible_and_instances
    convert (config := { transparency := .all }) actual using 1
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · simp only [canonicalExteriorAffineCoordinate, relabeledExteriorForcingPrimitive]
    · apply ContinuousLinearMap.ext
      intro direction
      simp only [canonicalExteriorAffineAngularDerivative, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.neg_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply,
        map_neg, sub_zero, zero_sub]
      abel

theorem canonicalExteriorAffineCoordinate_exists_uniform_angular_derivative :
    ∃ radius > 0,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (angular data : PeriodicC1HolderHalf), ‖angular‖ ≤ radius →
      ∀ {frequency time distance : ℝ}, frequency ≠ 0 → 0 < distance →
      192 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      HasFDerivAt (fun current => family.canonicalExteriorAffineCoordinate index current frequency time data)
        (family.canonicalExteriorAffineAngularDerivative index angular frequency time data) angular := by
  obtain ⟨correctionRadius, correctionPositive, _, _, correction, _, _⟩ :=
    movingStrainAngularCorrectionDerivative_exists_uniform_ball
  have near : ∀ᶠ angular in 𝓝 (0 : PeriodicC1HolderHalf), ‖diskRelabelCurve angular 1‖ < 3 := by
    have baseZero : diskRelabelCurve (0 : PeriodicC1HolderHalf) 1 = standardCircleBanach := by
      apply PeriodicC1HolderHalf.ext_value
      intro label
      rw [diskRelabelCurve_value]
      change Complex.exp ((1 : ℂ) * (Complex.I * 0)) * standardCircle label = standardCircle label
      simp
    exact (diskRelabelMap_analyticAt 0).continuousAt.norm.eventually
      (gt_mem_nhds (by
        change ‖diskRelabelCurve (0 : PeriodicC1HolderHalf) 1‖ < 3
        rw [baseZero]
        linarith [standardCircleBanach_norm_bound]))
  obtain ⟨baseRadius, basePositive, base⟩ := Metric.eventually_nhds_iff.mp near
  refine ⟨min correctionRadius (baseRadius / 2), by positivity, ?_⟩
  intro count family index angular data angularInside frequency time distance nonzero positive small separated
  have bounded := base (show dist angular 0 < baseRadius by
    rw [dist_zero_right]
    exact (angularInside.trans (min_le_right _ _)).trans_lt (by linarith))
  exact family.canonicalExteriorAffineCoordinate_hasFDerivAt_angular index angular nonzero data bounded
    (family.canonicalExteriorStaticCoefficient_summable_weight96 index time distance positive small separated)
    (correction angular (angularInside.trans (min_le_left _ _)))

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
