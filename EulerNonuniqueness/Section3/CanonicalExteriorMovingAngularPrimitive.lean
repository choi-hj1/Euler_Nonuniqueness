import EulerNonuniqueness.Section3.RelabeledPrimitiveMovingSeries
import EulerNonuniqueness.Section3.CanonicalExteriorPrimitiveRawEquation
import EulerNonuniqueness.Section3.CanonicalExteriorStaticPairRelative
import EulerNonuniqueness.Section6.UniformExteriorMovingAngularEnvelopes

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup
  forcingModeC1ComplexModule forcingModeC1ComplexSpace exteriorPowerSeriesOperatorSpace

open EulerNonuniqueness.Section6

theorem canonicalExteriorForcingPrimitive_hasDerivAt_moving_angular_raw {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count)
    (angular angularVelocity : ℝ → PeriodicC1HolderHalf)
    {frequency left right time distance weight mass speed : ℝ}
    (nonzero : frequency ≠ 0) (member : time ∈ Ioo left right)
    (angularSmall : ‖angular time‖ < 1 / 2)
    (realValues : ∀ label, star ((angular time).val.1 label) = (angular time).val.1 label)
    (nearby : ‖diskRelabelCurve (angular time) 1 - standardCircleBanach‖ < 1 / 3)
    (cutoff : ‖diskRelabelCurve (angular time) 1 - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (angularEquation : ∀ current, current ∈ Ioo left right → HasDerivAt angular (angularVelocity current) current)
    (baseBounds : ∀ current, current ∈ Ioo left right →
      ‖diskRelabelCurve (angular current) 1‖ < 3 ∧
      ‖fderiv ℝ (fun parameter => diskRelabelCurve parameter 1) (angular current) (angularVelocity current)‖ ≤ speed)
    (positive : 0 < distance) (weightNonnegative : 0 ≤ weight) (massNonnegative : 0 ≤ mass)
    (small : 192 * (family.patch index).radius ≤ distance)
    (inside : ∀ current ∈ Ioo left right, ∀ source,
      current ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (material : ∀ current ∈ Ioo left right, ∀ source label,
      (family.patch source).boundaryVelocity current label =
        biotSavart (family.vorticity current) ((family.patch source).boundary current label))
    (centered : ∀ current ∈ Ioo left right,
      (family.patch index).center =ᶠ[nhds current] (family.patch index).centroid)
    (centerGaps : ∀ current ∈ Ioo left right, ∀ source ∈ Finset.univ.erase index,
      distance + 3 * (family.patch source).radius ≤
        ‖(family.patch index).center current - (family.patch source).center current‖)
    (weightBound : ∀ current ∈ Ioo left right, (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) current) ((family.patch index).center current) position) ≤ weight)
    (massBound : ∀ current ∈ Ioo left right, (∫ position, |family.patchVorticity current index position|) ≤ mass) :
    HasDerivAt (fun current => family.relabeledExteriorForcingPrimitive index (angular current) frequency current)
      (frequency • fderiv ℝ diskEulerRotatingField (diskRelabelCurve (angular time) 1)
          (family.relabeledExteriorForcingPrimitive index (angular time) frequency time) +
        family.canonicalProjectedExteriorContourField index time distance positive
          (by linarith [(family.patch index).radius_positive])
          (family.exterior_domain_gap_of_center_gaps index (centerGaps time member))
          (Circle.exp (frequency * time / 2)) (diskRelabelCurve (angular time) 1) +
        fixedRelabelEquivalence (angular time) angularSmall
          (family.exteriorAmplitudeDerivativePrimitive index frequency time) +
        relabeledPrimitiveAngularDerivative frequency
          (fun degree => family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
            (family.patch index).radius (degree + 1)) time (angular time) (angularVelocity time)) time := by
  have separated := fun current (currentMember : current ∈ Ioo left right) =>
    family.exterior_domain_gap_of_center_gaps index (centerGaps current currentMember)
  obtain ⟨valueEnvelope, derivativeEnvelope, _, summableValue, summableDerivative, bounds⟩ :=
    family.exists_uniform_exteriorCoefficient_moving_angular_envelopes index (Ioo left right) positive small
      weightNonnegative massNonnegative (fun current currentMember => inside current currentMember index)
      (fun current currentMember => material current currentMember index) centered separated weightBound massBound
  let amplitude : ℕ → ℝ → ℂ := fun degree => family.exteriorTaylorCoefficient (Finset.univ.erase index)
    (family.patch index).center (family.patch index).radius (degree + 1)
  let amplitudeDerivative : ℕ → ℝ → ℂ := family.exteriorMaterialCoefficientDerivative index
  let baseVelocity := fun current =>
    fderiv ℝ (fun parameter => diskRelabelCurve parameter 1) (angular current) (angularVelocity current)
  have amplitudeEquation : ∀ degree current, current ∈ Ioo left right →
      HasDerivAt (amplitude degree) (amplitudeDerivative degree current) current := by
    intro degree current currentMember
    exact family.exteriorTaylorCoefficient_hasDerivAt_material index degree
      (fun source _ => inside current currentMember source)
      (fun source _ => material current currentMember source) positive (centerGaps current currentMember)
  have baseEquation : ∀ current, current ∈ Ioo left right →
      HasDerivAt (fun later => diskRelabelCurve (angular later) 1) (baseVelocity current) current := by
    intro current currentMember
    exact (diskRelabelMap_analyticAt (angular current)).differentiableAt.hasFDerivAt.comp_hasDerivAt
      current (angularEquation current currentMember)
  have frozen := family.canonicalExteriorForcingPrimitive_hasDerivAt_raw index (angular time) angularSmall realValues
    nearby cutoff nonzero member positive weightNonnegative massNonnegative
    (by linarith [(family.patch index).radius_positive]) inside material centered centerGaps weightBound massBound
  have weighted := family.canonicalExteriorStaticCoefficient_summable_weight96 index time distance positive small (separated time member)
  have actual := relabeledForcingPrimitiveSeries_hasDerivAt_moving_of_frozen nonzero amplitude amplitudeDerivative
    valueEnvelope derivativeEnvelope angular baseVelocity amplitudeEquation baseEquation
    (fun degree current currentMember => bounds current currentMember degree) baseBounds
    summableValue summableDerivative member member weighted frozen
  with_reducible_and_instances
    simpa only [relabeledExteriorForcingPrimitive, relabeledPrimitiveAngularDerivative,
      ContinuousLinearMap.comp_apply, amplitude, baseVelocity] using actual

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
