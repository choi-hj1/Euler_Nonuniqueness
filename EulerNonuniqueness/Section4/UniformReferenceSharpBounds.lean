import EulerNonuniqueness.Section4.UniformReferenceSharpShape
import EulerNonuniqueness.Section4.ReferenceSharpOuterDisplacement
import EulerNonuniqueness.Section4.UniformReferencePhaseData
import EulerNonuniqueness.General.PhaseDilationControl
import EulerNonuniqueness.Section4.ReferenceDiagonalFromImpulse
import EulerNonuniqueness.General.WeightedPrimitiveBound
import EulerNonuniqueness.Section4.ReferenceIntegratedImpulse
import EulerNonuniqueness.Section4.ReferenceSharpInteriorTube
import EulerNonuniqueness.Section4.ReferenceNeutralPrefixSafety

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_actual_reference_sharp_bounds_radius :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧
      ∀ (scales : Scales), 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ (bound : ℝ), 0 ≤ bound → ∃ constant ≥ (1 : ℝ),
      ∀ᶠ frequency : ℝ in atTop,
      let changed : Scales := {scales with frequency := frequency}
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)),
      (∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * changed.amplitude * changed.omega (index.val + 1) ^ 4) →
      (∀ (index : Fin count) (patch : Fin 4), (family.patch (finProdFinEquiv (index, patch))).radius = changed.radius (index.val + 1)) →
      ∀ (evolution : FinitePatchEvolution changed family.patchMotion 2), ∀ {threshold : ℝ}, ∀ {phase unstable : Fin count → ℝ},
      ReferenceInitialDisks changed family.patchMotion phase unstable threshold → threshold ≤ 1 / 2 →
      (∀ time ∈ Icc 0 2, ∀ source, time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime) →
      (∀ time ∈ Icc 0 2, ∀ source label, (family.patch source).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch source).boundary time label)) →
      (∀ time ∈ Icc 0 2, ∀ index : Fin count, changed.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion time index) →
      (∀ time ∈ Icc 0 2, ∀ index : Fin count, diagonalDifference family.patchMotion time index ≤ 2 * changed.length (index.val + 1) ^ 2) →
      (∀ time ∈ Icc 0 2, ∀ index, |radialShape family.patchMotion time index| ≤ 1 / 2) →
      (∀ time ∈ Icc 0 2, ∀ index, ‖centroidAsymmetry family.patchMotion time index‖ ≤ changed.length (index.val + 1) / 64) →
      (∀ time ∈ Icc 0 2, ∀ receiver source : Fin count, receiver ≠ source →
        |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 2 ≤
          ‖quadrupoleCenter family.patchMotion time receiver - quadrupoleCenter family.patchMotion time source‖) →
      ∀ (deformation : ℝ → Fin count → ℝ),
      (∀ time ∈ Icc 0 2, ∀ index patch, BoundaryCloseToCircle changed family.patchMotion time index patch (deformation time index)) →
      (∀ time ∈ Icc 0 2, ∀ index, 0 ≤ deformation time index) →
      (∀ time ∈ Icc 0 2, ∀ index, deformation time index ≤ 1 / 16) →
      (∀ time ∈ Icc 0 2, ∀ index, deformation time index ≤ bound / changed.omega (index.val + 1) ^ 2) →
      (∀ time ∈ Icc 0 2, ∀ index, 0 < (negativeHalfDiagonal family.patchMotion time index / positiveHalfDiagonal family.patchMotion time index).im) →
      (∀ time ∈ Icc 0 2, ∀ index, |unstableShape family.patchMotion time index| ≤ radius ∧ |stableShape family.patchMotion time index| ≤ radius) →
      ∃ phaseLift : ℝ → Fin count → ℝ, ReferencePhaseLift family.patchMotion phase phaseLift ∧
        ReferenceSharpBounds changed family.patchMotion phase phaseLift constant := by
  obtain ⟨radius, radiusPositive, radiusSmall, shapeAll⟩ :=
    exists_uniform_actual_reference_sharp_shape_radius
  refine ⟨radius, radiusPositive, radiusSmall, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive bound boundNonnegative
  obtain ⟨shapeConstant, shapeOne, shapeEstimate⟩ :=
    shapeAll scales amplitudePositive ratioBound alphaPositive bound boundNonnegative
  obtain ⟨outerConstant, outerNonnegative, outerEstimate⟩ :=
    FiniteMovingPatchFamily.exists_uniform_reference_outer_displacement_bound scales.amplitude bound amplitudePositive boundNonnegative
  let constant := 1 + shapeConstant + outerConstant
  have shapeNonnegative : 0 ≤ shapeConstant := zero_le_one.trans shapeOne
  have constantOne : 1 ≤ constant := by dsimp only [constant]; linarith only [shapeNonnegative, outerNonnegative]
  have shapeConstantBound : shapeConstant ≤ constant := by dsimp only [constant]; linarith only [outerNonnegative]
  have outerConstantBound : outerConstant ≤ constant := by dsimp only [constant]; linarith only [shapeNonnegative]
  refine ⟨constant, constantOne, ?_⟩
  filter_upwards [shapeEstimate, eventually_ge_atTop (1 : ℝ),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 1000),
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1 / 1000),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency shapeEstimate frequencyBound lengths radii strainSmall hessianSmall
  dsimp only
  intro count family densityEquation radiusEquation evolution threshold phase unstable initial thresholdSmall inside material
    differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation deformation control nonnegative small deformationBound upper confined
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith
  have actualAmplitudePositive : 0 < changed.amplitude := amplitudePositive
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive 1
  have lengthPositive := changed.length_pos 1
  have lengthSmall (index : Fin count) : changed.length (index.val + 1) ≤ changed.location (index.val + 1) / 1000 := by
    simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using (lengths (index.val + 1)).le
  have radiusSmallPhysical (index : Fin count) : changed.radius (index.val + 1) ≤ changed.length (index.val + 1) / 1000 := by
    simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using (radii (index.val + 1)).le
  obtain ⟨phaseLift, lift, shape⟩ := shapeEstimate family densityEquation radiusEquation evolution initial thresholdSmall inside material
    differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation deformation control nonnegative small deformationBound upper confined
  have outer := outerEstimate family changed rfl densityEquation evolution (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 2) Subset.rfl frequencyBound ratioBound alphaPositive
    initial inside material differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation lengthSmall radiusSmallPhysical
    deformation control nonnegative small deformationBound strainSmall.le hessianSmall.le
  have tailNonnegative : 0 ≤ ∑' index : ℕ, changed.circulation (index + 2) :=
    tsum_nonneg fun index => (changed.circulation_pos frequencyPositive ratioPositive _).le
  have outerBudgetNonnegative : 0 ≤ changed.outerDisplacementBound := by
    dsimp only [Scales.outerDisplacementBound]
    positivity
  refine ⟨phaseLift, lift, ?_, ?_⟩
  · intro terminal terminalPositive terminalBound time timeInside index
    have terminalNonnegative := terminalPositive.le
    have omegaIndexPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
    have actual := shape index terminal ⟨terminalNonnegative, terminalBound⟩ time timeInside
    constructor
    · apply actual.1.trans
      apply mul_le_mul_of_nonneg_right shapeConstantBound
      positivity
    · apply actual.2.trans
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right shapeConstantBound terminalNonnegative
      · positivity
  · intro time member index outerIndex
    exact (outer time member index outerIndex).trans
      (mul_le_mul_of_nonneg_right outerConstantBound outerBudgetNonnegative)

end EulerNonuniqueness.Paper

