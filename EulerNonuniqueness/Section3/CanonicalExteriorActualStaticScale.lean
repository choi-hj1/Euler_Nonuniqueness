import EulerNonuniqueness.Section3.CanonicalExteriorStaticScaleModel
import EulerNonuniqueness.Section3.DiskTrueAngularPhysicalPairBounds
import EulerNonuniqueness.Section3.CanonicalExteriorCommonShiftRelative
import EulerNonuniqueness.Section3.CanonicalExteriorHigherPrimitiveRelative

noncomputable section

open Metric MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

theorem canonicalExteriorStaticRelativeBudget_exists_actual_scale_ball :
    ∃ rawRadius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (first final : PeriodicC1HolderHalf), first ∈ ball 0 rawRadius → final ∈ ball 0 rawRadius →
      diskSpectralTubularArea first = Real.pi → diskSpectralTubularArea final = Real.pi →
      ∀ {frequency time distance weight radius : ℝ}, frequency ≠ 0 → 0 < distance → 0 ≤ weight →
      0 ≤ radius → radius ≤ 1 →
      ‖diskPhysicalTransverseProjection first‖ ≤ radius → ‖diskPhysicalTransverseProjection final‖ ≤ radius →
      192 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight →
      let firstBase := diskRelabelCurve (diskNeutralCLM first) 1
      let finalBase := diskRelabelCurve (diskNeutralCLM final) 1
      let firstData := diskPhysicalSpectralChart first
      let finalData := diskPhysicalSpectralChart final
      let firstShift := firstData - family.canonicalExteriorAffineCoordinate index (diskNeutralCLM first) frequency time firstData
      let finalShift := finalData - family.canonicalExteriorAffineCoordinate index (diskNeutralCLM final) frequency time finalData
      canonicalExteriorStaticRelativeBudget frequency
        (family.canonicalExteriorStaticCoefficient index time) (family.canonicalExteriorStaticCoefficient index time)
        firstBase finalBase (firstData - firstBase) (finalData - finalBase) firstShift finalShift
        (family.relabeledExteriorHigherForcingPrimitive index (diskNeutralCLM first) frequency time)
        (family.relabeledExteriorHigherForcingPrimitive index (diskNeutralCLM final) frequency time)
        (family.exteriorStrainModulatedCoefficient index frequency time)
        (family.exteriorStrainModulatedCoefficient index frequency time) ≤
        EulerNonuniqueness.General.exteriorStaticResidualScaleModel |frequency| constant (weight / |frequency|)
          radius ((family.patch index).radius / distance)
          ‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖
          ‖diskNeutralCLM first - diskNeutralCLM final‖ := by
  obtain ⟨geometryRadius, geometryPositive, geometryConstant, geometryOne, geometry⟩ :=
    diskPhysicalSpectralChart_exists_true_angular_pair_bounds
  obtain ⟨absoluteRadius, absolutePositive, absoluteConstant, absoluteOne, absolute⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_near_identity_bound
  obtain ⟨relativeRadius, relativePositive, relativeConstant, relativeOne, relative⟩ :=
    canonicalExteriorAffineCoordinate_exists_common_shift_relative
  obtain ⟨primitiveRadius, primitivePositive, primitiveConstant, primitiveOne, primitive⟩ :=
    relabeledExteriorHigherForcingPrimitive_exists_relative_ball
  have geometryNonnegative : 0 ≤ geometryConstant := by linarith
  have absoluteNonnegative : 0 ≤ absoluteConstant := by linarith
  have relativeNonnegative : 0 ≤ relativeConstant := by linarith
  have primitiveNonnegative : 0 ≤ primitiveConstant := by linarith
  let angularRadius := min absoluteRadius (min relativeRadius (min primitiveRadius (1 / 4)))
  let rawRadius := min geometryRadius (angularRadius / (1 + ‖diskNeutralCLM‖))
  let components : Fin 9 → ℝ := ![geometryConstant, 2 * geometryConstant,
    absoluteConstant * (1 + geometryConstant), relativeConstant * (2 * geometryConstant + 1),
    256 / Real.pi, primitiveConstant, 96 / Real.pi, 2 * (96 : ℝ) ^ 2 / Real.pi, 1 / (2 * Real.pi)]
  let constant := 1 + ∑ component, components component
  have componentsNonnegative (component : Fin 9) : 0 ≤ components component := by
    fin_cases component <;> simp [components] <;> positivity
  have sumNonnegative : 0 ≤ ∑ component, components component := Finset.sum_nonneg (fun component _ => componentsNonnegative component)
  have componentLe (component : Fin 9) : components component ≤ constant := by
    have single := Finset.single_le_sum (fun other _ => componentsNonnegative other) (Finset.mem_univ component)
    dsimp only [constant]
    linarith
  have geometryLe : geometryConstant ≤ constant := by simpa [components] using componentLe 0
  have fiberLe : 2 * geometryConstant ≤ constant := by simpa [components] using componentLe 1
  have absoluteLe : absoluteConstant * (1 + geometryConstant) ≤ constant := by simpa [components] using componentLe 2
  have relativeLe : relativeConstant * (2 * geometryConstant + 1) ≤ constant := by simpa [components] using componentLe 3
  have primitiveAbsoluteLe : 256 / Real.pi ≤ constant := by simpa [components] using componentLe 4
  have primitiveRelativeLe : primitiveConstant ≤ constant := by simpa [components] using componentLe 5
  have fullLe : 96 / Real.pi ≤ constant := by simpa [components] using componentLe 6
  have tailLe : 2 * (96 : ℝ) ^ 2 / Real.pi ≤ constant := by simpa [components] using componentLe 7
  have strainLe : 1 / (2 * Real.pi) ≤ constant := by simpa [components] using componentLe 8
  have constantOne : 1 ≤ constant := by dsimp only [constant]; linarith
  refine ⟨rawRadius, by dsimp only [rawRadius, angularRadius]; positivity, constant, constantOne, ?_⟩
  intro count family index first final firstInside finalInside firstArea finalArea frequency time distance weight radius
    nonzero positive weightNonnegative radiusNonnegative radiusSmall firstTransverse finalTransverse small separated weightBound
  dsimp only
  have angularWithin {state : PeriodicC1HolderHalf} (inside : state ∈ ball 0 rawRadius) :
      ‖diskNeutralCLM state‖ ≤ angularRadius := by
    have stateSmall : ‖state‖ ≤ rawRadius := (by simpa only [mem_ball, dist_zero_right] using inside : ‖state‖ < rawRadius).le
    have scaled := (le_div_iff₀ (by positivity : 0 < 1 + ‖diskNeutralCLM‖)).mp (stateSmall.trans (min_le_right _ _))
    nlinarith [diskNeutralCLM.le_opNorm state, norm_nonneg state]
  have firstAngular := angularWithin firstInside
  have finalAngular := angularWithin finalInside
  have angularAbsolute : angularRadius ≤ absoluteRadius := min_le_left _ _
  have angularRelative : angularRadius ≤ relativeRadius := (min_le_right _ _).trans (min_le_left _ _)
  have angularPrimitive : angularRadius ≤ primitiveRadius := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have angularQuarter : angularRadius ≤ 1 / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have firstHalf : ‖diskNeutralCLM first‖ < 1 / 2 := (firstAngular.trans angularQuarter).trans_lt (by norm_num)
  have finalHalf : ‖diskNeutralCLM final‖ < 1 / 2 := (finalAngular.trans angularQuarter).trans_lt (by norm_num)
  have geometryPair := geometry first final (ball_subset_ball (min_le_left _ _) firstInside)
    (ball_subset_ball (min_le_left _ _) finalInside) firstArea finalArea
  dsimp only at geometryPair
  let transverse := ‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖
  let angular := ‖diskNeutralCLM first - diskNeutralCLM final‖
  let epsilon := weight / |frequency|
  let ratio := (family.patch index).radius / distance
  have epsilonNonnegative : 0 ≤ epsilon := by positivity
  have ratioNonnegative : 0 ≤ ratio := div_nonneg (family.patch index).radius_positive.le positive.le
  have transverseNonnegative : 0 ≤ transverse := norm_nonneg _
  have angularNonnegative : 0 ≤ angular := norm_nonneg _
  have frequencyPositive : 0 < |frequency| := abs_pos.mpr nonzero
  have normalization : |frequency| * epsilon = weight := mul_div_cancel₀ weight frequencyPositive.ne'
  have smallFour : 4 * (family.patch index).radius ≤ distance := by linarith [(family.patch index).radius_positive]
  have smallFortyEight : 48 * (family.patch index).radius ≤ distance := by linarith [(family.patch index).radius_positive]
  have firstIncrementGeometry := geometryPair.1.trans (mul_le_mul_of_nonneg_left firstTransverse geometryNonnegative)
  have finalIncrementGeometry := geometryPair.2.1.trans (mul_le_mul_of_nonneg_left finalTransverse geometryNonnegative)
  have firstIncrementBound := firstIncrementGeometry.trans (mul_le_mul_of_nonneg_right geometryLe radiusNonnegative)
  have finalIncrementBound := finalIncrementGeometry.trans (mul_le_mul_of_nonneg_right geometryLe radiusNonnegative)
  have incrementDifference :
      ‖(diskPhysicalSpectralChart first - diskRelabelCurve (diskNeutralCLM first) 1) -
        (diskPhysicalSpectralChart final - diskRelabelCurve (diskNeutralCLM final) 1)‖ ≤
        constant * (transverse + radius * angular) := by
    have simplified := geometryPair.2.2.1.trans (mul_le_mul_of_nonneg_left
      (add_le_add_left (mul_le_mul_of_nonneg_right (add_le_add firstTransverse finalTransverse) angularNonnegative) transverse)
      geometryNonnegative)
    have scalar : geometryConstant * (transverse + (radius + radius) * angular) ≤
        (2 * geometryConstant) * (transverse + radius * angular) := by nlinarith
    exact (simplified.trans scalar).trans (mul_le_mul_of_nonneg_right fiberLe (by positivity))
  have baseDifference := geometryPair.2.2.2.1.trans (mul_le_mul_of_nonneg_right geometryLe angularNonnegative)
  have dataGeometry := geometryPair.2.2.2.2
  have dataDifference := dataGeometry.trans (mul_le_mul_of_nonneg_right geometryLe (by positivity : 0 ≤ transverse + angular))
  have shiftBound {state : PeriodicC1HolderHalf} (inside : ‖diskNeutralCLM state‖ ≤ angularRadius)
      (incrementBound : ‖diskPhysicalSpectralChart state - diskRelabelCurve (diskNeutralCLM state) 1‖ ≤ geometryConstant * radius) :
      ‖diskPhysicalSpectralChart state - family.canonicalExteriorAffineCoordinate index (diskNeutralCLM state)
        frequency time (diskPhysicalSpectralChart state)‖ ≤ constant * epsilon := by
    have actual := absolute family index (diskNeutralCLM state) (inside.trans angularAbsolute) (diskNeutralCLM_real state)
      nonzero positive weightNonnegative smallFour separated weightBound (diskPhysicalSpectralChart state)
    rw [norm_sub_rev] at actual
    have bounded := actual.trans (mul_le_mul_of_nonneg_left (add_le_add_left
      (incrementBound.trans (mul_le_mul_of_nonneg_left radiusSmall geometryNonnegative)) 1) (by positivity))
    exact (bounded.trans_eq (by ring)).trans (mul_le_mul_of_nonneg_right absoluteLe epsilonNonnegative)
  have firstShiftBound := shiftBound firstAngular firstIncrementGeometry
  have finalShiftBound := shiftBound finalAngular finalIncrementGeometry
  have shiftDifference := relative family index (diskNeutralCLM first) (diskNeutralCLM final)
    (firstAngular.trans angularRelative) (finalAngular.trans angularRelative) (diskNeutralCLM_real first) (diskNeutralCLM_real final)
    nonzero positive weightNonnegative smallFortyEight separated weightBound (diskPhysicalSpectralChart first) (diskPhysicalSpectralChart final)
  have shiftDifferenceBound :
      ‖(diskPhysicalSpectralChart first - family.canonicalExteriorAffineCoordinate index (diskNeutralCLM first) frequency time (diskPhysicalSpectralChart first)) -
        (diskPhysicalSpectralChart final - family.canonicalExteriorAffineCoordinate index (diskNeutralCLM final) frequency time (diskPhysicalSpectralChart final))‖ ≤
        constant * epsilon * (transverse + angular) := by
    have dataCap : ‖diskPhysicalSpectralChart first - diskPhysicalSpectralChart final‖ +
        (1 + ‖diskPhysicalSpectralChart final - diskRelabelCurve (diskNeutralCLM final) 1‖) * angular ≤
        (2 * geometryConstant + 1) * (transverse + angular) := by
      have incrementCap := finalIncrementGeometry.trans (mul_le_mul_of_nonneg_left radiusSmall geometryNonnegative)
      have bounded := add_le_add dataGeometry (mul_le_mul_of_nonneg_right (add_le_add_left incrementCap 1) angularNonnegative)
      have leftover : 0 ≤ (geometryConstant + 1) * transverse := by positivity
      nlinarith only [bounded, leftover]
    have actual := shiftDifference.trans (mul_le_mul_of_nonneg_left dataCap (by positivity))
    have scalar := mul_le_mul_of_nonneg_right relativeLe
      (mul_nonneg epsilonNonnegative (add_nonneg transverseNonnegative angularNonnegative))
    exact (actual.trans_eq (by change relativeConstant * epsilon * ((2 * geometryConstant + 1) * (transverse + angular)) =
      (relativeConstant * (2 * geometryConstant + 1)) * (epsilon * (transverse + angular)); ring)).trans
        (scalar.trans_eq (by ring))
  have primitiveDifference := primitive family index (diskNeutralCLM first) (diskNeutralCLM final)
    (firstAngular.trans angularPrimitive) (finalAngular.trans angularPrimitive) (diskNeutralCLM_real first) (diskNeutralCLM_real final)
    nonzero positive weightNonnegative small separated weightBound
  have primitiveDifferenceBound :
      ‖family.relabeledExteriorHigherForcingPrimitive index (diskNeutralCLM first) frequency time -
        family.relabeledExteriorHigherForcingPrimitive index (diskNeutralCLM final) frequency time‖ ≤
        constant * epsilon * ratio * angular := primitiveDifference.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right primitiveRelativeLe epsilonNonnegative) ratioNonnegative) angularNonnegative)
  have primitiveFinal := family.relabeledExteriorHigherForcingPrimitive_norm_bound index (diskNeutralCLM final) finalHalf
    (diskNeutralCLM_real final) nonzero positive weightNonnegative smallFour separated weightBound
  have primitiveFinalBound : ‖family.relabeledExteriorHigherForcingPrimitive index (diskNeutralCLM final) frequency time‖ ≤
      constant * epsilon * ratio := by
    have scalar := mul_le_mul_of_nonneg_right primitiveAbsoluteLe (mul_nonneg epsilonNonnegative ratioNonnegative)
    exact (primitiveFinal.trans_eq (by dsimp only [epsilon, ratio]; ring)).trans (scalar.trans_eq (by ring))
  have full := family.canonicalExteriorStaticCoefficient_weight96_le index time distance weight positive weightNonnegative small separated weightBound
  have fullBound : (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖family.canonicalExteriorStaticCoefficient index time degree‖) ≤
      constant * |frequency| * epsilon := by
    have scalar := mul_le_mul_of_nonneg_right fullLe weightNonnegative
    calc
      _ ≤ 96 * weight / Real.pi := full
      _ = (96 / Real.pi) * weight := by ring
      _ ≤ constant * weight := scalar
      _ = constant * |frequency| * epsilon := by rw [mul_assoc, normalization]
  have tail := family.canonicalExteriorStaticCoefficient_higher_weight96_le index time distance weight positive weightNonnegative small separated weightBound
  have tailBound : (∑' degree, (96 : ℝ) ^ (degree + 1) *
      ‖exteriorCoefficientWithoutLeading (family.canonicalExteriorStaticCoefficient index time) degree‖) ≤
      constant * |frequency| * epsilon * ratio := by
    have scalar := mul_le_mul_of_nonneg_right tailLe (mul_nonneg weightNonnegative ratioNonnegative)
    exact (tail.trans_eq (by dsimp only [ratio]; ring)).trans (scalar.trans_eq (by rw [mul_assoc constant, normalization]; ring))
  have strain : ‖family.exteriorStrainModulatedCoefficient index frequency time‖ ≤ weight / (2 * Real.pi) := by
    rw [exteriorStrainModulatedCoefficient, norm_mul, diskForcingPhase_norm, one_mul]
    exact family.exteriorTaylorCoefficient_one_norm_le index time distance weight positive separated weightBound
  have strainBound : ‖family.exteriorStrainModulatedCoefficient index frequency time‖ ≤ constant * |frequency| * epsilon := by
    have scalar := mul_le_mul_of_nonneg_right strainLe weightNonnegative
    calc
      _ ≤ weight / (2 * Real.pi) := strain
      _ = (1 / (2 * Real.pi)) * weight := by ring
      _ ≤ constant * weight := scalar
      _ = constant * |frequency| * epsilon := by rw [mul_assoc, normalization]
  apply canonicalExteriorStaticRelativeBudget_same_le_scale_model frequency
    (family.canonicalExteriorStaticCoefficient index time)
    (diskRelabelCurve (diskNeutralCLM first) 1) (diskRelabelCurve (diskNeutralCLM final) 1)
    (diskPhysicalSpectralChart first - diskRelabelCurve (diskNeutralCLM first) 1)
    (diskPhysicalSpectralChart final - diskRelabelCurve (diskNeutralCLM final) 1)
    _ _ _ _ (family.exteriorStrainModulatedCoefficient index frequency time)
    (by linarith) epsilonNonnegative radiusNonnegative ratioNonnegative transverseNonnegative angularNonnegative
    fullBound tailBound strainBound (by linarith) firstIncrementBound finalIncrementBound incrementDifference baseDifference
    (by simpa only [add_sub_cancel] using dataDifference) (by linarith) shiftDifferenceBound finalShiftBound
    primitiveDifferenceBound primitiveFinalBound

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
