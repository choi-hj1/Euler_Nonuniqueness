import EulerNonuniqueness.Section3.CanonicalExteriorAngularJetWeightBound
import EulerNonuniqueness.Section3.CanonicalExteriorTrueAngularDriftRelative
import EulerNonuniqueness.Section3.CanonicalExteriorTrueAngularDriftBound
import EulerNonuniqueness.Section3.DiskTrueAngularPhysicalPairBounds
import EulerNonuniqueness.Section3.DiskPhysicalSpectralFirstOrderBounds
import EulerNonuniqueness.General.ExteriorMovingAngularScale

noncomputable section

open Filter Metric MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

def canonicalExteriorCommonMovingAngularTerm {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (frequency time distance : ℝ) (positive : 0 < distance)
    (small : 8 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖) (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  family.canonicalExteriorAffineAngularDerivative index (diskNeutralCLM (diskPhysicalSpectralCoordinate data))
    frequency time data (diskNeutralCLM (diskPhysicalSpectralInverseDerivative data
      (frequency • diskEulerRotatingField data + family.canonicalProjectedExteriorContourField index time distance
        positive small separated (Circle.exp (frequency * time / 2)) data)))

theorem canonicalExteriorCommonMovingAngularTerm_exists_actual_quadratic_rate_ball :
    ∃ rawRadius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (first final : PeriodicC1HolderHalf), first ∈ ball 0 rawRadius → final ∈ ball 0 rawRadius →
      diskSpectralTubularArea first = Real.pi → diskSpectralTubularArea final = Real.pi →
      ∀ {frequency time distance weight radius : ℝ}, frequency ≠ 0 →
      ∀ (positive : 0 < distance) (weightNonnegative : 0 ≤ weight),
      0 ≤ radius → radius ≤ 1 →
      ‖diskPhysicalTransverseProjection first‖ ≤ radius → ‖diskPhysicalTransverseProjection final‖ ≤ radius →
      ∀ (small : 192 * (family.patch index).radius ≤ distance)
        (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
          distance ≤ ‖(family.patch index).center time - position‖),
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight →
      weight / |frequency| ≤ radius → (weight / |frequency|) ^ 2 ≤ radius ^ 3 →
      ‖family.canonicalExteriorCommonMovingAngularTerm index frequency time distance positive
          (by linarith [(family.patch index).radius_positive]) separated (diskPhysicalSpectralChart first) -
        family.canonicalExteriorCommonMovingAngularTerm index frequency time distance positive
          (by linarith [(family.patch index).radius_positive]) separated (diskPhysicalSpectralChart final)‖ ≤
        constant * |frequency| * radius ^ 2 *
          (‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖ +
            radius * ‖diskNeutralCLM first - diskNeutralCLM final‖) := by
  obtain ⟨absoluteRadius, absolutePositive, absoluteConstant, absoluteOne, absolute⟩ :=
    canonicalExteriorAffineAngularDerivative_exists_weight_bound_ball
  obtain ⟨relativeRadius, relativePositive, relativeConstant, relativeOne, relative⟩ :=
    canonicalExteriorAffineAngularDerivative_exists_relative_weight_bound_ball
  obtain ⟨driftRadius, driftPositive, driftConstant, driftOne, drifts⟩ :=
    canonicalProjectedExteriorContourField_exists_true_angular_drift_relative_ball
  obtain ⟨speedRadius, speedPositive, speedConstant, speedOne, speeds⟩ :=
    canonicalProjectedExteriorContourField_exists_true_angular_drift_bound_ball
  obtain ⟨geometryRadius, geometryPositive, geometryConstant, geometryOne, geometry⟩ :=
    diskPhysicalSpectralChart_exists_true_angular_pair_bounds
  obtain ⟨chartRadius, chartPositive, chartConstant, chartOne, charts, _⟩ :=
    diskPhysicalSpectralChart_exists_uniform_firstOrder_bounds
  obtain ⟨inverseRadius, inversePositive, inverses⟩ := Metric.eventually_nhds_iff.mp
    diskPhysicalSpectralCoordinate_eventually_left_inverse
  have absoluteNonnegative : 0 ≤ absoluteConstant := by linarith
  have relativeNonnegative : 0 ≤ relativeConstant := by linarith
  have driftNonnegative : 0 ≤ driftConstant := by linarith
  have speedNonnegative : 0 ≤ speedConstant := by linarith
  have geometryNonnegative : 0 ≤ geometryConstant := by linarith
  have chartConstantPositive : 0 < chartConstant := by linarith
  let angularRadius := min absoluteRadius relativeRadius
  let physicalRadius := min driftRadius speedRadius
  let rawRadius := min geometryRadius (min chartRadius (min inverseRadius
    (min (angularRadius / (1 + ‖diskNeutralCLM‖)) (physicalRadius / (2 * chartConstant)))))
  let components : Fin 5 → ℝ := ![absoluteConstant * (1 + geometryConstant),
    relativeConstant * (2 * geometryConstant + 1), 4 * driftConstant, driftConstant * geometryConstant, speedConstant]
  let constant := 1 + ∑ component, components component
  have componentsNonnegative (component : Fin 5) : 0 ≤ components component := by
    fin_cases component <;> simp [components] <;> positivity
  have sumNonnegative : 0 ≤ ∑ component, components component := Finset.sum_nonneg (fun component _ => componentsNonnegative component)
  have componentLe (component : Fin 5) : components component ≤ constant := by
    have single := Finset.single_le_sum (fun other _ => componentsNonnegative other) (Finset.mem_univ component)
    dsimp only [constant]
    linarith
  have absoluteLe : absoluteConstant * (1 + geometryConstant) ≤ constant := by simpa [components] using componentLe 0
  have relativeLe : relativeConstant * (2 * geometryConstant + 1) ≤ constant := by simpa [components] using componentLe 1
  have selfLe : 4 * driftConstant ≤ constant := by simpa [components] using componentLe 2
  have sourceLe : driftConstant * geometryConstant ≤ constant := by simpa [components] using componentLe 3
  have speedLe : speedConstant ≤ constant := by simpa [components] using componentLe 4
  have constantOne : 1 ≤ constant := by dsimp only [constant]; linarith
  have constantNonnegative : 0 ≤ constant := by linarith
  refine ⟨rawRadius, by dsimp only [rawRadius, angularRadius, physicalRadius]; positivity,
    4 * constant ^ 2 + 1, by nlinarith [sq_nonneg constant], ?_⟩
  intro count family index first final firstInside finalInside firstArea finalArea frequency time distance weight radius
    nonzero positive weightNonnegative radiusNonnegative radiusSmall firstTransverse finalTransverse small separated weightBound
    epsilonSmall squaredSmall
  have within {state : PeriodicC1HolderHalf} (inside : state ∈ ball 0 rawRadius) :
      state ∈ ball 0 geometryRadius ∧ diskPhysicalSpectralCoordinate (diskPhysicalSpectralChart state) = state ∧
      ‖diskNeutralCLM state‖ ≤ angularRadius ∧
      ‖diskPhysicalSpectralChart state - standardCircleBanach‖ ≤ driftRadius ∧
      ‖diskPhysicalSpectralChart state - standardCircleBanach‖ < speedRadius := by
    have stateSmall : ‖state‖ ≤ rawRadius := (by simpa only [mem_ball, dist_zero_right] using inside : ‖state‖ < rawRadius).le
    have chartSmall := stateSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
    have chartBound := (charts state chartSmall).1
    have angularScaled := (le_div_iff₀ (by positivity : 0 < 1 + ‖diskNeutralCLM‖)).mp
      (stateSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
    have physicalScaled := (le_div_iff₀ (by positivity : 0 < 2 * chartConstant)).mp
      (stateSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
    have physicalHalf : ‖diskPhysicalSpectralChart state - standardCircleBanach‖ ≤ physicalRadius / 2 := by nlinarith
    refine ⟨ball_subset_ball (min_le_left _ _) inside, inverses ?_, ?_,
      physicalHalf.trans ((div_le_self (by dsimp only [physicalRadius]; positivity) (by norm_num : (1 : ℝ) ≤ 2)).trans (min_le_left _ _)),
      physicalHalf.trans_lt ?_⟩
    · simpa only [mem_ball, dist_zero_right] using
        (ball_subset_ball ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) inside : state ∈ ball 0 inverseRadius)
    · nlinarith [diskNeutralCLM.le_opNorm state, norm_nonneg state]
    · have physicalPositive : 0 < physicalRadius := by dsimp only [physicalRadius]; positivity
      exact (half_lt_self physicalPositive).trans_le (min_le_right _ _)
  have firstWithin := within firstInside
  have finalWithin := within finalInside
  have pair := geometry first final firstWithin.1 finalWithin.1 firstArea finalArea
  dsimp only at pair
  let transverse := ‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖
  let angular := ‖diskNeutralCLM first - diskNeutralCLM final‖
  let epsilon := weight / |frequency|
  have transverseNonnegative : 0 ≤ transverse := norm_nonneg _
  have angularNonnegative : 0 ≤ angular := norm_nonneg _
  have epsilonNonnegative : 0 ≤ epsilon := by positivity
  have normalization : |frequency| * epsilon = weight := mul_div_cancel₀ weight (abs_pos.mpr nonzero).ne'
  let firstJet := family.canonicalExteriorAffineAngularDerivative index (diskNeutralCLM first) frequency time (diskPhysicalSpectralChart first)
  let finalJet := family.canonicalExteriorAffineAngularDerivative index (diskNeutralCLM final) frequency time (diskPhysicalSpectralChart final)
  let force := family.canonicalProjectedExteriorContourField index time distance positive
    (by linarith [(family.patch index).radius_positive]) separated (Circle.exp (frequency * time / 2))
  let drift := fun data => diskNeutralCLM (diskPhysicalSpectralInverseDerivative data (frequency • diskEulerRotatingField data + force data))
  have firstIncrement := pair.1.trans (mul_le_mul_of_nonneg_left firstTransverse geometryNonnegative)
  have finalIncrement := pair.2.1.trans (mul_le_mul_of_nonneg_left finalTransverse geometryNonnegative)
  have firstJetBound : ‖firstJet‖ ≤ constant * epsilon := by
    have actual := absolute family index (diskNeutralCLM first) (diskPhysicalSpectralChart first)
      (firstWithin.2.2.1.trans (min_le_left _ _)) nonzero positive weightNonnegative small separated weightBound
    have bounded := actual.trans (mul_le_mul_of_nonneg_left (add_le_add_left
      (firstIncrement.trans (mul_le_mul_of_nonneg_left radiusSmall geometryNonnegative)) 1) (by positivity))
    exact (bounded.trans_eq (by ring)).trans (mul_le_mul_of_nonneg_right absoluteLe epsilonNonnegative)
  have jetPair : ‖firstJet - finalJet‖ ≤ constant * epsilon * (transverse + angular) := by
    have actual := relative family index (diskNeutralCLM first) (diskNeutralCLM final) (diskPhysicalSpectralChart first) (diskPhysicalSpectralChart final)
      (firstWithin.2.2.1.trans (min_le_right _ _)) (finalWithin.2.2.1.trans (min_le_right _ _))
      nonzero positive weightNonnegative small separated weightBound
    have incrementCap := finalIncrement.trans (mul_le_mul_of_nonneg_left radiusSmall geometryNonnegative)
    have geometric : ‖diskPhysicalSpectralChart first - diskPhysicalSpectralChart final‖ +
        (1 + ‖diskPhysicalSpectralChart final - diskRelabelCurve (diskNeutralCLM final) 1‖) * angular ≤
        (2 * geometryConstant + 1) * (transverse + angular) := by
      have bounded := add_le_add pair.2.2.2.2 (mul_le_mul_of_nonneg_right (add_le_add_left incrementCap 1) angularNonnegative)
      have leftover : 0 ≤ (geometryConstant + 1) * transverse := by positivity
      nlinarith only [bounded, leftover]
    have bounded := actual.trans (mul_le_mul_of_nonneg_left geometric (by positivity))
    have scalar := mul_le_mul_of_nonneg_right relativeLe (mul_nonneg epsilonNonnegative (add_nonneg transverseNonnegative angularNonnegative))
    exact (bounded.trans_eq (by change relativeConstant * epsilon * ((2 * geometryConstant + 1) * (transverse + angular)) =
      (relativeConstant * (2 * geometryConstant + 1)) * (epsilon * (transverse + angular)); ring)).trans (scalar.trans_eq (by ring))
  have firstPhysicalArea : contourAreaFunctional (diskPhysicalSpectralChart first) = Real.pi := firstArea
  have finalPhysicalArea : contourAreaFunctional (diskPhysicalSpectralChart final) = Real.pi := finalArea
  have driftPair : ‖drift (diskPhysicalSpectralChart first) - drift (diskPhysicalSpectralChart final)‖ ≤
      constant * |frequency| * (radius * transverse + radius ^ 2 * angular + epsilon * (transverse + angular)) := by
    have actual := drifts family index (diskPhysicalSpectralChart first) (diskPhysicalSpectralChart final)
      firstWithin.2.2.2.1 finalWithin.2.2.2.1 firstPhysicalArea finalPhysicalArea
      time distance weight frequency positive weightNonnegative small separated weightBound (Circle.exp (frequency * time / 2))
    dsimp only at actual
    rw [firstWithin.2.1, finalWithin.2.1] at actual
    have sumCap := add_le_add firstTransverse finalTransverse
    have squaredCap := pow_le_pow_left₀ (by positivity : 0 ≤ ‖diskPhysicalTransverseProjection first‖ + ‖diskPhysicalTransverseProjection final‖) sumCap 2
    have stateCap := pair.2.2.2.2
    have bounded := actual.trans (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_right sumCap transverseNonnegative)
        (mul_le_mul_of_nonneg_right squaredCap angularNonnegative)) (abs_nonneg frequency))
        (mul_le_mul_of_nonneg_left stateCap weightNonnegative)) driftNonnegative)
    have selfBound := mul_le_mul_of_nonneg_right selfLe (by positivity : 0 ≤ |frequency| * (radius * transverse + radius ^ 2 * angular))
    have sourceBound := mul_le_mul_of_nonneg_right sourceLe (by positivity : 0 ≤ weight * (transverse + angular))
    have leftover : 0 ≤ 2 * driftConstant * |frequency| * radius * transverse := by positivity
    have regrouped : driftConstant *
        (|frequency| * ((radius + radius) * transverse + (radius + radius) ^ 2 * angular) +
          weight * (geometryConstant * (transverse + angular))) ≤
        constant * |frequency| * (radius * transverse + radius ^ 2 * angular) + constant * weight * (transverse + angular) := by
      nlinarith only [selfBound, sourceBound, leftover]
    exact (bounded.trans regrouped).trans_eq (by rw [← normalization]; ring)
  have driftFinal : ‖drift (diskPhysicalSpectralChart final)‖ ≤ constant * |frequency| * (radius ^ 2 + epsilon * radius) := by
    have actual := speeds family index (diskPhysicalSpectralChart final) finalWithin.2.2.2.2 finalPhysicalArea
      time distance weight frequency positive weightNonnegative small separated weightBound (Circle.exp (frequency * time / 2))
    rw [finalWithin.2.1] at actual
    have bounded := actual.trans (mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) finalTransverse 2) (abs_nonneg frequency))
      (mul_le_mul_of_nonneg_left finalTransverse weightNonnegative)) speedNonnegative)
    have scalar := mul_le_mul_of_nonneg_right speedLe (by positivity : 0 ≤ |frequency| * radius ^ 2 + weight * radius)
    exact (bounded.trans scalar).trans_eq (by rw [← normalization]; ring)
  have applied := EulerNonuniqueness.General.norm_operator_apply_difference_le firstJet finalJet
    (drift (diskPhysicalSpectralChart first)) (drift (diskPhysicalSpectralChart final))
  have bounded := applied.trans (add_le_add
    (mul_le_mul firstJetBound driftPair (norm_nonneg _) (by positivity))
    (mul_le_mul jetPair driftFinal (norm_nonneg _) (by positivity)))
  have quadratic := EulerNonuniqueness.General.exteriorMovingAngularScale_le_quadratic_rate
    (abs_nonneg frequency) constantNonnegative epsilonNonnegative radiusNonnegative radiusSmall
    transverseNonnegative angularNonnegative epsilonSmall squaredSmall
  have scalar := mul_le_mul_of_nonneg_right (show 4 * constant ^ 2 ≤ 4 * constant ^ 2 + 1 by linarith)
    (by positivity : 0 ≤ |frequency| * radius ^ 2 * (transverse + radius * angular))
  have result := (bounded.trans quadratic).trans (by convert scalar using 1 <;> ring)
  with_reducible_and_instances
    simpa only [canonicalExteriorCommonMovingAngularTerm, firstWithin.2.1, finalWithin.2.1, firstJet, finalJet, drift, force,
      transverse, angular, mul_assoc] using result

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
