import EulerNonuniqueness.Section3.CanonicalExteriorWeight96Bound
import EulerNonuniqueness.Section3.RelabeledPrimitiveSeriesDifference
import EulerNonuniqueness.Section3.RelabelMapUniformLipschitz

noncomputable section

open Filter Metric MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup
  forcingModeC1ComplexModule forcingModeC1ComplexSpace exteriorPowerSeriesOperatorSpace

open EulerNonuniqueness.Section6

theorem relabeledExteriorHigherForcingPrimitive_exists_relative_ball :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (firstAngular finalAngular : PeriodicC1HolderHalf), ‖firstAngular‖ ≤ radius → ‖finalAngular‖ ≤ radius →
      (∀ label, star (firstAngular.val.1 label) = firstAngular.val.1 label) →
      (∀ label, star (finalAngular.val.1 label) = finalAngular.val.1 label) →
      ∀ {frequency time distance weight : ℝ}, frequency ≠ 0 → 0 < distance → 0 ≤ weight →
      192 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight →
      ‖family.relabeledExteriorHigherForcingPrimitive index firstAngular frequency time -
        family.relabeledExteriorHigherForcingPrimitive index finalAngular frequency time‖ ≤
        constant * (weight / |frequency|) * ((family.patch index).radius / distance) * ‖firstAngular - finalAngular‖ := by
  obtain ⟨baseRadius, basePositive, baseConstant, _, baseRelative⟩ := diskRelabelMap_exists_uniform_lipschitz
  have normSmall : ∀ᶠ angular in 𝓝 (0 : PeriodicC1HolderHalf), ‖diskRelabelCurve angular 1‖ < 3 := by
    have circle : diskRelabelCurve (0 : PeriodicC1HolderHalf) 1 = standardCircleBanach := by
      apply PeriodicC1HolderHalf.ext_value
      intro label
      rw [diskRelabelCurve_value]
      change Complex.exp ((1 : ℂ) * (Complex.I * 0)) * standardCircle label = standardCircle label
      simp
    exact (diskRelabelMap_analyticAt 0).continuousAt.norm.eventually (gt_mem_nhds (by
      change ‖diskRelabelCurve (0 : PeriodicC1HolderHalf) 1‖ < 3
      rw [circle]
      linarith [standardCircleBanach_norm_bound]))
  obtain ⟨normRadius, normPositive, norms⟩ := Metric.eventually_nhds_iff.mp normSmall
  let radius := min baseRadius (min (1 / 4) (normRadius / 2))
  let constant := 4 * (96 : ℝ) ^ 2 * (baseConstant : ℝ) / Real.pi + 1
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ 4 * (96 : ℝ) ^ 2 * (baseConstant : ℝ) / Real.pi := by positivity
    dsimp only [constant]
    linarith
  refine ⟨radius, by dsimp only [radius]; positivity, constant, constantOne, ?_⟩
  intro count family index firstAngular finalAngular firstInside finalInside firstReal finalReal
    frequency time distance weight nonzero positive weightNonnegative small separated weightBound
  have receiverNonnegative := (family.patch index).radius_positive.le
  have half {angular : PeriodicC1HolderHalf} (inside : ‖angular‖ ≤ radius) : ‖angular‖ < 1 / 2 :=
    (inside.trans ((min_le_right _ _).trans (min_le_left _ _))).trans_lt (by norm_num)
  have bounded {angular : PeriodicC1HolderHalf} (inside : ‖angular‖ ≤ radius) : ‖diskRelabelCurve angular 1‖ ≤ 3 := by
    apply (norms ?_).le
    rw [dist_zero_right]
    exact (inside.trans ((min_le_right _ _).trans (min_le_right _ _))).trans_lt (by linarith)
  let amplitude := fun degree current => exteriorCoefficientWithoutLeading
    (family.canonicalExteriorStaticCoefficient index current) degree
  have weighted96 := exteriorCoefficientWithoutLeading_weight_summable
    (family.canonicalExteriorStaticCoefficient index time) (by norm_num : (0 : ℝ) ≤ 96)
    (family.canonicalExteriorStaticCoefficient_summable_weight96 index time distance positive small separated)
  have weighted24 := summable_exteriorCoefficientWeight_mono (amplitude · time)
    (by norm_num : (0 : ℝ) ≤ 24) (by norm_num : (24 : ℝ) ≤ 96) weighted96
  have sumMonotone : (∑' degree, (24 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖) ≤
      ∑' degree, (96 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖ :=
    Summable.tsum_le_tsum (fun degree => mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 24) (by norm_num : (24 : ℝ) ≤ 96) _) (norm_nonneg _))
      weighted24 weighted96
  have sumBound := sumMonotone.trans
    (family.canonicalExteriorStaticCoefficient_higher_weight96_le index time distance weight positive
      weightNonnegative small separated weightBound)
  have actual := relabeledForcingPrimitiveSeries_difference_bound firstAngular finalAngular
    (half firstInside) (half finalInside) firstReal finalReal (bounded firstInside) (bounded finalInside)
    nonzero amplitude time weighted24
  have basePair := baseRelative firstAngular finalAngular
    (firstInside.trans (min_le_left _ _)) (finalInside.trans (min_le_left _ _))
  have boundedPair := actual.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left sumBound (by positivity : 0 ≤ 2 / |frequency|)) basePair
    (norm_nonneg _) (by positivity))
  have coefficientLe : 4 * (96 : ℝ) ^ 2 * (baseConstant : ℝ) / Real.pi ≤ constant := by
    dsimp only [constant]
    linarith
  have scalar := mul_le_mul_of_nonneg_right coefficientLe (by positivity : 0 ≤
    (weight / |frequency|) * ((family.patch index).radius / distance) * ‖firstAngular - finalAngular‖)
  have finalBound := (boundedPair.trans_eq (by ring)).trans scalar
  have coefficientIdentity (current : ℝ) : family.canonicalExteriorStaticCoefficient index current =
      (fun degree => family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
        (family.patch index).radius (degree + 1) current) := by
    funext degree
    rfl
  simp only [amplitude, coefficientIdentity] at finalBound
  with_reducible_and_instances
    simpa only [relabeledExteriorHigherForcingPrimitive, mul_assoc] using finalBound

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
