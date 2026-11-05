import EulerNonuniqueness.Section6.FourPointMomentControl

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Section6

def fourPointArithmeticCenter (positions : FourPointConfiguration) : ℂ :=
  (∑ target : Fin 4, positions target) / 4

theorem fourPointArithmeticCenter_sub (first second : FourPointConfiguration) :
    fourPointArithmeticCenter (first - second) = fourPointArithmeticCenter first - fourPointArithmeticCenter second := by
  simp [fourPointArithmeticCenter, Finset.sum_sub_distrib, sub_div]

theorem fourPointArithmeticCenter_norm_le (positions : FourPointConfiguration) :
    ‖fourPointArithmeticCenter positions‖ ≤ ‖positions‖ := by
  have sumBound : ‖∑ target : Fin 4, positions target‖ ≤ 4 * ‖positions‖ := by
    calc
      _ ≤ ∑ target : Fin 4, ‖positions target‖ := norm_sum_le _ _
      _ ≤ ∑ _target : Fin 4, ‖positions‖ := Finset.sum_le_sum (fun target _ => norm_le_pi_norm positions target)
      _ = _ := by simp
  dsimp only [fourPointArithmeticCenter]
  rw [norm_div, Complex.norm_ofNat]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr (by linarith)

theorem fourPointArithmeticCenter_central (positive negative : ℂ) :
    fourPointArithmeticCenter (centrallySymmetricFourPoint positive negative) = 0 := by
  simp [fourPointArithmeticCenter, centrallySymmetricFourPoint, Fin.sum_univ_succ]

theorem fourPointArithmeticCenter_central_field (coefficient : ℝ) {positive negative : ℂ}
    (noncollision : FourPointNoncollision (centrallySymmetricFourPoint positive negative)) :
    fourPointArithmeticCenter (fourPointField coefficient (centrallySymmetricFourPoint positive negative)) = 0 := by
  obtain ⟨positiveNonzero, negativeNonzero, differenceNonzero, sumNonzero⟩ :=
    centrallySymmetricFourPoint_noncollision_conditions noncollision
  rw [fourPointField_central_embedding coefficient positiveNonzero negativeNonzero differenceNonzero sumNonzero,
    fourPointArithmeticCenter_central]

theorem fourPointArithmeticCenter_field_bound {base : FourPointConfiguration}
    (noncollision : FourPointNoncollision base) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ,
      ∀ positive negative firstCenter secondCenter : ℂ,
      FourPointNoncollision (centrallySymmetricFourPoint positive negative) →
      ‖centrallySymmetricFourPoint positive negative - base‖ < radius →
      ‖firstCenter - secondCenter‖ < 2 * radius →
      ‖fourPointArithmeticCenter (fourPointField coefficient
          (centrallySymmetricFourPoint positive negative + fourPointPairCenterMode firstCenter secondCenter))‖ ≤
        bound * |coefficient| * ‖firstCenter - secondCenter‖ / 2 := by
  have smooth : ContDiffAt ℝ 1 (fourPointField 1) base :=
    (fourPointField_contDiffAt 1 noncollision).of_le (by norm_num)
  obtain ⟨bound, neighborhood, neighborhoodMem, lipschitz⟩ := smooth.exists_lipschitzOnWith
  obtain ⟨radius, radiusPositive, ballInside⟩ := Metric.mem_nhds_iff.mp neighborhoodMem
  refine ⟨bound, bound.coe_nonneg, radius / 4, by positivity, ?_⟩
  intro coefficient positive negative firstCenter secondCenter centerNoncollision centerSmall differenceSmall
  rw [fourPointField_pairCenter_translation]
  let center := centrallySymmetricFourPoint positive negative
  let increment := fourPointPairCenterMode ((firstCenter - secondCenter) / 2) (-((firstCenter - secondCenter) / 2))
  have incrementNorm : ‖increment‖ = ‖firstCenter - secondCenter‖ / 2 := by
    dsimp only [increment]
    rw [fourPointPairCenterMode_balanced_norm, norm_div, Complex.norm_ofNat]
  have incrementSmall : ‖increment‖ < radius / 4 := by rw [incrementNorm]; linarith
  have centerInside : center ∈ neighborhood := ballInside (by
    rw [Metric.mem_ball, dist_eq_norm]
    exact centerSmall.trans (by linarith))
  have shiftedInside : center + increment ∈ neighborhood := ballInside (by
    rw [Metric.mem_ball, dist_eq_norm]
    have triangle : ‖center + increment - base‖ ≤ ‖center - base‖ + ‖increment‖ := by
      simpa only [sub_add_eq_add_sub] using norm_add_le (center - base) increment
    linarith)
  have fieldControl := (lipschitzOnWith_iff_norm_sub_le.mp lipschitz) shiftedInside centerInside
  simp only [add_sub_cancel_left] at fieldControl
  have zeroCenter := fourPointArithmeticCenter_central_field coefficient centerNoncollision
  have projected := fourPointArithmeticCenter_norm_le
    (fourPointField coefficient (center + increment) - fourPointField coefficient center)
  rw [fourPointArithmeticCenter_sub, zeroCenter, sub_zero] at projected
  apply projected.trans
  have scaled : fourPointField coefficient (center + increment) - fourPointField coefficient center =
      coefficient • (fourPointField 1 (center + increment) - fourPointField 1 center) := by
    rw [fourPointField_scaling coefficient, fourPointField_scaling coefficient, smul_sub]
  rw [scaled, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ |coefficient| * ((bound : ℝ) * ‖increment‖) :=
      mul_le_mul_of_nonneg_left fieldControl (abs_nonneg coefficient)
    _ = _ := by rw [incrementNorm]; ring

theorem fourPointArithmeticCenter_field_signedMoment_bound {base : FourPointConfiguration}
    (noncollision : FourPointNoncollision base) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ,
      ∀ positions : FourPointConfiguration,
      FourPointNoncollision (centrallySymmetricFourPoint (fourPointOddPart positions).1
        (fourPointOddPart positions).2) →
      ‖centrallySymmetricFourPoint (fourPointOddPart positions).1 (fourPointOddPart positions).2 - base‖ < radius →
      ‖fourPointSignedMoment positions‖ < 4 * radius →
      ‖fourPointArithmeticCenter (fourPointField coefficient positions)‖ ≤
        bound * |coefficient| * ‖fourPointSignedMoment positions‖ / 4 := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    fourPointArithmeticCenter_field_bound noncollision
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro coefficient positions centeredNoncollision centeredSmall momentSmall
  have momentNorm : ‖fourPointSignedMoment positions‖ =
      2 * ‖(positions 0 + positions 1) / 2 - (positions 2 + positions 3) / 2‖ := by
    rw [fourPointSignedMoment_centerDifference, norm_mul, Complex.norm_ofNat]
  have differenceSmall : ‖(positions 0 + positions 1) / 2 - (positions 2 + positions 3) / 2‖ <
      2 * radius := by rw [momentNorm] at momentSmall; linarith
  have control := estimate coefficient (fourPointOddPart positions).1 (fourPointOddPart positions).2
    ((positions 0 + positions 1) / 2) ((positions 2 + positions 3) / 2)
    centeredNoncollision centeredSmall differenceSmall
  have decomposition : centrallySymmetricFourPoint (fourPointOddPart positions).1
      (fourPointOddPart positions).2 + fourPointPairCenterMode ((positions 0 + positions 1) / 2)
        ((positions 2 + positions 3) / 2) = positions :=
    (fourPoint_increment_decomposition positions).symm
  rw [decomposition] at control
  rw [momentNorm]
  convert control using 1 <;> ring

theorem fourPointArithmeticCenter_forced_hasDerivAt {trajectory : ℝ → FourPointConfiguration}
    {coefficient time : ℝ} {forcing : FourPointConfiguration}
    (equation : ∀ target, HasDerivAt (fun current => trajectory current target)
      (fourPointField coefficient (trajectory time) target + forcing target) time) :
    HasDerivAt (fun current => fourPointArithmeticCenter (trajectory current))
      (fourPointArithmeticCenter (fourPointField coefficient (trajectory time)) + fourPointArithmeticCenter forcing) time := by
  have derivative := (HasDerivAt.sum (u := Finset.univ) (fun target _ => equation target)).div_const 4
  simpa only [fourPointArithmeticCenter, Finset.sum_add_distrib, add_div] using derivative

end EulerNonuniqueness.Section6
