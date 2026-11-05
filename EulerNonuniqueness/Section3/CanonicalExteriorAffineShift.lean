import EulerNonuniqueness.Section3.CanonicalExteriorAffineCoordinate

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

theorem canonicalExteriorAffineCoordinate_exists_uniform_shift_admissibility (budget : ℝ) (budgetPositive : 0 < budget) :
    ∃ radius > 0,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (angular direction : PeriodicC1HolderHalf), ‖angular‖ ≤ radius →
      (∀ label, star (angular.val.1 label) = angular.val.1 label) →
      ∀ {frequency time distance weight : ℝ}, frequency ≠ 0 → 0 < distance → 0 ≤ weight →
      4 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) position) ≤ weight →
      ‖diskRelabelCurve angular 1 - standardCircleBanach‖ + ‖direction‖ ≤ radius → weight / |frequency| ≤ radius →
      ‖diskRelabelCurve angular 1 + direction - standardCircleBanach‖ +
        ‖(diskRelabelCurve angular 1 + direction) -
          family.canonicalExteriorAffineCoordinate index angular frequency time (diskRelabelCurve angular 1 + direction)‖ ≤ budget := by
  obtain ⟨originalRadius, originalPositive, constant, constantOne, bounds⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_near_identity_bound
  let radius := min originalRadius (min 1 (min (budget / 2) (budget / (4 * constant))))
  have constantPositive : 0 < constant := by linarith
  have radiusPositive : 0 < radius := by dsimp [radius]; positivity
  have originalLe : radius ≤ originalRadius := min_le_left _ _
  have radiusOne : radius ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have radiusHalf : radius ≤ budget / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have radiusScale : radius ≤ budget / (4 * constant) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have scaled : 2 * constant * radius ≤ budget / 2 := by
    have multiplied := (le_div_iff₀ (by positivity : 0 < 4 * constant)).mp radiusScale
    linarith
  refine ⟨radius, radiusPositive, ?_⟩
  intro count family index angular direction angularSmall realValues frequency time distance weight
    nonzero positive weightNonnegative small separated weightBound inside frequencySmall
  have directionBound : ‖direction‖ ≤ 1 := by
    linarith [norm_nonneg (diskRelabelCurve angular 1 - standardCircleBanach)]
  have actual := bounds family index angular (angularSmall.trans originalLe) realValues nonzero positive
    weightNonnegative small separated weightBound (diskRelabelCurve angular 1 + direction)
  simp only [add_sub_cancel_left] at actual
  have shiftBound : ‖(diskRelabelCurve angular 1 + direction) -
      family.canonicalExteriorAffineCoordinate index angular frequency time (diskRelabelCurve angular 1 + direction)‖ ≤ budget / 2 := by
    rw [norm_sub_rev]
    apply actual.trans
    calc
      _ ≤ constant * (weight / |frequency|) * 2 :=
        mul_le_mul_of_nonneg_left (by linarith : 1 + ‖direction‖ ≤ 2) (by positivity)
      _ ≤ 2 * constant * radius := by
        have estimate := mul_le_mul_of_nonneg_left frequencySmall (by positivity : 0 ≤ 2 * constant)
        convert estimate using 1 <;> ring
      _ ≤ _ := scaled
  have shapeBound : ‖diskRelabelCurve angular 1 + direction - standardCircleBanach‖ ≤ budget / 2 := by
    rw [show diskRelabelCurve angular 1 + direction - standardCircleBanach =
      (diskRelabelCurve angular 1 - standardCircleBanach) + direction by abel]
    exact (norm_add_le _ _).trans (inside.trans radiusHalf)
  linarith

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
