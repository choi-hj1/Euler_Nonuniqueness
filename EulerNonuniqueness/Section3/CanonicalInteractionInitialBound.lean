import EulerNonuniqueness.Section3.CanonicalInteractionParameter
import EulerNonuniqueness.Section3.DiskQuadraticObservableRecovery
import EulerNonuniqueness.Section3.CanonicalExteriorAffineShift

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

local instance interactionInitialC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskRelabelCurve_zero_angular : diskRelabelCurve 0 1 = standardCircleBanach := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [diskRelabelCurve_value]
  change Complex.exp ((1 : ℂ) * (Complex.I * 0)) * standardCircle label = standardCircle label
  simp

namespace FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem canonicalNormalizedInteractionCoordinate_exists_uniform_circle_bound :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        {frequency time distance weight : ℝ}, frequency ≠ 0 → 0 < distance → 0 ≤ weight →
      4 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) position) ≤ weight → weight / |frequency| ≤ radius →
      ‖family.canonicalNormalizedInteractionCoordinate index 0 frequency time standardCircleBanach‖ ≤
        constant * (weight / |frequency|) := by
  obtain ⟨observableRadius, observablePositive, observableConstant, observableOne, observableBounds⟩ :=
    diskNormalizedQuadraticObservable_exists_uniform_difference_bound
  obtain ⟨shiftRadius, shiftPositive, shifts⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_shift_admissibility observableRadius observablePositive
  obtain ⟨affineRadius, affinePositive, affineConstant, affineOne, affineBounds⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_near_identity_bound
  let constant := diskPhysicalGroupBound * observableConstant * affineConstant + 1
  have constantOne : 1 ≤ constant := by
    have nonnegative := mul_nonneg (mul_nonneg diskPhysicalGroupBound_nonnegative
      (by linarith : 0 ≤ observableConstant)) (by linarith : 0 ≤ affineConstant)
    dsimp only [constant]
    linarith
  refine ⟨min shiftRadius affineRadius, lt_min shiftPositive affinePositive, constant, constantOne, ?_⟩
  intro count family index frequency time distance weight nonzero positive weightNonnegative small separated weightBound frequencySmall
  have zeroReal : ∀ label, star ((0 : PeriodicC1HolderHalf).val.1 label) = (0 : PeriodicC1HolderHalf).val.1 label := by
    intro label
    change star (0 : ℂ) = 0
    simp
  have shifted := shifts family index 0 0 (by simpa using shiftPositive.le) zeroReal nonzero positive
    weightNonnegative small separated weightBound
    (by simpa only [diskRelabelCurve_zero_angular, sub_self, norm_zero, zero_add] using shiftPositive.le)
    (frequencySmall.trans (min_le_left _ _))
  have shiftBound := affineBounds family index 0 (by simpa using affinePositive.le) zeroReal nonzero positive
    weightNonnegative small separated weightBound standardCircleBanach
  change ‖diskPhysicalScaledGroup frequency (-time)
    (diskNormalizedQuadraticObservable (family.canonicalExteriorAffineCoordinate index 0 frequency time standardCircleBanach))‖ ≤ _
  generalize coordinateEq : family.canonicalExteriorAffineCoordinate index 0 frequency time = coordinate
    at shifted shiftBound ⊢
  rw [diskRelabelCurve_zero_angular, add_zero, sub_self, norm_zero, zero_add] at shifted
  rw [diskRelabelCurve_zero_angular, sub_self, norm_zero, add_zero, mul_one] at shiftBound
  generalize correctedEq : coordinate standardCircleBanach = corrected
    at shifted shiftBound ⊢
  have nearby : ‖corrected - standardCircleBanach‖ ≤ observableRadius := by
    rwa [norm_sub_rev] at shifted
  have observed := observableBounds _ standardCircleBanach nearby (by simpa using observablePositive.le)
  rw [diskNormalizedQuadraticObservable_circle, sub_zero] at observed
  have groupBound := diskPhysicalScaledGroup_norm_bound frequency (-time)
    (diskNormalizedQuadraticObservable corrected)
  generalize observableEq : diskNormalizedQuadraticObservable corrected = observable at observed groupBound ⊢
  generalize groupEq : diskPhysicalScaledGroup frequency (-time) observable = groupValue at groupBound ⊢
  have actual := observed.trans (mul_le_mul_of_nonneg_left shiftBound (by linarith : 0 ≤ observableConstant))
  have combined := groupBound.trans (mul_le_mul_of_nonneg_left actual diskPhysicalGroupBound_nonnegative)
  apply combined.trans
  rw [show constant = diskPhysicalGroupBound * observableConstant * affineConstant + 1 from rfl]
  nlinarith [div_nonneg weightNonnegative (abs_nonneg frequency)]

end FiniteMovingPatchFamily

end EulerNonuniqueness.Paper
