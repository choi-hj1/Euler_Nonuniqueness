import EulerNonuniqueness.Section6.MovingPatchMovingAngularMoment
import EulerNonuniqueness.Section6.QuadrupoleMaterialMoments
import EulerNonuniqueness.Section3.FiniteMovingPatchMotion

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

variable {count : ℕ}

theorem quadrupoleDensity_eq_subfamily (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (time : ℝ) (index : Fin count) :
    quadrupoleDensity scales family.patchMotion time index = family.subfamilyVorticity (quadrupolePatchLabels index) time := by
  funext position
  dsimp only [quadrupoleDensity, subfamilyVorticity, quadrupolePatchLabels]
  rw [Finset.sum_image (fun first _ second _ equality => (quadrupolePatchLabel_injective index) equality)]
  apply Finset.sum_congr rfl
  intro patch member
  exact congrFun (family.patchDensity_eq scales densityEquation time index patch) position

theorem patchCentroid_differentiableAt (family : FiniteMovingPatchFamily (count * 4))
    {time : ℝ} (inside : ∀ index, time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ index label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (index : Fin count) (patch : Fin 4) :
    DifferentiableAt ℝ (fun parameter => patchCentroid family.patchMotion parameter index patch) time := by
  have equality : (fun parameter => patchCentroid family.patchMotion parameter index patch) =
      (family.patch (finProdFinEquiv (index, patch))).centroid :=
    funext (fun parameter => family.patchCentroid_eq parameter index patch)
  rw [equality]
  exact ((family.patch (finProdFinEquiv (index, patch))).centroid_hasDerivAt (inside _)
    (family.vorticity_integrable time) (family.vorticity_memLp time _) (material _)).differentiableAt

theorem quadrupoleCenter_differentiableAt (family : FiniteMovingPatchFamily (count * 4))
    {time : ℝ} (inside : ∀ index, time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ index label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label)) (index : Fin count) :
    DifferentiableAt ℝ (fun parameter => quadrupoleCenter family.patchMotion parameter index) time := by
  change DifferentiableAt ℝ
    (fun parameter => (∑ patch : Fin 4, patchCentroid family.patchMotion parameter index patch) / 4) time
  exact (DifferentiableAt.sum fun patch _ => family.patchCentroid_differentiableAt inside material index patch).div_const 4

theorem quadrupole_angularImpulse_hasDerivAt_external (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {time : ℝ} (inside : ∀ index, time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ index label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label)) (index : Fin count) :
    HasDerivAt (fun parameter => angularImpulse scales family.patchMotion parameter index)
      (2 * ∫ position, @inner ℝ ℂ _ (position - quadrupoleCenter family.patchMotion time index)
        (quadrupoleDensity scales family.patchMotion time index position •
          (biotSavart (family.vorticity time) position -
            biotSavart (quadrupoleDensity scales family.patchMotion time index) position -
            deriv (fun parameter => quadrupoleCenter family.patchMotion parameter index) time))) time := by
  have centerDerivative := (family.quadrupoleCenter_differentiableAt inside material index).hasDerivAt
  have derivative := family.subfamily_moving_angular_moment_hasDerivAt_external
    (quadrupolePatchLabels index) inside material centerDerivative
  have integralIdentity (parameter : ℝ) : angularImpulse scales family.patchMotion parameter index =
      ∫ position, family.subfamilyVorticity (quadrupolePatchLabels index) parameter position *
        ‖position - quadrupoleCenter family.patchMotion parameter index‖ ^ 2 := by
    unfold angularImpulse
    rw [family.quadrupoleDensity_eq_subfamily scales densityEquation]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun position => mul_comm _ _
  simp_rw [integralIdentity, family.quadrupoleDensity_eq_subfamily scales densityEquation]
  exact derivative

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
