import EulerNonuniqueness.Section6.MovingExteriorCoefficientBound
import EulerNonuniqueness.Section6.MovingPatchSubfamilyMoments
import EulerNonuniqueness.Section6.MaterialCoefficientTransport
import EulerNonuniqueness.Section6.WeightedExteriorFieldLipschitz

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem integral_exterior_material_coefficient {count : ℕ}
    (family : FiniteMovingPatchFamily count) (selected : Finset (Fin count))
    (center velocity : ℂ) (time : ℝ) (power : ℕ) {distance : ℝ}
    (positive : 0 < distance)
    (separated : ∀ source ∈ selected, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖center - position‖) :
    (∫ position : ℂ, family.subfamilyVorticity selected time position •
      (star (velocity - biotSavart (family.vorticity time) position) *
        (star (center - position))⁻¹ ^ power)) =
      ∑ source ∈ selected, family.density source •
        ∫ position in (family.patch source).domain time,
          star (velocity - biotSavart (family.vorticity time) position) *
            (star (center - position))⁻¹ ^ power := by
  apply family.integral_subfamilyVorticity_smul
  intro source member
  have conjugateContinuous : Continuous (star : ℂ → ℂ) := by fun_prop
  have smooth : IntegrableOn (fun position : ℂ =>
      star (velocity - biotSavart (family.vorticity time) position) *
        smoothConjugateInversePower distance power (center - position))
      ((family.patch source).domain time) :=
    (family.patch source).integral_continuous_function time
      ((conjugateContinuous.comp (continuous_const.sub (family.biotSavart_continuous time))).mul
        ((smoothConjugateInversePower_contDiff positive power).continuous.comp
          (continuous_const.sub continuous_id)))
  apply smooth.congr_fun _ ((family.patch source).domain_isOpen time).measurableSet
  intro position inside
  dsimp only
  rw [(smoothConjugateInversePower_eventuallyEq positive power
    (separated source member position inside)).self_of_nhds]

theorem vorticity_eq_erased_subfamily_add_patch {count : ℕ}
    (family : FiniteMovingPatchFamily count) (time : ℝ) (index : Fin count) :
    family.vorticity time = family.subfamilyVorticity (Finset.univ.erase index) time +
      family.patchVorticity time index := by
  funext position
  exact (Finset.sum_erase_add _ _ (Finset.mem_univ index)).symm

theorem centerVelocity_eq_external_average {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) {time : ℝ}
    (inside : time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (centered : (family.patch index).center =ᶠ[nhds time] (family.patch index).centroid) :
    (family.patch index).centerVelocity time =
      (volume.real ((family.patch index).domain time))⁻¹ •
        ∫ position in (family.patch index).domain time,
          biotSavart (family.subfamilyVorticity (Finset.univ.erase index) time) position := by
  have derivative := ((family.patch index).centroid_hasDerivAt inside
    (family.vorticity_integrable time) (family.vorticity_memLp time _) material).congr_of_eventuallyEq centered
  have velocityIdentity := ((family.patch index).center_equation time).unique derivative
  have sourceIntegrable := family.subfamilyVorticity_integrable (Finset.univ.erase index) time
  have receiverIntegrable := family.patchVorticity_integrable time index
  have sourceMembership := family.subfamilyVorticity_memLp (Finset.univ.erase index) time (ENNReal.ofReal (4 : ℝ))
  have receiverMembership := family.patchVorticity_memLp time index (ENNReal.ofReal (4 : ℝ))
  have finite : volume ((family.patch index).domain time) < ⊤ :=
    ((family.patch index).domain_isBounded time).measure_lt_top
  have sourceVelocityIntegrable := integrableOn_biotSavart_of_L1_L4_finite sourceIntegrable sourceMembership finite
  have receiverVelocityIntegrable := integrableOn_biotSavart_of_L1_L4_finite receiverIntegrable receiverMembership finite
  obtain ⟨supportRadius, _, supportBound⟩ := ((family.patch index).domain_isBounded time).exists_pos_norm_le
  have selfZero := integral_patch_self_interaction_density ((family.patch index).domain_isOpen time).measurableSet
    (show (family.patch index).domain time ⊆ Metric.closedBall 0 supportRadius from fun position member => by
      simpa only [Metric.mem_closedBall, dist_zero_right] using supportBound position member) (family.density index)
  rw [velocityIdentity, family.vorticity_eq_erased_subfamily_add_patch time index]
  simp_rw [biotSavart_add_of_L1_L4 sourceIntegrable receiverIntegrable sourceMembership receiverMembership]
  rw [integral_add sourceVelocityIntegrable receiverVelocityIntegrable]
  change _ • (_ + ∫ position in (family.patch index).domain time,
    biotSavart (((family.patch index).domain time).indicator (fun _ => family.density index)) position) = _
  rw [selfZero, add_zero]

theorem centerVelocity_external_defect_le {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) {time distance : ℝ}
    (inside : time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (centered : (family.patch index).center =ᶠ[nhds time] (family.patch index).centroid)
    (positive : 0 < distance) (small : 4 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖) :
    ‖(family.patch index).centerVelocity time -
      biotSavart (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time)‖ ≤
      (2 * (family.patch index).radius / Real.pi) *
        ∫ position, inverseSquareVorticityWeight (family.subfamilyVorticity (Finset.univ.erase index) time)
          ((family.patch index).center time) position := by
  have sourceIntegrable := family.subfamilyVorticity_integrable (Finset.univ.erase index) time
  have sourceMembership := family.subfamilyVorticity_memLp (Finset.univ.erase index) time (ENNReal.ofReal (4 : ℝ))
  have finite : volume ((family.patch index).domain time) < ⊤ :=
    ((family.patch index).domain_isBounded time).measure_lt_top
  have sourceVelocityIntegrable := integrableOn_biotSavart_of_L1_L4_finite sourceIntegrable sourceMembership finite
  have constantIntegrable : IntegrableOn (fun _ : ℂ =>
      biotSavart (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time))
      ((family.patch index).domain time) := integrableOn_const.mpr (Or.inr finite)
  have estimate := weighted_exterior_centroid_average_defect sourceIntegrable sourceMembership
    ((family.patch index).center time) ((family.patch index).domain_isOpen time).measurableSet finite
    ((family.patch index).domain_area_positive time) positive
    (show 2 * (family.patch index).radius ≤ distance / 2 by linarith)
    (fun position member => Metric.ball_subset_closedBall ((family.patch index).domain_subset_ball time member))
    (family.subfamily_support_separated (Finset.univ.erase index) ((family.patch index).center time) time distance separated)
  rw [integral_sub sourceVelocityIntegrable constantIntegrable, setIntegral_const, smul_sub,
    smul_smul, inv_mul_cancel₀ ((family.patch index).domain_area_positive time).ne', one_smul] at estimate
  rw [family.centerVelocity_eq_external_average index inside material centered]
  exact estimate

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
