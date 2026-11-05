import EulerNonuniqueness.Section4.UniversalReferenceNeutralHistory
import EulerNonuniqueness.Section4.PaperReferenceCenterVelocity
import EulerNonuniqueness.Section4.ReferenceOuterField
import EulerNonuniqueness.Section6.PaperAngularMomentDynamics
import EulerNonuniqueness.General.InteriorDerivativeError

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000

theorem exists_uniform_paper_reference_outer_displacement :
    ∃ constant ≥ (1 : ℝ), ∀ (scales : Scales),
      0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ {threshold bound : ℝ}, threshold ≤ 1 / 8 → 0 ≤ bound → bound ≤ scales.amplitude →
      ∀ᶠ frequency : ℝ in atTop,
      let changed : Scales := {scales with frequency := frequency}
      ∀ {count : ℕ} (motion : PatchMotion count) (evolution : FinitePatchEvolution changed motion 2),
      ∀ {phase unstable : Fin count → ℝ}, ReferenceInitialDisks changed motion phase unstable threshold →
      ReferenceCoarseBounds changed motion threshold bound →
      ∀ time ∈ Icc (0 : ℝ) 2, ∀ index : Fin count, index.val = 0 →
        ‖quadrupoleCenter motion time index - (changed.location 1 : ℂ)‖ / changed.length 1 ≤
          constant * changed.outerDisplacementBound := by
  obtain ⟨memory, memoryOne, neutralFactories⟩ := exists_uniform_paper_reference_neutral_history
  let residual := 13824000000 + 113246208 / Real.pi
  let coefficient := 96 / Real.pi + 40000 * memory + 497664 / Real.pi + residual
  have memoryNonnegative : 0 ≤ memory := by linarith
  have residualNonnegative : 0 ≤ residual := by dsimp only [residual]; positivity
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  refine ⟨1 + 2 * coefficient, by linarith, ?_⟩
  intro scales amplitudePositive ratioLarge alphaPositive threshold bound thresholdSmall boundNonnegative boundAmplitude
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    neutralFactories scales amplitudePositive ratioLarge alphaPositive thresholdSmall boundNonnegative,
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioLarge alphaPositive thresholdSmall boundNonnegative,
    scales.eventually_reference_coarse_boundary_label_gaps amplitudePositive ratioLarge alphaPositive thresholdSmall boundNonnegative,
    (scales.hessian_tendsto_zero ratioLarge alphaPositive).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency frequencyLarge neutral mechanical gaps hessianSmall
  dsimp only
  intro count motion evolution phase unstable initial coarse time member index outer
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyLarge
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (changed.location_pos _).le _)
  have actual := mechanical motion evolution coarse
  have control (current : ℝ) (inside : current ∈ Icc (0 : ℝ) 2) (other : Fin count) (patch : Fin 4) :
      ∃ error ≤ (1 : ℝ), BoundaryCloseToCircle changed motion current other patch error := by
    obtain ⟨_, _, _, _, _, _, _, _, small, boundary⟩ := actual current inside other
    exact ⟨_, small.trans (by norm_num), boundary patch⟩
  have separated (current : ℝ) (inside : current ∈ Icc (0 : ℝ) 2)
      (receiver source : Fin count) (patch otherPatch : Fin 4) (different : (source, otherPatch) ≠ (receiver, patch)) :=
    gaps motion coarse current inside receiver source patch otherPatch (Ne.symm different)
  have radiusPositive (other : Fin count) := changed.radius_pos amplitudePositive frequencyPositive ratioPositive (other.val + 1)
  have centroidData (patch : Fin 4) := evolution.patchCentroid_closed_derivative_of_boundary_gaps
    (by norm_num) amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index patch
  have centerContinuous : ContinuousOn (fun current => quadrupoleCenter motion current index) (Icc (0 : ℝ) 2) :=
    (continuousOn_finset_sum Finset.univ fun patch _ => (centroidData patch).1).div_const 4
  let velocity := fun current => (∑ patch : Fin 4,
    patchAverageVelocity changed motion current index patch (biotSavart (patchVorticity changed motion current))) / 4
  have equation (current : ℝ) (inside : current ∈ Ioo (0 : ℝ) 2) :
      HasDerivAt (fun next => quadrupoleCenter motion next index) (velocity current) current :=
    evolution.quadrupoleCenter_hasDerivAt_of_boundary_gaps (by norm_num) amplitudePositive frequencyPositive
      ratioPositive radiusPositive control separated index inside
  let tail := ∑' source : ℕ, changed.circulation (source + 2)
  let budget := tail + changed.hessian * changed.omega 1 * changed.length 1 ^ 2 +
    changed.hessian * changed.length 1 ^ 2 + changed.length 1 / changed.omega 1 ^ 4
  have tailNonnegative : 0 ≤ tail := tsum_nonneg fun source =>
    (changed.circulation_pos frequencyPositive ratioPositive _).le
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive 1
  have lengthPositive := changed.length_pos 1
  have budgetNonnegative : 0 ≤ budget := by dsimp only [budget]; positivity
  have budgetIdentity : budget = changed.length 1 * changed.outerDisplacementBound := by
    dsimp only [budget, tail, Scales.outerDisplacementBound]
    field_simp [lengthPositive.ne', omegaPositive.ne']
    <;> ring
  have residualBound : (13824000000 + 113246208 / Real.pi) * bound / changed.amplitude ≤ residual := by
    apply (div_le_iff₀ amplitudePositive).mpr
    exact (mul_le_mul_of_nonneg_left boundAmplitude residualNonnegative).trans_eq (by dsimp only [residual])
  have velocityBound (current : ℝ) (inside : current ∈ Ioo (0 : ℝ) 2) :
      ‖velocity current‖ ≤ coefficient * budget := by
    have closed : current ∈ Icc (0 : ℝ) 2 := ⟨inside.1.le, inside.2.le⟩
    have omegaIndexPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
    obtain ⟨geometry, _, _, _, _, _, _, deformationNonnegative, deformationSmall, boundary⟩ := actual current closed index
    have relative := evolution.reference_refined_center_average_velocity_bound closed amplitudePositive frequencyLarge
      ratioLarge alphaPositive index boundary deformationNonnegative deformationSmall boundNonnegative
      (by rw [div_eq_mul_inv, inv_pow]) (changed.length_le_one frequencyPositive ratioPositive _) hessianSmall.le geometry
    have external := evolution.reference_outer_field_bound closed amplitudePositive frequencyLarge ratioLarge alphaPositive index outer geometry
    have triangle : ‖velocity current‖ ≤
        ‖velocity current - biotSavart (externalPatchVorticity changed motion current index)
          (quadrupoleCenter motion current index)‖ +
        ‖biotSavart (externalPatchVorticity changed motion current index) (quadrupoleCenter motion current index)‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (velocity current - biotSavart (externalPatchVorticity changed motion current index) (quadrupoleCenter motion current index))
        (biotSavart (externalPatchVorticity changed motion current index) (quadrupoleCenter motion current index))
    have momentCost := mul_le_mul_of_nonneg_left ((neutral motion evolution initial coarse current closed index).2)
      (by positivity : 0 ≤ 40000 * changed.omega (index.val + 1))
    have preliminary := (triangle.trans (add_le_add relative external)).trans
      (add_le_add_right (add_le_add_right (add_le_add_right momentCost _) _) _)
    simp only [outer, zero_add] at preliminary
    have coefficientBounds : 96 / Real.pi ≤ coefficient ∧ 40000 * memory ≤ coefficient ∧
        497664 / Real.pi ≤ coefficient ∧ residual ≤ coefficient := by
      dsimp only [coefficient]
      have firstNonnegative : (0 : ℝ) ≤ 96 / Real.pi := by positivity
      have secondNonnegative : 0 ≤ 40000 * memory := mul_nonneg (by norm_num) memoryNonnegative
      have thirdNonnegative : (0 : ℝ) ≤ 497664 / Real.pi := by positivity
      exact ⟨((le_add_of_nonneg_right secondNonnegative).trans (le_add_of_nonneg_right thirdNonnegative)).trans
          (le_add_of_nonneg_right residualNonnegative),
        ((le_add_of_nonneg_left firstNonnegative).trans (le_add_of_nonneg_right thirdNonnegative)).trans
          (le_add_of_nonneg_right residualNonnegative),
        (le_add_of_nonneg_left (add_nonneg firstNonnegative secondNonnegative)).trans
          (le_add_of_nonneg_right residualNonnegative),
        le_add_of_nonneg_left (add_nonneg (add_nonneg firstNonnegative secondNonnegative) thirdNonnegative)⟩
    have actualResidualBound := residualBound.trans coefficientBounds.2.2.2
    apply preliminary.trans
    calc
      _ = (96 / Real.pi) * tail + (40000 * memory) * (changed.hessian * changed.omega 1 * changed.length 1 ^ 2) +
          (497664 / Real.pi) * (changed.hessian * changed.length 1 ^ 2) +
          ((13824000000 + 113246208 / Real.pi) * bound / changed.amplitude) * (changed.length 1 / changed.omega 1 ^ 4) := by
        dsimp only [tail]
        ring
      _ ≤ coefficient * tail + coefficient * (changed.hessian * changed.omega 1 * changed.length 1 ^ 2) +
          coefficient * (changed.hessian * changed.length 1 ^ 2) + coefficient * (changed.length 1 / changed.omega 1 ^ 4) :=
        add_le_add (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right coefficientBounds.1 tailNonnegative)
          (mul_le_mul_of_nonneg_right coefficientBounds.2.1 (by positivity)))
          (mul_le_mul_of_nonneg_right coefficientBounds.2.2.1 (by positivity)))
          (mul_le_mul_of_nonneg_right actualResidualBound (by positivity))
      _ = coefficient * budget := by dsimp only [budget]; ring
  have displacement := norm_sub_le_of_continuousOn_interior_derivative_bound member.1
    (mul_nonneg coefficientNonnegative budgetNonnegative)
    (centerContinuous.mono (Icc_subset_Icc le_rfl member.2))
    (fun current inside => equation current ⟨inside.1, inside.2.trans_le member.2⟩)
    (fun current inside => velocityBound current ⟨inside.1, inside.2.trans_le member.2⟩)
  rw [(evolution.reference_initial_center_and_asymmetry (by norm_num) amplitudePositive frequencyPositive
    ratioPositive initial index).1, outer, zero_add] at displacement
  have final := displacement.trans (mul_le_mul_of_nonneg_left member.2
    (mul_nonneg coefficientNonnegative budgetNonnegative))
  apply (div_le_iff₀ lengthPositive).mpr
  rw [budgetIdentity] at final
  have extraNonnegative : 0 ≤ changed.length 1 * changed.outerDisplacementBound := by rw [← budgetIdentity]; exact budgetNonnegative
  nlinarith

end EulerNonuniqueness.Paper
