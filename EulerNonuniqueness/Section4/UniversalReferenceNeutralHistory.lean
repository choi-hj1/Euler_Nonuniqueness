import EulerNonuniqueness.Section4.UniversalReferenceMechanicalData
import EulerNonuniqueness.Section4.PaperNeutralDifferentialBound
import EulerNonuniqueness.Section4.ReferenceInitialInvariants
import EulerNonuniqueness.Section6.PaperCentroidEndpoints
import EulerNonuniqueness.General.InteriorNormGronwall

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000

theorem exists_uniform_paper_reference_neutral_history :
    ∃ memory ≥ (1 : ℝ), ∀ (scales : Scales),
      0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ {threshold constant : ℝ}, threshold ≤ 1 / 8 → 0 ≤ constant →
      ∀ᶠ frequency : ℝ in atTop,
      let changed : Scales := {scales with frequency := frequency}
      ∀ {count : ℕ} (motion : PatchMotion count) (evolution : FinitePatchEvolution changed motion 2),
      ∀ {phase unstable : Fin count → ℝ}, ReferenceInitialDisks changed motion phase unstable threshold →
      ReferenceCoarseBounds changed motion threshold constant →
      ∀ time ∈ Icc (0 : ℝ) 2, ∀ index : Fin count,
        ‖centroidAsymmetry motion time index‖ ≤
          (497664 / Real.pi) * changed.hessian * changed.length (index.val + 1) ^ 2 * time *
            Real.exp ((4608 / Real.pi) * changed.strain * time) ∧
        ‖centroidAsymmetry motion time index‖ ≤ memory * changed.hessian * changed.length (index.val + 1) ^ 2 := by
  let memory := 1 + (995328 / Real.pi) * Real.exp (9216 / Real.pi)
  have memoryOne : (1 : ℝ) ≤ memory := by
    have termNonnegative : 0 ≤ (995328 / Real.pi) * Real.exp (9216 / Real.pi) := by positivity
    dsimp only [memory]
    linarith
  refine ⟨memory, memoryOne, ?_⟩
  intro scales amplitudePositive ratioLarge alphaPositive threshold constant thresholdSmall constantNonnegative
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioLarge alphaPositive
      thresholdSmall constantNonnegative,
    scales.eventually_reference_coarse_boundary_label_gaps amplitudePositive ratioLarge alphaPositive
      thresholdSmall constantNonnegative,
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio)
      (by norm_num : (0 : ℝ) < 1 / 1000),
    scales.eventually_omega_pow_length_lt (by linarith : 1 < scales.ratio) alphaPositive 0
      (by norm_num : (0 : ℝ) < 1 / 64),
    (scales.strain_tendsto_zero ratioLarge alphaPositive).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency frequencyLarge mechanical gaps radii lengths strainSmall
  dsimp only
  intro count motion evolution phase unstable initial coarse
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyLarge
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have radiusPositive (index : Fin count) := changed.radius_pos amplitudePositive frequencyPositive ratioPositive (index.val + 1)
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (changed.location_pos _).le _)
  have actual := mechanical motion evolution coarse
  have control (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (index : Fin count) (patch : Fin 4) :
      ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle changed motion time index patch bound := by
    obtain ⟨_, _, _, _, _, _, _, _, small, boundary⟩ := actual time member index
    exact ⟨_, small.trans (by norm_num), boundary patch⟩
  have separated (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2)
      (index other : Fin count) (patch otherPatch : Fin 4) (different : (other, otherPatch) ≠ (index, patch)) :=
    gaps motion coarse time member index other patch otherPatch (Ne.symm different)
  have receiverBounded (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (index : Fin count) (patch : Fin 4) :
      motion.domain time index patch ⊆ closedBall (quadrupoleCenter motion time index) (3 * changed.length (index.val + 1)) := by
    obtain ⟨_, lower, upper, asymmetry, unstableSmall, stableSmall, _, _, deformationSmall, boundary⟩ := actual time member index
    have lengthPositive := changed.length_pos (index.val + 1)
    have lengthSmall : changed.length (index.val + 1) ≤ 1 / 64 := by
      simpa only [changed, pow_zero, one_mul] using (lengths (index.val + 1)).le
    have asymmetrySmall : ‖centroidAsymmetry motion time index‖ ≤ changed.length (index.val + 1) / 64 :=
      asymmetry.trans (by nlinarith)
    have radialSmall : radialShape motion time index ≤ 1 / 2 := by
      rw [radialShape_eq_unstable_add_stable]
      linarith [(le_abs_self _).trans unstableSmall, (le_abs_self _).trans stableSmall]
    have diagonalPositive : 0 < diagonalDifference motion time index :=
      (by positivity : 0 < changed.length (index.val + 1) ^ 2 / 2).trans_le lower
    obtain ⟨positiveBound, negativeBound⟩ := halfDiagonals_norm_le_of_reference_shape lengthPositive
      diagonalPositive upper radialSmall
    have radiusSmall : changed.radius (index.val + 1) ≤ changed.length (index.val + 1) / 1000 := by
      simpa only [changed, div_eq_mul_inv, one_div, one_mul, mul_comm] using (radii (index.val + 1)).le
    intro position memberPosition
    have centerControl : ‖quadrupoleCenter motion time index - quadrupoleCenter motion time index‖ ≤ (0 : ℝ) := by simp
    have commonBoundary (otherPatch : Fin 4) : BoundaryCloseToCircle changed motion time index otherPatch (1 / 16) := by
      obtain ⟨relabeling, periodic, relabelingBound, errorBound⟩ := boundary otherPatch
      exact ⟨relabeling, periodic, relabelingBound, errorBound.mono deformationSmall⟩
    have estimate := evolution.reference_domain_confinement
      (boundaryError := (1 / 16 : ℝ))
      member index commonBoundary (radiusPositive index)
      positiveBound negativeBound asymmetrySmall centerControl patch position memberPosition
    rw [mem_closedBall, dist_eq_norm]
    dsimp only [changed] at estimate radiusSmall lengthPositive ⊢
    linarith only [estimate, radiusSmall, lengthPositive]
  intro time member index
  have centroidData (patch : Fin 4) := evolution.patchCentroid_closed_derivative_of_boundary_gaps
    (by norm_num) amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index patch
  let velocity := fun current =>
    (patchAverageVelocity changed motion current index 0 (biotSavart (patchVorticity changed motion current)) +
      patchAverageVelocity changed motion current index 1 (biotSavart (patchVorticity changed motion current)) -
      patchAverageVelocity changed motion current index 2 (biotSavart (patchVorticity changed motion current)) -
      patchAverageVelocity changed motion current index 3 (biotSavart (patchVorticity changed motion current))) / 4
  have trajectoryContinuous : ContinuousOn (fun current => centroidAsymmetry motion current index) (Icc (0 : ℝ) 2) :=
    ((((centroidData 0).1.add (centroidData 1).1).sub (centroidData 2).1).sub (centroidData 3).1).div_const 4
  have velocityContinuous : ContinuousOn velocity (Icc (0 : ℝ) 2) :=
    ((((centroidData 0).2.1.add (centroidData 1).2.1).sub (centroidData 2).2.1).sub (centroidData 3).2.1).div_const 4
  have equation (current : ℝ) (inside : current ∈ Ioo (0 : ℝ) 2) :
      HasDerivAt (fun next => centroidAsymmetry motion next index) (velocity current) current := by
    have derivatives (patch : Fin 4) := evolution.patchCentroid_hasDerivAt_of_boundary_gaps (by norm_num)
      amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index patch inside
    exact ((((derivatives 0).add (derivatives 1)).sub (derivatives 2)).sub (derivatives 3)).div_const 4
  have derivativeBound (current : ℝ) (inside : current ∈ Ioo (0 : ℝ) 2) :
      ‖velocity current‖ ≤ (4608 / Real.pi) * changed.strain * ‖centroidAsymmetry motion current index‖ +
        (497664 / Real.pi) * changed.hessian * changed.length (index.val + 1) ^ 2 := by
    rw [← (equation current inside).deriv]
    exact evolution.reference_neutral_derivative_bound_of_boundary_gaps (by norm_num)
      amplitudePositive frequencyLarge ratioLarge alphaPositive control separated index inside
      (actual current ⟨inside.1.le, inside.2.le⟩ index).1
      (receiverBounded current ⟨inside.1.le, inside.2.le⟩ index)
  have history := General.norm_constant_forcing_gronwall_of_interior_derivative (by norm_num : (0 : ℝ) < 2)
    (by positivity : 0 ≤ (4608 / Real.pi) * changed.strain)
    (by positivity : 0 ≤ (497664 / Real.pi) * changed.hessian * changed.length (index.val + 1) ^ 2)
    trajectoryContinuous velocityContinuous equation derivativeBound time member
  rw [(evolution.reference_initial_center_and_asymmetry (by norm_num) amplitudePositive frequencyPositive ratioPositive initial index).2,
    norm_zero, zero_add] at history
  refine ⟨history, history.trans ?_⟩
  have timeNonnegative := member.1
  have timeBound := member.2
  have exponentBound : (4608 / Real.pi) * changed.strain * time ≤ 9216 / Real.pi := by
    calc
      _ ≤ (4608 / Real.pi) * 1 * 2 := by gcongr <;> first | exact strainSmall.le | exact timeBound
      _ = _ := by ring
  calc
    _ ≤ (497664 / Real.pi) * changed.hessian * changed.length (index.val + 1) ^ 2 * 2 *
        Real.exp (9216 / Real.pi) := by gcongr
    _ = ((995328 / Real.pi) * Real.exp (9216 / Real.pi)) * changed.hessian * changed.length (index.val + 1) ^ 2 := by ring
    _ ≤ memory * changed.hessian * changed.length (index.val + 1) ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right
        · dsimp only [memory]; linarith
        · exact hessianNonnegative
      · exact sq_nonneg _

end EulerNonuniqueness.Paper
