import EulerNonuniqueness.Section4.ReferenceRelativeExternalField
import EulerNonuniqueness.Section4.ReferenceAngularGeometry
import EulerNonuniqueness.Section4.ReferenceCenterDynamics

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 1000000

theorem reference_pair_center_velocity_bound {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {horizon time error tolerance : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (timeInside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (inside : ∀ index, time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ index label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (differenceLower : ∀ index : Fin count, scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion time index)
    (differenceUpper : ∀ index : Fin count, diagonalDifference family.patchMotion time index ≤ 2 * scales.length (index.val + 1) ^ 2)
    (radialSmall : ∀ index, |radialShape family.patchMotion time index| ≤ 1 / 2)
    (asymmetrySmall : ∀ index, ‖centroidAsymmetry family.patchMotion time index‖ ≤ scales.length (index.val + 1) / 64)
    (centerSeparation : ∀ receiver source : Fin count, receiver ≠ source →
      |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤
        ‖quadrupoleCenter family.patchMotion time receiver - quadrupoleCenter family.patchMotion time source‖)
    (centerUpper : ∀ receiver source : Fin count, receiver ≠ source →
      ‖quadrupoleCenter family.patchMotion time receiver - quadrupoleCenter family.patchMotion time source‖ ≤
        2 * |scales.location (receiver.val + 1) - scales.location (source.val + 1)|)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (control : ∀ index patch, BoundaryCloseToCircle scales family.patchMotion time index patch error)
    (errorNonnegative : 0 ≤ error) (errorSmall : error ≤ 1 / 16)
    (radiusSmall : ∀ index : Fin count,
      scales.radius (index.val + 1) * (1 + error) ≤ scales.length (index.val + 1) / 1000)
    (toleranceNonnegative : 0 ≤ tolerance)
    (omegaLength : ∀ index : Fin count,
      scales.omega (index.val + 1) * scales.length (index.val + 1) ≤ tolerance * scales.location (index.val + 1))
    (first second : Fin count) (different : first ≠ second) :
    ‖deriv (fun current => quadrupoleCenter family.patchMotion current first) time -
        deriv (fun current => quadrupoleCenter family.patchMotion current second) time‖ ≤
      ((15120 / Real.pi) * scales.strain + 1800 * tolerance) *
        |scales.location (first.val + 1) - scales.location (second.val + 1)| := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  let strain : ℝ≥0 := ⟨(1152 / Real.pi) * scales.strain, by positivity⟩
  let center := fun index : Fin count => quadrupoleCenter family.patchMotion time index
  let velocity := fun index : Fin count => deriv (fun current => quadrupoleCenter family.patchMotion current index) time
  let field := fun index : Fin count => biotSavart (externalPatchVorticity scales family.patchMotion time index) (center index)
  have geometry (index : Fin count) := evolution.reference_angular_geometry timeInside amplitudePositive frequencyPositive
    ratioPositive differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation lengthSmall control
    errorNonnegative errorSmall radiusSmall index
  have positive (receiver source : Fin count) (different : receiver ≠ source) :
      0 < |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8 := by
    exact div_pos (scales.location_distance_pos (fun equality => different (Fin.ext (Nat.add_right_cancel equality)))) (by norm_num)
  have relativeBound (index : Fin count) : ‖velocity index - field index‖ ≤
      600 * scales.omega (index.val + 1) * scales.length (index.val + 1) +
        3 * (strain : ℝ) * scales.length (index.val + 1) := by
    have lengthPositive := scales.length_pos (index.val + 1)
    have bound := family.quadrupoleCenter_relative_deriv_bound (strain := strain) scales evolution timeInside
      amplitudePositive frequencyPositive ratioPositive index (fun patch => inside _) (by
        intro patch label
        rw [family.patchVorticity_eq scales densityEquation]
        exact material _ label) (by positivity) (by positivity) (geometry index).1 (geometry index).2.1
      (fun source => |scales.location (index.val + 1) - scales.location (source.val + 1)| / 8)
      (fun source member => positive index source (Ne.symm (Finset.mem_erase.mp member).1))
      (geometry index).2.2 (scales.foreign_strain_weight_le frequencyBound ratioBound alphaPositive index)
    have identity : 3 * (scales.circulation (index.val + 1) /
        (2 * Real.pi * (scales.length (index.val + 1) / 200))) =
        600 * scales.omega (index.val + 1) * scales.length (index.val + 1) := by
      rw [Scales.circulation]
      field_simp
      <;> ring
    rw [identity] at bound
    exact bound.trans_eq (by ring)
  have externalBound := evolution.reference_relative_external_field_bound timeInside amplitudePositive frequencyBound
    ratioBound alphaPositive center (by
      intro receiver source different patch location locationInside
      exact (geometry receiver).2.2 (center receiver)
        (Metric.mem_closedBall_self (by have lengthPositive := scales.length_pos (receiver.val + 1); positivity))
        source (Finset.mem_erase.mpr ⟨Ne.symm different, Finset.mem_univ _⟩) patch location locationInside)
    first second different
  have triangle : ‖velocity first - velocity second‖ ≤
      ‖velocity first - field first‖ + ‖field first - field second‖ + ‖velocity second - field second‖ := by
    have estimate := norm_sub_le_norm_sub_add_norm_sub (velocity first) (field first) (velocity second)
    have last := norm_sub_le_norm_sub_add_norm_sub (field first) (field second) (velocity second)
    rw [norm_sub_rev (field second) (velocity second)] at last
    linarith
  have lengthBound (index : Fin count) : scales.length (index.val + 1) ≤ scales.location (index.val + 1) := by
    linarith [lengthSmall index, scales.location_pos (index.val + 1)]
  have locations := scales.location_sum_le_three_distance
    (show first.val + 1 ≠ second.val + 1 from fun equality => different (Fin.ext (Nat.add_right_cancel equality)))
  have omegaSum := add_le_add (omegaLength first) (omegaLength second)
  have lengthSum := add_le_add (lengthBound first) (lengthBound second)
  apply (triangle.trans (add_le_add (add_le_add (relativeBound first) externalBound) (relativeBound second))).trans
  calc
    _ = 600 * (scales.omega (first.val + 1) * scales.length (first.val + 1) +
        scales.omega (second.val + 1) * scales.length (second.val + 1)) +
      3 * (strain : ℝ) * (scales.length (first.val + 1) + scales.length (second.val + 1)) +
      ((2304 / Real.pi) * scales.strain * ‖center first - center second‖ +
        (144 / Real.pi) * scales.strain * |scales.location (first.val + 1) - scales.location (second.val + 1)|) := by ring
    _ ≤ 600 * (tolerance * scales.location (first.val + 1) + tolerance * scales.location (second.val + 1)) +
      3 * (strain : ℝ) * (scales.location (first.val + 1) + scales.location (second.val + 1)) +
      ((2304 / Real.pi) * scales.strain * (2 * |scales.location (first.val + 1) - scales.location (second.val + 1)|) +
        (144 / Real.pi) * scales.strain * |scales.location (first.val + 1) - scales.location (second.val + 1)|) := by
      gcongr
      exact centerUpper first second different
    _ = (600 * tolerance + 3 * (strain : ℝ)) *
        (scales.location (first.val + 1) + scales.location (second.val + 1)) +
      (4752 / Real.pi) * scales.strain * |scales.location (first.val + 1) - scales.location (second.val + 1)| := by ring
    _ ≤ (600 * tolerance + 3 * (strain : ℝ)) *
        (3 * |scales.location (first.val + 1) - scales.location (second.val + 1)|) +
      (4752 / Real.pi) * scales.strain * |scales.location (first.val + 1) - scales.location (second.val + 1)| := by gcongr
    _ = _ := by
      dsimp only [strain]
      simp only [NNReal.coe_mk]
      ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
