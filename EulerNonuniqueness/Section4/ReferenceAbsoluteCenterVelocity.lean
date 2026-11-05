import EulerNonuniqueness.Section4.ReferenceAngularGeometry
import EulerNonuniqueness.Section4.ReferenceCenterDynamics
import EulerNonuniqueness.Section1.ForeignVelocityWeight

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 1000000

theorem reference_absolute_center_velocity_bound {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {horizon time error : ℝ}
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
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (control : ∀ index patch, BoundaryCloseToCircle scales family.patchMotion time index patch error)
    (errorNonnegative : 0 ≤ error) (errorSmall : error ≤ 1 / 16)
    (radiusSmall : ∀ index : Fin count,
      scales.radius (index.val + 1) * (1 + error) ≤ scales.length (index.val + 1) / 1000)
    (index : Fin count) :
    ‖deriv (fun current => quadrupoleCenter family.patchMotion current index) time‖ ≤
      600 * scales.omega (index.val + 1) * scales.length (index.val + 1) +
        (3456 / Real.pi) * scales.strain * scales.length (index.val + 1) +
        (48 / Real.pi) * ∑' source : ℕ, scales.circulation (source + 1) / scales.location (source + 1) := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have lengthPositive := scales.length_pos (index.val + 1)
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  let strain : ℝ≥0 := ⟨(1152 / Real.pi) * scales.strain, by positivity⟩
  let center := quadrupoleCenter family.patchMotion time index
  let distance := fun source : Fin count =>
    |scales.location (index.val + 1) - scales.location (source.val + 1)| / 8
  obtain ⟨sourceBounded, internalSeparated, separated⟩ := evolution.reference_angular_geometry timeInside
    amplitudePositive frequencyPositive ratioPositive differenceLower differenceUpper radialSmall asymmetrySmall
    centerSeparation lengthSmall control errorNonnegative errorSmall radiusSmall index
  have positive (source : Fin count) (member : source ∈ Finset.univ.erase index) : 0 < distance source := by
    exact div_pos (scales.location_distance_pos (fun equality =>
      (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality).symm))) (by norm_num)
  have relative := family.quadrupoleCenter_relative_deriv_bound (strain := strain) scales evolution timeInside
    amplitudePositive frequencyPositive ratioPositive index (fun patch => inside _) (by
      intro patch label
      rw [family.patchVorticity_eq scales densityEquation]
      exact material _ label) (by positivity) (by positivity) sourceBounded internalSeparated distance positive separated
    (scales.foreign_strain_weight_le frequencyBound ratioBound alphaPositive index)
  have fieldBound := (evolution.externalPatch_biotSavart_bounds timeInside amplitudePositive frequencyPositive ratioPositive
    index distance positive (separated center (Metric.mem_closedBall_self (by positivity)))
      (separated center (Metric.mem_closedBall_self (by positivity)))).1
  have fieldEstimate := fieldBound.trans (scales.foreign_velocity_weight_le frequencyBound ratioBound alphaPositive index)
  have identity : 3 * (scales.circulation (index.val + 1) /
      (2 * Real.pi * (scales.length (index.val + 1) / 200))) =
      600 * scales.omega (index.val + 1) * scales.length (index.val + 1) := by
    rw [Scales.circulation]
    field_simp
    <;> ring
  rw [identity] at relative
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (deriv (fun current => quadrupoleCenter family.patchMotion current index) time)
    (biotSavart (externalPatchVorticity scales family.patchMotion time index) center) 0
  simp only [sub_zero] at triangle
  apply (triangle.trans (add_le_add relative fieldEstimate)).trans_eq
  dsimp only [strain]
  simp only [NNReal.coe_mk]
  ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
