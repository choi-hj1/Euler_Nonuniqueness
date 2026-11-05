import EulerNonuniqueness.Section4.ReferenceRefinedCenterVelocity
import EulerNonuniqueness.Section4.ReferenceOuterField
import EulerNonuniqueness.Section4.ReferenceNeutralMoment
import EulerNonuniqueness.Section3.HolderPaperBoundaryBound
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000

theorem exists_uniform_reference_outer_displacement_bound
    (amplitude bound : ℝ) (amplitudePositive : 0 < amplitude) (boundNonnegative : 0 ≤ bound) :
    ∃ constant ≥ (0 : ℝ),
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales),
      scales.amplitude = amplitude →
      (∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) →
      ∀ {horizon finish threshold : ℝ},
      ∀ (evolution : FinitePatchEvolution scales family.patchMotion horizon),
      0 < horizon → 0 ≤ finish → finish ≤ 2 → Icc 0 finish ⊆ Icc 0 horizon →
      1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ {phase unstable : Fin count → ℝ},
      ReferenceInitialDisks scales family.patchMotion phase unstable threshold →
      (∀ time ∈ Icc 0 finish, ∀ index,
        time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime) →
      (∀ time ∈ Icc 0 finish, ∀ index label, (family.patch index).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch index).boundary time label)) →
      (∀ time ∈ Icc 0 finish, ∀ index : Fin count,
        scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion time index) →
      (∀ time ∈ Icc 0 finish, ∀ index : Fin count,
        diagonalDifference family.patchMotion time index ≤ 2 * scales.length (index.val + 1) ^ 2) →
      (∀ time ∈ Icc 0 finish, ∀ index, |radialShape family.patchMotion time index| ≤ 1 / 2) →
      (∀ time ∈ Icc 0 finish, ∀ index,
        ‖centroidAsymmetry family.patchMotion time index‖ ≤ scales.length (index.val + 1) / 64) →
      (∀ time ∈ Icc 0 finish, ∀ receiver source : Fin count, receiver ≠ source →
        |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤
          ‖quadrupoleCenter family.patchMotion time receiver - quadrupoleCenter family.patchMotion time source‖) →
      (∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000) →
      (∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000) →
      ∀ (deformation : ℝ → Fin count → ℝ),
      (∀ time ∈ Icc 0 finish, ∀ index patch,
        BoundaryCloseToCircle scales family.patchMotion time index patch (deformation time index)) →
      (∀ time ∈ Icc 0 finish, ∀ index, 0 ≤ deformation time index) →
      (∀ time ∈ Icc 0 finish, ∀ index, deformation time index ≤ 1 / 16) →
      (∀ time ∈ Icc 0 finish, ∀ index,
        deformation time index ≤ bound / scales.omega (index.val + 1) ^ 2) →
      scales.strain ≤ 1 → scales.hessian ≤ 1 →
      ∀ time ∈ Icc 0 finish, ∀ index : Fin count, index.val = 0 →
        ‖quadrupoleCenter family.patchMotion time index - (scales.location 1 : ℂ)‖ /
          scales.length 1 ≤ constant * scales.outerDisplacementBound := by
  let memory := (995328 / Real.pi) * Real.exp (2304 / Real.pi)
  let residual := (13824000000 + 113246208 / Real.pi) * bound / amplitude
  let coefficient := 96 / Real.pi + 40000 * memory + 497664 / Real.pi + residual
  have memoryNonnegative : 0 ≤ memory := by dsimp only [memory]; positivity
  have residualNonnegative : 0 ≤ residual := by dsimp only [residual]; positivity
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  refine ⟨2 * coefficient, by positivity, ?_⟩
  intro count family scales amplitudeEquation densityEquation horizon finish threshold evolution horizonPositive
    finishNonnegative finishBound timeRange frequencyBound ratioBound alphaPositive phase unstable initial inside material
    differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation lengthSmall radiusSmall deformation
    control nonnegative small deformationBound strainBound hessianBound
  have actualAmplitudePositive : 0 < scales.amplitude := amplitudeEquation.symm ▸ amplitudePositive
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have omegaOnePositive := scales.omega_pos frequencyPositive ratioPositive 1
  have lengthOnePositive := scales.length_pos 1
  have hessianNonnegative : 0 ≤ scales.hessian := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (scales.location_pos _).le _)
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have commonControl (time : ℝ) (member : time ∈ Icc 0 finish) (index : Fin count) (patch : Fin 4) :
      BoundaryCloseToCircle scales family.patchMotion time index patch (1 / 16) := by
    obtain ⟨relabeling, periodic, relabelingBound, errorBound⟩ := control time member index patch
    exact ⟨relabeling, periodic, relabelingBound, errorBound.mono (small time member index)⟩
  have radiusWeaker (index : Fin count) :
      scales.radius (index.val + 1) * (1 + (1 : ℝ) / 16) ≤ scales.length (index.val + 1) / 32 := by
    linarith only [radiusSmall index, scales.length_pos (index.val + 1)]
  have neutral (index : Fin count) := family.reference_centroidAsymmetry_bound scales densityEquation evolution
    horizonPositive finishNonnegative timeRange actualAmplitudePositive frequencyBound ratioBound alphaPositive initial
    inside material differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation lengthSmall commonControl
    radiusWeaker index
  have neutralBound (time : ℝ) (member : time ∈ Icc 0 finish) (index : Fin count) :
      ‖centroidAsymmetry family.patchMotion time index‖ ≤ memory * scales.hessian * scales.length (index.val + 1) ^ 2 := by
    have timeNonnegative := member.1
    have timeBound : time ≤ 2 := member.2.trans finishBound
    have exponentBound : (1152 / Real.pi) * scales.strain * time ≤ 2304 / Real.pi := by
      calc
        _ ≤ (1152 / Real.pi) * 1 * 2 := by gcongr
        _ = _ := by ring
    apply (neutral index time member).trans
    calc
      _ ≤ (497664 / Real.pi) * scales.hessian * scales.length (index.val + 1) ^ 2 * 2 *
          Real.exp (2304 / Real.pi) := by gcongr
      _ = _ := by dsimp only [memory]; ring
  have geometry (time : ℝ) (member : time ∈ Icc 0 finish) (index : Fin count) :=
    evolution.reference_centroid_field_geometry (timeRange member) actualAmplitudePositive frequencyPositive ratioPositive
      (differenceLower time member) (differenceUpper time member) (radialSmall time member) (asymmetrySmall time member)
      (centerSeparation time member) lengthSmall radiusSmall (deformation time) (control time member)
      (nonnegative time member) (small time member) index
  intro time member index outer
  let tail := ∑' source : ℕ, scales.circulation (source + 2)
  let budget := tail + scales.hessian * scales.omega 1 * scales.length 1 ^ 2 +
    scales.hessian * scales.length 1 ^ 2 + scales.length 1 / scales.omega 1 ^ 4
  have tailNonnegative : 0 ≤ tail := tsum_nonneg fun source =>
    (scales.circulation_pos frequencyPositive ratioPositive _).le
  have budgetIdentity : budget = scales.length 1 * scales.outerDisplacementBound := by
    dsimp only [budget, tail, Scales.outerDisplacementBound]
    field_simp [(scales.length_pos 1).ne', (scales.omega_pos frequencyPositive ratioPositive 1).ne']
    <;> ring
  have velocityBound (current : ℝ) (currentInside : current ∈ Ico 0 finish) :
      ‖deriv (fun next => quadrupoleCenter family.patchMotion next index) current‖ ≤ coefficient * budget := by
    have closed : current ∈ Icc 0 finish := ⟨currentInside.1, currentInside.2.le⟩
    have lengthBound := scales.length_le_one frequencyPositive ratioPositive (index.val + 1)
    have relative := family.reference_refined_center_velocity_bound scales evolution (timeRange closed)
      actualAmplitudePositive frequencyBound ratioBound alphaPositive index (fun patch => inside current closed _) (by
        intro patch label
        rw [family.patchVorticity_eq scales densityEquation]
        exact material current closed _ label)
      (control current closed index) (nonnegative current closed index) (small current closed index)
      boundNonnegative (deformationBound current closed index) lengthBound hessianBound (geometry current closed index)
    have external := evolution.reference_outer_field_bound (timeRange closed) actualAmplitudePositive frequencyBound
      ratioBound alphaPositive index outer (geometry current closed index)
    have triangle : ‖deriv (fun next => quadrupoleCenter family.patchMotion next index) current‖ ≤
        ‖deriv (fun next => quadrupoleCenter family.patchMotion next index) current -
          biotSavart (externalPatchVorticity scales family.patchMotion current index)
            (quadrupoleCenter family.patchMotion current index)‖ +
        ‖biotSavart (externalPatchVorticity scales family.patchMotion current index)
          (quadrupoleCenter family.patchMotion current index)‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (deriv (fun next => quadrupoleCenter family.patchMotion next index) current -
          biotSavart (externalPatchVorticity scales family.patchMotion current index)
            (quadrupoleCenter family.patchMotion current index))
        (biotSavart (externalPatchVorticity scales family.patchMotion current index)
          (quadrupoleCenter family.patchMotion current index))
    have combined := triangle.trans (add_le_add relative external)
    have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
    have momentCost := mul_le_mul_of_nonneg_left (neutralBound current closed index)
      (by positivity : 0 ≤ 40000 * scales.omega (index.val + 1))
    have preliminary := combined.trans (add_le_add_right
      (add_le_add_right (add_le_add_right momentCost _) _) _)
    simp only [outer, zero_add, amplitudeEquation] at preliminary
    have first : 96 / Real.pi ≤ coefficient := by
      dsimp only [coefficient]
      linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 497664) Real.pi_pos.le]
    have second : 40000 * memory ≤ coefficient := by
      dsimp only [coefficient]
      linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 96) Real.pi_pos.le,
        div_nonneg (by norm_num : (0 : ℝ) ≤ 497664) Real.pi_pos.le]
    have third : 497664 / Real.pi ≤ coefficient := by
      dsimp only [coefficient]
      linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 96) Real.pi_pos.le]
    have fourth : residual ≤ coefficient := by
      dsimp only [coefficient]
      linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 96) Real.pi_pos.le,
        div_nonneg (by norm_num : (0 : ℝ) ≤ 497664) Real.pi_pos.le]
    apply preliminary.trans
    calc
      _ = (96 / Real.pi) * tail + (40000 * memory) *
          (scales.hessian * scales.omega 1 * scales.length 1 ^ 2) +
          (497664 / Real.pi) * (scales.hessian * scales.length 1 ^ 2) +
          residual * (scales.length 1 / scales.omega 1 ^ 4) := by dsimp only [tail, residual]; ring
      _ ≤ coefficient * tail + coefficient * (scales.hessian * scales.omega 1 * scales.length 1 ^ 2) +
          coefficient * (scales.hessian * scales.length 1 ^ 2) +
          coefficient * (scales.length 1 / scales.omega 1 ^ 4) := by
        exact add_le_add (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right first tailNonnegative)
          (mul_le_mul_of_nonneg_right second (by positivity)))
          (mul_le_mul_of_nonneg_right third (by positivity)))
          (mul_le_mul_of_nonneg_right fourth (by positivity))
      _ = coefficient * budget := by dsimp only [budget]; ring
  have derivative (current : ℝ) (currentInside : current ∈ Icc 0 finish) :=
    (family.quadrupoleCenter_differentiableAt (inside current currentInside) (material current currentInside) index).hasDerivAt
  have displacement := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun current currentInside => (derivative current currentInside).hasDerivWithinAt) velocityBound time member
  rw [(evolution.reference_initial_center_and_asymmetry horizonPositive.le actualAmplitudePositive frequencyPositive
    ratioPositive initial index).1, outer, zero_add, sub_zero] at displacement
  have budgetNonnegative : 0 ≤ budget := by dsimp only [budget]; positivity
  have final := displacement.trans (mul_le_mul_of_nonneg_left (member.2.trans finishBound)
    (mul_nonneg coefficientNonnegative budgetNonnegative))
  apply (div_le_iff₀ (scales.length_pos 1)).mpr
  rw [budgetIdentity] at final
  exact final.trans_eq (by ring)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
