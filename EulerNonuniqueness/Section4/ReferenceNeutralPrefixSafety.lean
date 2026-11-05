import EulerNonuniqueness.Section4.ReferenceNeutralMoment
import EulerNonuniqueness.Section1.ExternalFieldScaleBounds
import EulerNonuniqueness.Section1.UniformScaleBounds

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_reference_neutral_clearance (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) {memory : ℝ} (memoryOne : 1 ≤ memory) :
    ∀ᶠ frequency : ℝ in atTop, 1 ≤ frequency ∧ ({scales with frequency := frequency}).hessian ≤ 1 ∧
      ∀ index : ℕ, memory * ({scales with frequency := frequency}).hessian *
        ({scales with frequency := frequency}).length index < 1 / 128 := by
  have memoryPositive : 0 < memory := by linarith
  have small := (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually
    (eventually_lt_nhds (by positivity : (0 : ℝ) < min 1 (1 / (128 * memory))))
  filter_upwards [eventually_ge_atTop (1 : ℝ), small] with frequency frequencyBound hessianSmall
  let changed : Scales := {scales with frequency := frequency}
  have hessianBound : changed.hessian < 1 := hessianSmall.trans_le (min_le_left _ _)
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos (zero_lt_one.trans_le frequencyBound) (by dsimp only [changed]; linarith) _).le
      (pow_nonneg (changed.location_pos _).le _)
  refine ⟨frequencyBound, hessianBound.le, ?_⟩
  intro index
  have lengthBound := changed.length_le_one (zero_lt_one.trans_le frequencyBound) (by dsimp only [changed]; linarith) index
  have numerical : memory * changed.hessian < 1 / 128 := by
    have divided := hessianSmall.trans_le (min_le_right _ _)
    have multiplied := (lt_div_iff₀ (by positivity : 0 < 128 * memory)).mp divided
    nlinarith only [multiplied]
  exact (mul_le_of_le_one_right (mul_nonneg memoryPositive.le hessianNonnegative) lengthBound).trans_lt numerical

namespace FiniteMovingPatchFamily

theorem exists_uniform_reference_neutral_prefix_improvement :
    ∃ memory ≥ (1 : ℝ), ∀ {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales),
      (∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) →
      ∀ {horizon finish error threshold : ℝ},
      ∀ (evolution : FinitePatchEvolution scales family.patchMotion horizon),
      0 < horizon → 0 ≤ finish → finish ≤ 2 → Icc 0 finish ⊆ Icc 0 horizon →
      0 < scales.amplitude → 1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ {phase unstable : Fin count → ℝ}, ReferenceInitialDisks scales family.patchMotion phase unstable threshold →
      (∀ time ∈ Icc 0 finish, ∀ source, time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime) →
      (∀ time ∈ Icc 0 finish, ∀ source label, (family.patch source).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch source).boundary time label)) →
      (∀ time ∈ Icc 0 finish, ∀ index : Fin count,
        scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion time index) →
      (∀ time ∈ Icc 0 finish, ∀ index : Fin count,
        diagonalDifference family.patchMotion time index ≤ 2 * scales.length (index.val + 1) ^ 2) →
      (∀ time ∈ Icc 0 finish, ∀ index, |radialShape family.patchMotion time index| ≤ 1 / 2) →
      (∀ time ∈ Icc 0 finish, ∀ index, ‖centroidAsymmetry family.patchMotion time index‖ ≤ scales.length (index.val + 1) / 64) →
      (∀ time ∈ Icc 0 finish, ∀ receiver source : Fin count, receiver ≠ source →
        |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤
          ‖quadrupoleCenter family.patchMotion time receiver - quadrupoleCenter family.patchMotion time source‖) →
      (∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000) →
      (∀ time ∈ Icc 0 finish, ∀ index patch, BoundaryCloseToCircle scales family.patchMotion time index patch error) →
      (∀ index : Fin count, scales.radius (index.val + 1) * (1 + error) ≤ scales.length (index.val + 1) / 32) →
      scales.strain ≤ 1 → scales.hessian ≤ 1 →
      (∀ index : Fin count, memory * scales.hessian * scales.length (index.val + 1) < 1 / 128) →
      ∀ time ∈ Icc 0 finish, ∀ index : Fin count,
        ‖centroidAsymmetry family.patchMotion time index‖ ≤ memory * scales.hessian * scales.length (index.val + 1) ^ 2 ∧
        ‖centroidAsymmetry family.patchMotion time index‖ ≤ memory * scales.length (index.val + 1) ^ 2 ∧
        ‖centroidAsymmetry family.patchMotion time index‖ < scales.length (index.val + 1) / 128 := by
  let rawMemory := (995328 / Real.pi) * Real.exp (2304 / Real.pi)
  let memory := max 1 rawMemory
  refine ⟨memory, le_max_left _ _, ?_⟩
  intro count family scales densityEquation horizon finish error threshold evolution horizonPositive finishNonnegative finishBound timeRange
    amplitudePositive frequencyBound ratioBound alphaPositive phase unstable initial inside material differenceLower differenceUpper radialSmall
    asymmetrySmall centerSeparation lengthSmall control radiusSmall strainBound hessianBound numerical time member index
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ scales.hessian := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (scales.location_pos _).le _)
  have neutral := family.reference_centroidAsymmetry_bound scales densityEquation evolution horizonPositive finishNonnegative timeRange
    amplitudePositive frequencyBound ratioBound alphaPositive initial inside material differenceLower differenceUpper radialSmall asymmetrySmall
    centerSeparation lengthSmall control radiusSmall index time member
  have timeNonnegative := member.1
  have timeBound : time ≤ 2 := member.2.trans finishBound
  have exponentBound : (1152 / Real.pi) * scales.strain * time ≤ 2304 / Real.pi := by
    calc
      _ ≤ (1152 / Real.pi) * 1 * 2 := by gcongr
      _ = _ := by ring
  have rawBound : ‖centroidAsymmetry family.patchMotion time index‖ ≤ rawMemory * scales.hessian * scales.length (index.val + 1) ^ 2 := by
    apply neutral.trans
    calc
      _ ≤ (497664 / Real.pi) * scales.hessian * scales.length (index.val + 1) ^ 2 * 2 * Real.exp (2304 / Real.pi) := by gcongr
      _ = _ := by dsimp only [rawMemory]; ring
  have actualBound : ‖centroidAsymmetry family.patchMotion time index‖ ≤ memory * scales.hessian * scales.length (index.val + 1) ^ 2 :=
    rawBound.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hessianNonnegative) (sq_nonneg _))
  have lengthPositive := scales.length_pos (index.val + 1)
  refine ⟨actualBound, actualBound.trans ?_, actualBound.trans_lt ?_⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by dsimp only [memory]; positivity) hessianBound) (sq_nonneg _)
  · have scaled := mul_lt_mul_of_pos_right (numerical index) lengthPositive
    nlinarith only [scaled]

end FiniteMovingPatchFamily
end EulerNonuniqueness.Paper
