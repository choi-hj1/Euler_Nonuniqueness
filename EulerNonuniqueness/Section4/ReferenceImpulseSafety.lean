import EulerNonuniqueness.Section4.ReferenceAngularScale
import EulerNonuniqueness.Section4.ReferenceNeutralMoment
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000

theorem exists_uniform_reference_impulse_safety_bound :
    ∃ constant ≥ (0 : ℝ), ∀ {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales),
      (∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) →
      ∀ {horizon finish error threshold : ℝ},
      ∀ (evolution : FinitePatchEvolution scales family.patchMotion horizon),
      0 < horizon → 0 ≤ finish → finish ≤ 2 → Icc 0 finish ⊆ Icc 0 horizon →
      0 < scales.amplitude → 1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ {phase unstable : Fin count → ℝ},
      ReferenceInitialDisks scales family.patchMotion phase unstable threshold → threshold ≤ 1 / 2 →
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
      (∀ time ∈ Icc 0 finish, ∀ index patch,
        BoundaryCloseToCircle scales family.patchMotion time index patch error) →
      0 ≤ error → error ≤ 1 / 16 →
      (∀ index : Fin count, scales.radius (index.val + 1) * (1 + error) ≤ scales.length (index.val + 1) / 1000) →
      (∀ index : Fin count, scales.omega (index.val + 1) * scales.length (index.val + 1) ≤ 1) →
      scales.strain ≤ 1 → scales.hessian ≤ 1 →
      ∀ time ∈ Icc 0 finish, ∀ index : Fin count,
        |angularImpulse scales family.patchMotion time index /
            (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) - 1| ≤
          constant * (scales.strain + scales.hessian) * time := by
  let memory := (995328 / Real.pi) * Real.exp (2304 / Real.pi)
  let secondary := (12 * memory + 36) * (1152 / Real.pi)
  let constant := 2400 * memory + secondary
  have memoryNonnegative : 0 ≤ memory := by dsimp only [memory]; positivity
  have secondaryNonnegative : 0 ≤ secondary := by dsimp only [secondary]; positivity
  refine ⟨constant, by dsimp only [constant]; positivity, ?_⟩
  intro count family scales densityEquation horizon finish error threshold evolution horizonPositive finishNonnegative
    finishBound timeRange amplitudePositive frequencyBound ratioBound alphaPositive phase unstable initial thresholdSmall
    inside material differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation lengthSmall control
    errorNonnegative errorSmall radiusSmall omegaLength strainBound hessianBound
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ scales.hessian := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (scales.location_pos _).le _)
  have radiusWeaker (index : Fin count) :
      scales.radius (index.val + 1) * (1 + error) ≤ scales.length (index.val + 1) / 32 := by
    linarith [radiusSmall index, scales.length_pos (index.val + 1)]
  have neutral (index : Fin count) := family.reference_centroidAsymmetry_bound scales densityEquation evolution
    horizonPositive finishNonnegative timeRange amplitudePositive frequencyBound ratioBound alphaPositive initial
    inside material differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation lengthSmall control radiusWeaker index
  have improvedNeutral (time : ℝ) (member : time ∈ Icc 0 finish) (index : Fin count) :
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
  have rateBound : 2400 * memory * scales.hessian + secondary * scales.strain ≤
      constant * (scales.strain + scales.hessian) := by
    have first := mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right secondaryNonnegative : 2400 * memory ≤ constant) hessianNonnegative
    have second := mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (by positivity : 0 ≤ 2400 * memory) : secondary ≤ constant) strainNonnegative
    exact (add_le_add first second).trans_eq (by ring)
  intro time member index
  let denominator := 2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2
  have denominatorPositive : 0 < denominator := by
    have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)
    have lengthPositive := scales.length_pos (index.val + 1)
    dsimp only [denominator]
    positivity
  have derivative (current : ℝ) (currentInside : current ∈ Icc 0 finish) :=
    (family.quadrupole_angularImpulse_hasDerivAt_external scales densityEquation (inside current currentInside)
      (material current currentInside) index).differentiableAt.hasDerivAt.div_const denominator
  have bound (current : ℝ) (currentInside : current ∈ Ico 0 finish) :
      ‖deriv (fun next => angularImpulse scales family.patchMotion next index) current / denominator‖ ≤
        constant * (scales.strain + scales.hessian) := by
    have closed : current ∈ Icc 0 finish := ⟨currentInside.1, currentInside.2.le⟩
    have locationBound : scales.location (index.val + 1) ≤ 1 := by
      have estimate := scales.location_antitone (Nat.zero_le (index.val + 1))
      simpa only [Scales.location_eq_inv_pow, pow_zero, inv_one] using estimate
    have lengthBound : scales.length (index.val + 1) ≤ 1 := by
      linarith [lengthSmall index, scales.location_pos (index.val + 1)]
    have pointwise := family.reference_angularImpulse_deriv_scale_bound scales densityEquation evolution
      (timeRange closed) amplitudePositive frequencyBound ratioBound alphaPositive (inside current closed)
      (material current closed) (differenceLower current closed) (differenceUpper current closed)
      (radialSmall current closed) (asymmetrySmall current closed) (centerSeparation current closed)
      lengthSmall (control current closed) errorNonnegative errorSmall radiusSmall index memoryNonnegative
      (improvedNeutral current closed index) (omegaLength index) lengthBound hessianBound
    change |deriv (fun next => angularImpulse scales family.patchMotion next index) current| ≤
      denominator * (2400 * memory * scales.hessian + secondary * scales.strain) at pointwise
    rw [Real.norm_eq_abs, abs_div, abs_of_pos denominatorPositive]
    apply (div_le_iff₀ denominatorPositive).mpr
    exact pointwise.trans ((mul_le_mul_of_nonneg_left rateBound denominatorPositive.le).trans_eq (mul_comm _ _))
  have estimate := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun current currentInside => (derivative current currentInside).hasDerivWithinAt) bound time member
  have initialImpulse := evolution.reference_initial_angularImpulse horizonPositive.le amplitudePositive frequencyPositive
    ratioPositive initial thresholdSmall index
  have initialNormalized : angularImpulse scales family.patchMotion 0 index / denominator = 1 := by
    rw [initialImpulse]
    exact div_self denominatorPositive.ne'
  rw [initialNormalized, sub_zero] at estimate
  exact (by simpa only [Real.norm_eq_abs] using estimate)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
