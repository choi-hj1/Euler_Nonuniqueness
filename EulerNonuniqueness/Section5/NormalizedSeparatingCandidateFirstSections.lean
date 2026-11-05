import EulerNonuniqueness.Section5.SeparatingCandidateFirstSection

noncomputable section

open Filter Set
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section2

theorem normalizedSeparatingCandidate_exists_with_first_sections :
    ∃ timeShift rotationPhase dipoleAngle : ℝ, ∃ offset : ℂ,
    let orbit := separatingCandidate timeShift rotationPhase dipoleAngle offset
    IsNormalizedSeparatingOrbit orbit ∧
      ∀ incoming radiusMin : ℝ, ∃ sectionTime : ℝ,
        max (incoming + 1) 0 < sectionTime ∧ radiusMin ≤ separationRadius orbit sectionTime ∧
        (∀ time ∈ Icc (sectionTime - 1) (sectionTime + 1),
          HasDerivAt (separationRadius orbit)
            (separatingRadiusScalarVelocity (separatingScalarOrbit 1 (by norm_num) (time + timeShift))) time ∧
          1 ≤ separatingRadiusScalarVelocity (separatingScalarOrbit 1 (by norm_num) (time + timeShift))) ∧
        ∀ time ≤ sectionTime - 1, separationRadius orbit time ≤ separationRadius orbit sectionTime - 1 := by
  obtain ⟨coefficient, coefficientPositive, unstableLimit⟩ := separatingUnstableShape_incoming_exponential 1 (by norm_num)
  obtain ⟨phaseLimit, phaseLimitProperty⟩ := separatingPhase_incoming_limit 1 (by norm_num)
  obtain ⟨dipoleAngle, offset, bound, boundPositive, timeMin, timePositive, scattering⟩ :=
    separating_scattering_asymptotics 1 (by norm_num)
  simp only [Complex.ofReal_one, mul_one] at scattering
  simp only [mul_one] at unstableLimit phaseLimitProperty
  let timeShift : ℝ := -Real.log coefficient / (2 * Real.sqrt 2)
  let rotationPhase : ℝ := timeShift - phaseLimit
  have timeAtBot : Filter.Tendsto (fun time : ℝ => time + timeShift) Filter.atBot Filter.atBot :=
    Filter.tendsto_atBot_add_const_right _ _ tendsto_id
  have timeAtTop : Filter.Tendsto (fun time : ℝ => time + timeShift) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _ tendsto_id
  have geometry := separatingCandidate_geometry timeShift rotationPhase dipoleAngle offset
  refine ⟨timeShift, rotationPhase, dipoleAngle, offset, ?_, ?_⟩
  · unfold IsNormalizedSeparatingOrbit
    refine ⟨geometry.1, ?_, geometry.2.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro time
      have geometryTime := geometry.2.1 time
      have equations := separatingCandidate_pointEquations timeShift rotationPhase dipoleAngle time offset
      exact ⟨geometryTime.1, geometryTime.2, equations.1, equations.2⟩
    · have result := (separating_radial_incoming_limit 1 (by norm_num)).comp timeAtBot
      convert result using 1
      funext time
      have norms := separatingCandidate_norms timeShift rotationPhase dipoleAngle time offset
      rw [norms.1, norms.2]
      rfl
    · have result := (separating_angle_incoming_limit 1 (by norm_num)).comp timeAtBot
      apply result.congr'
      apply Filter.Eventually.of_forall
      intro time
      change 2 * Complex.arg (separatingNegative 1 (by norm_num) (time + timeShift) /
        separatingPositive 1 (by norm_num) (time + timeShift)) = 2 * Complex.arg
        ((separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time /
          (separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time)
      rw [separatingCandidate_ratio, separating_position_ratio]
    · have result := (unstableLimit.comp timeAtBot).const_mul (Real.exp ((2 * Real.sqrt 2) * timeShift))
      have exponent : (2 * Real.sqrt 2) * timeShift = -Real.log coefficient := by
        dsimp only [timeShift]
        field_simp
        ring
      have normalizedConstant : Real.exp ((2 * Real.sqrt 2) * timeShift) * coefficient = 1 := by
        rw [exponent, Real.exp_neg, Real.exp_log coefficientPositive, inv_mul_cancel₀ coefficientPositive.ne']
      rw [normalizedConstant] at result
      apply result.congr'
      apply Filter.Eventually.of_forall
      intro time
      change Real.exp ((2 * Real.sqrt 2) * timeShift) *
        (Real.exp (-(2 * Real.sqrt 2) * (time + timeShift)) *
          separatingUnstableShape (separatingScalarOrbit 1 (by norm_num) (time + timeShift))) =
        Real.exp (-(2 * Real.sqrt 2) * time) *
          orbitUnstableShape (separatingCandidate timeShift rotationPhase dipoleAngle offset) time
      rw [(separatingCandidate_unstableStable timeShift rotationPhase dipoleAngle time offset).1]
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      congr 1
      ring
    · have result := (phaseLimitProperty.comp timeAtBot).add_const (rotationPhase - timeShift)
      convert result using 1
      · funext time
        dsimp only [separatingCandidate, Function.comp_def]
        ring
      · congr 1
        dsimp only [rotationPhase]
        ring
    · have result := (separatingStableShape_incoming_ratio 1 (by norm_num)).comp timeAtBot
      apply result.congr'
      apply Filter.Eventually.of_forall
      intro time
      change separatingStableShape (separatingScalarOrbit 1 (by norm_num) (time + timeShift)) /
        separatingUnstableShape (separatingScalarOrbit 1 (by norm_num) (time + timeShift)) =
        orbitStableShape (separatingCandidate timeShift rotationPhase dipoleAngle offset) time /
          orbitUnstableShape (separatingCandidate timeShift rotationPhase dipoleAngle offset) time
      rw [(separatingCandidate_unstableStable timeShift rotationPhase dipoleAngle time offset).1,
        (separatingCandidate_unstableStable timeShift rotationPhase dipoleAngle time offset).2]
    · have result := (separating_radial_outgoing_limit 1 (by norm_num)).comp timeAtTop
      convert result using 1
      funext time
      have norms := separatingCandidate_norms timeShift rotationPhase dipoleAngle time offset
      rw [norms.1, norms.2]
      rfl
    · have result := (separating_angle_outgoing_limit 1 (by norm_num)).comp timeAtTop
      apply result.congr'
      apply Filter.Eventually.of_forall
      intro time
      change 2 * Complex.arg (separatingNegative 1 (by norm_num) (time + timeShift) /
        separatingPositive 1 (by norm_num) (time + timeShift)) = 2 * Complex.arg
        ((separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time /
          (separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time)
      rw [separatingCandidate_ratio, separating_position_ratio]
    · exact separatingCandidate_scattering timeShift rotationPhase dipoleAngle offset boundPositive timePositive scattering
  · intro incoming radiusMin
    exact separatingCandidate_exists_first_section timeShift rotationPhase dipoleAngle offset incoming radiusMin

end EulerNonuniqueness.Paper
