import EulerNonuniqueness.Section5.CascadeBlockExtentRate
import EulerNonuniqueness.Section3.MovingCentroidGaugeEuler

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

theorem blockExtentVector_lt_of_monitored_material_prefix {count : ℕ}
    {configuration : FiniteContourConfiguration (count * 4)}
    {centerBound shapeRadius cutoffGap margin backwardHorizon forwardHorizon : ℝ}
    {initial : MovingContourState (count * 4)}
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius cutoffGap margin
      backwardHorizon forwardHorizon initial) (scales : Scales)
    (densities : ∀ index patch, configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (radii : ∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1))
    (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {horizon : ℝ} (horizonNonnegative : 0 ≤ horizon) (horizonBound : horizon ≤ 1)
    (beforeFinal : horizon < forwardHorizon) (marginPositive : 0 < margin)
    (safe : ∀ time ∈ Icc 0 horizon, margin ≤ infDist (trajectory.curve time)
      (configuration.movingStateAdmissible centerBound shapeRadius cutoffGap)ᶜ)
    {factor : ℝ} (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (internal : ∀ time ∈ Icc 0 horizon, ∀ receiver source,
      cascadeInternalGapMonitor scales factor receiver source (trajectory.movingFamily.cascadeCenters time) ≤ 0)
    (extent : ∀ time ∈ Icc 0 horizon, ∀ label,
      cascadeExtentMonitor scales label (trajectory.movingFamily.cascadeCenters time) ≤ 0)
    (lower : ∀ time ∈ Icc 0 horizon, ∀ receiver source,
      cascadeAnchorLowerMonitor scales receiver source (trajectory.movingFamily.cascadeCenters time) ≤ 0)
    (radiusInternal : ∀ index : Fin count, scales.radius (index.val + 1) ≤ factor * scales.length (index.val + 1) / 1000)
    (radiusLocation : ∀ index : Fin count, scales.radius (index.val + 1) ≤ factor * scales.location (index.val + 1) / 1000)
    (control : ∀ time ∈ Icc 0 horizon, ∀ index patch,
      BoundaryCloseToCircle scales trajectory.movingFamily.patchMotion time index patch (1 / 16))
    (initialExtent : ∀ index : Fin count, ‖trajectory.blockExtentVector index 0‖ ≤ scales.location (index.val + 1) / 200)
    (rateBudget : (4 / Real.pi) * (24 / factor) ^ 2 * scales.strain ≤ Real.log (4 / 3))
    (forcingBudget : ∀ index : Fin count,
      10 * scales.omega (index.val + 1) * scales.length (index.val + 1) / factor +
        (512 / Real.pi) * (24 / factor) ^ 3 * scales.radius (index.val + 1) ^ 2 * scales.hessian ≤
          scales.location (index.val + 1) / 1000) :
    ∀ time ∈ Icc 0 horizon, ∀ index : Fin count,
      ‖trajectory.blockExtentVector index time‖ < scales.location (index.val + 1) / 100 := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ scales.hessian := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (scales.location_pos _).le _)
  have globalInside (time : ℝ) (inside : time ∈ Icc 0 horizon) : time ∈ Ioo (-backwardHorizon) forwardHorizon :=
    ⟨by linarith [trajectory.backward_positive, inside.1], inside.2.trans_lt beforeFinal⟩
  have evolution := trajectory.finitePatchEvolution_of_margin scales densities radii initialCircles
    marginPositive horizonNonnegative beforeFinal safe
  have fieldIdentity := trajectory.movingFamily.patchVorticity_eq scales densities
  have material (time : ℝ) (inside : time ∈ Icc 0 horizon) (patch : Fin (count * 4)) (label : ℝ) :
      (trajectory.movingFamily.patch patch).boundaryVelocity time label =
        biotSavart (Paper.patchVorticity scales trajectory.movingFamily.patchMotion time)
          ((trajectory.movingFamily.patch patch).boundary time label) := by
    rw [fieldIdentity]
    exact trajectory.movingFamily_material_equation_of_margin marginPositive (globalInside time inside) (safe time inside) patch label
  intro time inside index
  have locationPositive := scales.location_pos (index.val + 1)
  by_cases horizonZero : horizon = 0
  · have timeZero : time = 0 := by linarith [inside.1, inside.2]
    rw [timeZero]
    exact (initialExtent index).trans_lt (by linarith)
  have horizonPositive : 0 < horizon := lt_of_le_of_ne horizonNonnegative (Ne.symm horizonZero)
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have lengthPositive := scales.length_pos (index.val + 1)
  have rates := trajectory.blockExtentVector_gronwall index horizonPositive
    (by positivity) (by positivity)
    (fun current member => trajectory.blockExtentVelocity_bound_of_monitors scales radii initialCircles
      evolution ⟨member.1.le, member.2.le⟩ (globalInside current ⟨member.1.le, member.2.le⟩)
      amplitudePositive frequencyBound ratioBound alphaPositive (material current ⟨member.1.le, member.2.le⟩)
      factorPositive factorSmall (internal current ⟨member.1.le, member.2.le⟩)
      (extent current ⟨member.1.le, member.2.le⟩) (lower current ⟨member.1.le, member.2.le⟩)
      radiusInternal radiusLocation (control current ⟨member.1.le, member.2.le⟩) index)
  have timeOne : time ≤ 1 := inside.2.trans horizonBound
  have rateNonnegative : 0 ≤ (4 / Real.pi) * (24 / factor) ^ 2 * scales.strain := by positivity
  have exponent : ((4 / Real.pi) * (24 / factor) ^ 2 * scales.strain) * time ≤ Real.log (4 / 3) :=
    (mul_le_of_le_one_right rateNonnegative timeOne).trans rateBudget
  have exponential : Real.exp (((4 / Real.pi) * (24 / factor) ^ 2 * scales.strain) * time) ≤ 4 / 3 := by
    exact (Real.exp_le_exp.mpr exponent).trans_eq (Real.exp_log (by norm_num))
  have forcingNonnegative : 0 ≤ 10 * scales.omega (index.val + 1) * scales.length (index.val + 1) / factor +
      (512 / Real.pi) * (24 / factor) ^ 3 * scales.radius (index.val + 1) ^ 2 * scales.hessian := by positivity
  have forcingTime := (mul_le_of_le_one_right forcingNonnegative timeOne).trans (forcingBudget index)
  have prefactor := add_le_add (initialExtent index) forcingTime
  have finalBound := (rates time inside).trans
    (mul_le_mul prefactor exponential (Real.exp_pos _).le (by positivity))
  nlinarith

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
