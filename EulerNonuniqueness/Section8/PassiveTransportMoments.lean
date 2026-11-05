import EulerNonuniqueness.General.StrongL2MovingPairing
import EulerNonuniqueness.General.VariableLinearLp
import EulerNonuniqueness.General.IntervalWeakDerivative
import EulerNonuniqueness.General.DerivativeFromIntervalFTC
import EulerNonuniqueness.Section8.ExpandingEulerSequence
import EulerNonuniqueness.Section8.SeparableTransport

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace EulerNonuniqueness

theorem ContinuousInLpOn.continuousOn_passiveTransportFlux
    {horizon : ℝ} {density : Evolution} {velocity : ℝ → Velocity}
    (densityContinuous : ContinuousInLpOn horizon 2 density)
    (velocityContinuous : ContinuousInLpOn horizon 2 velocity)
    {test : Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    ContinuousOn (fun time => ∫ position, density time position *
      fderiv ℝ test position (velocity time position)) (Icc 0 horizon) := by
  obtain ⟨operatorBound, operatorBounds⟩ :=
    (compact.fderiv ℝ).exists_bound_of_continuous (smooth.continuous_fderiv (by simp))
  obtain ⟨_, densityMembers, densityQuotient⟩ := densityContinuous
  obtain ⟨_, velocityMembers, velocityQuotient⟩ := velocityContinuous
  have testMembers (time : Icc (0 : ℝ) horizon) : MemLp
      (fun position => fderiv ℝ test position (velocity time position)) 2 volume :=
    (velocityMembers time).apply_bounded_continuousLinearMap
      (smooth.continuous_fderiv (by simp)).aestronglyMeasurable operatorBounds
  apply continuousOn_iff_continuous_restrict.mpr
  apply continuous_iff_continuousAt.mpr
  intro time
  apply tendsto_integral_mul_of_strongL2_strongL2 densityMembers testMembers
    (densityMembers time) (testMembers time)
  · exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ densityMembers _ (densityMembers time)).mp
      (densityQuotient.tendsto time)
  · apply tendsto_eLpNorm_apply_bounded_continuousLinearMap_sub operatorBounds
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ velocityMembers _ (velocityMembers time)).mp
      (velocityQuotient.tendsto time)

theorem ContinuousInLpOn.integrable_passiveTransportFlux
    {horizon : ℝ} {density : Evolution} {velocity : ℝ → Velocity}
    (densityContinuous : ContinuousInLpOn horizon 2 density)
    (velocityContinuous : ContinuousInLpOn horizon 2 velocity)
    {time : ℝ} (inside : time ∈ Icc 0 horizon)
    {test : Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Integrable (fun position => density time position * fderiv ℝ test position (velocity time position)) := by
  obtain ⟨operatorBound, operatorBounds⟩ :=
    (compact.fderiv ℝ).exists_bound_of_continuous (smooth.continuous_fderiv (by simp))
  obtain ⟨_, densityMembers, _⟩ := densityContinuous
  obtain ⟨_, velocityMembers, _⟩ := velocityContinuous
  have testMember := (velocityMembers ⟨time, inside⟩).apply_bounded_continuousLinearMap
    (smooth.continuous_fderiv (by simp)).aestronglyMeasurable operatorBounds
  have productMember : MemLp
      ((fun position => fderiv ℝ test position (velocity time position)) * density time) 1 volume :=
    (densityMembers ⟨time, inside⟩).mul testMember
  simpa only [Pi.mul_apply, mul_comm] using memLp_one_iff_integrable.mp productMember

theorem WeakTransportOn.passive_smooth_moment_sub_eq_intervalIntegral
    {horizon : ℝ} {initial : Vorticity} {density : Evolution} {velocity : ℝ → Velocity}
    (transport : WeakTransportOn horizon initial density velocity)
    (densityContinuous : ContinuousInLpOn horizon 2 density)
    (velocityContinuous : ContinuousInLpOn horizon 2 velocity)
    (horizonPositive : 0 < horizon) {test : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    {first second : ℝ} (firstInside : first ∈ Icc 0 horizon) (secondInside : second ∈ Icc 0 horizon) :
    (∫ position, density second position * test position) -
        (∫ position, density first position * test position) =
      ∫ time in first..second, ∫ position, density time position * fderiv ℝ test position (velocity time position) := by
  have testMember : MemLp test 2 volume := smooth.continuous.memLp_of_hasCompactSupport compact
  have weak := densityContinuous.weakL2ContinuousOn
  have momentContinuous : ContinuousOn (fun time => ∫ position, density time position * test position) (Icc 0 horizon) :=
    continuousOn_iff_continuous_restrict.mpr (weak.2 test testMember)
  have fluxContinuous := densityContinuous.continuousOn_passiveTransportFlux velocityContinuous smooth compact
  refine momentContinuous.sub_eq_intervalIntegral_of_weak_derivative_setIntegral
    fluxContinuous horizonPositive ?_ firstInside secondInside
  intro temporal temporalSmooth temporalCompact temporalSupport
  apply (transport.separableTest_identity temporalSmooth temporalCompact temporalSupport smooth compact ?_ ?_).2
  · intro time inside
    have productMember : MemLp (test * density time) 1 volume := (weak.1 time inside).mul testMember
    have integrable := memLp_one_iff_integrable.mp productMember
    change Integrable (fun position => test position * density time position) at integrable
    simpa only [mul_comm] using integrable
  · intro time inside
    exact densityContinuous.integrable_passiveTransportFlux velocityContinuous inside smooth compact

theorem WeakTransportOn.hasDerivAt_passive_smooth_moment
    {horizon : ℝ} {initial : Vorticity} {density : Evolution} {velocity : ℝ → Velocity}
    (transport : WeakTransportOn horizon initial density velocity)
    (densityContinuous : ContinuousInLpOn horizon 2 density)
    (velocityContinuous : ContinuousInLpOn horizon 2 velocity)
    (horizonPositive : 0 < horizon) {test : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    {time : ℝ} (inside : time ∈ Ioo 0 horizon) :
    HasDerivAt (fun current => ∫ position, density current position * test position)
      (∫ position, density time position * fderiv ℝ test position (velocity time position)) time := by
  apply hasDerivAt_of_sub_eq_intervalIntegral_on_Icc
    (function := fun current => ∫ position, density current position * test position)
    (densityContinuous.continuousOn_passiveTransportFlux velocityContinuous smooth compact) horizonPositive
    (fun current member => transport.passive_smooth_moment_sub_eq_intervalIntegral
      densityContinuous velocityContinuous horizonPositive smooth compact ⟨le_rfl, horizonPositive.le⟩ member) inside

end EulerNonuniqueness
