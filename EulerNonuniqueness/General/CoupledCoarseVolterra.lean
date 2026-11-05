import EulerNonuniqueness.General.ExponentialVolterra

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

theorem coupled_coarse_volterra_on_Icc
    {coordinate raw forcing rawForcing : ℝ → ℝ} {constant omega epsilon rate horizon : ℝ}
    (coordinateContinuous : ContinuousOn coordinate (Icc 0 horizon))
    (rawContinuous : ContinuousOn raw (Icc 0 horizon))
    (forcingContinuous : ContinuousOn forcing (Icc 0 horizon))
    (rawForcingContinuous : ContinuousOn rawForcing (Icc 0 horizon))
    (constantNonnegative : 0 ≤ constant) (omegaOne : 1 ≤ omega)
    (epsilonNonnegative : 0 ≤ epsilon) (epsilonOne : epsilon ≤ 1)
    (rateNonnegative : 0 ≤ rate) (rateOne : rate ≤ 1) (horizonNonnegative : 0 ≤ horizon)
    (coordinateNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ coordinate time)
    (rawNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ raw time)
    (forcingNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ forcing time)
    (rawForcingNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ rawForcing time)
    (coordinateBound : ∀ time ∈ Icc 0 horizon,
      coordinate time ≤ constant * ∫ current in (0 : ℝ)..time,
        omega * (coordinate current + epsilon * raw current) + forcing current)
    (rawBound : ∀ time ∈ Icc 0 horizon,
      raw time ≤ constant * ∫ current in (0 : ℝ)..time,
        Real.exp (rate * (time - current)) * (omega * coordinate current + rawForcing current)) :
    ∀ time ∈ Icc 0 horizon,
      coordinate time + raw time ≤ (1 + 2 * constant) * ∫ current in (0 : ℝ)..time,
        Real.exp ((1 + 2 * constant) * omega * (time - current)) * (forcing current + rawForcing current) := by
  have omegaNonnegative : 0 ≤ omega := zero_le_one.trans omegaOne
  have coordinateIntegrandContinuous : ContinuousOn
      (fun current => omega * (coordinate current + epsilon * raw current) + forcing current) (Icc 0 horizon) :=
    (continuousOn_const.mul (coordinateContinuous.add (continuousOn_const.mul rawContinuous))).add forcingContinuous
  have rawIntegrandContinuous : ContinuousOn
      (fun current => omega * coordinate current + rawForcing current) (Icc 0 horizon) :=
    (continuousOn_const.mul coordinateContinuous).add rawForcingContinuous
  have combinedIntegrandContinuous : ContinuousOn
      (fun current => forcing current + rawForcing current + (2 * omega) * (coordinate current + raw current)) (Icc 0 horizon) :=
    (forcingContinuous.add rawForcingContinuous).add (continuousOn_const.mul (coordinateContinuous.add rawContinuous))
  have inequality (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      coordinate time + raw time ≤ (0 : ℝ) * Real.exp (rate * time) +
        constant * ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) *
          (forcing current + rawForcing current + (2 * omega) * (coordinate current + raw current)) := by
    have prefixSubset : Icc (0 : ℝ) time ⊆ Icc 0 horizon := Icc_subset_Icc le_rfl inside.2
    have kernelContinuous : Continuous (fun current : ℝ => Real.exp (rate * (time - current))) := by fun_prop
    have coordinateIntegrable := (coordinateIntegrandContinuous.mono prefixSubset).intervalIntegrable_of_Icc (μ := volume) inside.1
    have coordinateKernelIntegrable :=
      (kernelContinuous.continuousOn.mul (coordinateIntegrandContinuous.mono prefixSubset)).intervalIntegrable_of_Icc (μ := volume) inside.1
    have rawKernelIntegrable :=
      (kernelContinuous.continuousOn.mul (rawIntegrandContinuous.mono prefixSubset)).intervalIntegrable_of_Icc (μ := volume) inside.1
    have combinedKernelIntegrable :=
      (kernelContinuous.continuousOn.mul (combinedIntegrandContinuous.mono prefixSubset)).intervalIntegrable_of_Icc (μ := volume) inside.1
    have coordinateComparison := intervalIntegral.integral_mono_on inside.1 coordinateIntegrable coordinateKernelIntegrable (by
      intro current member
      have integrandNonnegative : 0 ≤ omega * (coordinate current + epsilon * raw current) + forcing current :=
        add_nonneg (mul_nonneg omegaNonnegative (add_nonneg (coordinateNonnegative current (prefixSubset member))
          (mul_nonneg epsilonNonnegative (rawNonnegative current (prefixSubset member)))))
          (forcingNonnegative current (prefixSubset member))
      have kernelOne : 1 ≤ Real.exp (rate * (time - current)) :=
        Real.one_le_exp_iff.mpr (mul_nonneg rateNonnegative (sub_nonneg.mpr member.2))
      exact (by simpa only [one_mul] using mul_le_mul_of_nonneg_right kernelOne integrandNonnegative))
    have enlargedCoordinate := (coordinateBound time inside).trans
      (mul_le_mul_of_nonneg_left coordinateComparison constantNonnegative)
    have sumBound := add_le_add enlargedCoordinate (rawBound time inside)
    rw [← mul_add, ← intervalIntegral.integral_add coordinateKernelIntegrable rawKernelIntegrable] at sumBound
    have combinedComparison := intervalIntegral.integral_mono_on inside.1
      (coordinateKernelIntegrable.add rawKernelIntegrable) combinedKernelIntegrable (by
        intro current member
        have epsilonRaw : epsilon * raw current ≤ raw current :=
          mul_le_of_le_one_left (rawNonnegative current (prefixSubset member)) epsilonOne
        have scaled := mul_le_mul_of_nonneg_left epsilonRaw omegaNonnegative
        have slack := mul_nonneg omegaNonnegative (rawNonnegative current (prefixSubset member))
        have point : (omega * (coordinate current + epsilon * raw current) + forcing current) +
            (omega * coordinate current + rawForcing current) ≤
            forcing current + rawForcing current + (2 * omega) * (coordinate current + raw current) := by
          nlinarith only [scaled, slack]
        simpa only [mul_add] using mul_le_mul_of_nonneg_left point (Real.exp_pos (rate * (time - current))).le)
    simpa only [zero_mul, zero_add] using
      sumBound.trans (mul_le_mul_of_nonneg_left combinedComparison constantNonnegative)
  have resolved := EulerNonuniqueness.exponential_volterra_gronwall
    (trajectory := fun time => coordinate time + raw time) (forcing := fun time => forcing time + rawForcing time)
    (initial := 0) (rate := rate) (feedback := 2 * omega) (multiplier := constant)
    (coordinateContinuous.add rawContinuous) (forcingContinuous.add rawForcingContinuous)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) omegaNonnegative) constantNonnegative horizonNonnegative inequality
  simp only [zero_mul, zero_add] at resolved
  have rateBound : rate + constant * (2 * omega) ≤ (1 + 2 * constant) * omega := by
    have actual : rate ≤ omega := rateOne.trans omegaOne
    nlinarith only [actual]
  have constantBound : constant ≤ 1 + 2 * constant := by linarith only [constantNonnegative]
  intro time inside
  have prefixSubset : Icc (0 : ℝ) time ⊆ Icc 0 horizon := Icc_subset_Icc le_rfl inside.2
  have originalKernelContinuous : Continuous (fun current : ℝ => Real.exp ((rate + constant * (2 * omega)) * (time - current))) := by fun_prop
  have coarseKernelContinuous : Continuous (fun current : ℝ => Real.exp ((1 + 2 * constant) * omega * (time - current))) := by fun_prop
  have forcingOn := (forcingContinuous.add rawForcingContinuous).mono prefixSubset
  have originalIntegrable := (originalKernelContinuous.continuousOn.mul forcingOn).intervalIntegrable_of_Icc (μ := volume) inside.1
  have coarseIntegrable := (coarseKernelContinuous.continuousOn.mul forcingOn).intervalIntegrable_of_Icc (μ := volume) inside.1
  have rateComparison := intervalIntegral.integral_mono_on inside.1 originalIntegrable coarseIntegrable (by
    intro current member
    have exponentialBound := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right rateBound (sub_nonneg.mpr member.2))
    exact mul_le_mul_of_nonneg_right exponentialBound
      (add_nonneg (forcingNonnegative current (prefixSubset member)) (rawForcingNonnegative current (prefixSubset member))))
  have coarseNonnegative : 0 ≤ ∫ current in (0 : ℝ)..time,
      Real.exp ((1 + 2 * constant) * omega * (time - current)) * (forcing current + rawForcing current) :=
    intervalIntegral.integral_nonneg inside.1 (fun current member => mul_nonneg (Real.exp_pos _).le
      (add_nonneg (forcingNonnegative current (prefixSubset member)) (rawForcingNonnegative current (prefixSubset member))))
  exact ((resolved time inside).trans (mul_le_mul_of_nonneg_left rateComparison constantNonnegative)).trans
    (mul_le_mul_of_nonneg_right constantBound coarseNonnegative)

end EulerNonuniqueness.General
