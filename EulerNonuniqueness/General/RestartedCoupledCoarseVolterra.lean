import EulerNonuniqueness.General.RestartedExponentialVolterra

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

theorem coupled_coarse_volterra_on_subinterval
    {coordinate memory forcing memoryForcing : ℝ → ℝ}
    {constant omega epsilon rate start finish : ℝ}
    (coordinateContinuous : ContinuousOn coordinate (Icc start finish))
    (memoryContinuous : ContinuousOn memory (Icc start finish))
    (forcingContinuous : ContinuousOn forcing (Icc start finish))
    (memoryForcingContinuous : ContinuousOn memoryForcing (Icc start finish))
    (constantNonnegative : 0 ≤ constant) (omegaNonnegative : 0 ≤ omega)
    (epsilonNonnegative : 0 ≤ epsilon) (epsilonOne : epsilon ≤ 1)
    (rateNonnegative : 0 ≤ rate) (ordered : start ≤ finish)
    (coordinateNonnegative : ∀ time ∈ Icc start finish, 0 ≤ coordinate time)
    (memoryNonnegative : ∀ time ∈ Icc start finish, 0 ≤ memory time)
    (forcingNonnegative : ∀ time ∈ Icc start finish, 0 ≤ forcing time)
    (coordinateBound : ∀ time ∈ Icc start finish,
      coordinate time ≤ coordinate start + constant * ∫ current in start..time,
        omega * (coordinate current + epsilon * memory current) + forcing current)
    (memoryBound : ∀ time ∈ Icc start finish,
      memory time ≤ memory start * Real.exp (rate * (time - start)) +
        constant * ∫ current in start..time,
          Real.exp (rate * (time - current)) * (omega * coordinate current + memoryForcing current)) :
    ∀ time ∈ Icc start finish,
      IntervalIntegrable (fun current =>
        Real.exp ((rate + constant * (2 * omega)) * (time - current)) *
          (forcing current + memoryForcing current)) volume start time ∧
      coordinate time + memory time ≤
        (coordinate start + memory start) * Real.exp ((rate + constant * (2 * omega)) * (time - start)) +
        constant * ∫ current in start..time,
          Real.exp ((rate + constant * (2 * omega)) * (time - current)) *
            (forcing current + memoryForcing current) := by
  have coordinateIntegrandContinuous : ContinuousOn
      (fun current => omega * (coordinate current + epsilon * memory current) + forcing current)
      (Icc start finish) :=
    (continuousOn_const.mul (coordinateContinuous.add (continuousOn_const.mul memoryContinuous))).add forcingContinuous
  have memoryIntegrandContinuous : ContinuousOn
      (fun current => omega * coordinate current + memoryForcing current) (Icc start finish) :=
    (continuousOn_const.mul coordinateContinuous).add memoryForcingContinuous
  have combinedIntegrandContinuous : ContinuousOn
      (fun current => forcing current + memoryForcing current +
        (2 * omega) * (coordinate current + memory current)) (Icc start finish) :=
    (forcingContinuous.add memoryForcingContinuous).add
      (continuousOn_const.mul (coordinateContinuous.add memoryContinuous))
  have inequality (time : ℝ) (inside : time ∈ Icc start finish) :
      coordinate time + memory time ≤ (coordinate start + memory start) * Real.exp (rate * (time - start)) +
        constant * ∫ current in start..time, Real.exp (rate * (time - current)) *
          (forcing current + memoryForcing current + (2 * omega) * (coordinate current + memory current)) := by
    have prefixSubset : Icc start time ⊆ Icc start finish := Icc_subset_Icc le_rfl inside.2
    have kernelContinuous : Continuous (fun current : ℝ => Real.exp (rate * (time - current))) := by fun_prop
    have coordinateIntegrable :=
      (coordinateIntegrandContinuous.mono prefixSubset).intervalIntegrable_of_Icc (μ := volume) inside.1
    have coordinateKernelIntegrable :=
      (kernelContinuous.continuousOn.mul (coordinateIntegrandContinuous.mono prefixSubset)).intervalIntegrable_of_Icc
        (μ := volume) inside.1
    have memoryKernelIntegrable :=
      (kernelContinuous.continuousOn.mul (memoryIntegrandContinuous.mono prefixSubset)).intervalIntegrable_of_Icc
        (μ := volume) inside.1
    have combinedKernelIntegrable :=
      (kernelContinuous.continuousOn.mul (combinedIntegrandContinuous.mono prefixSubset)).intervalIntegrable_of_Icc
        (μ := volume) inside.1
    have coordinateComparison := intervalIntegral.integral_mono_on inside.1
      coordinateIntegrable coordinateKernelIntegrable (by
        intro current member
        have integrandNonnegative : 0 ≤ omega * (coordinate current + epsilon * memory current) + forcing current :=
          add_nonneg (mul_nonneg omegaNonnegative (add_nonneg (coordinateNonnegative current (prefixSubset member))
            (mul_nonneg epsilonNonnegative (memoryNonnegative current (prefixSubset member)))))
            (forcingNonnegative current (prefixSubset member))
        have kernelOne : 1 ≤ Real.exp (rate * (time - current)) :=
          Real.one_le_exp_iff.mpr (mul_nonneg rateNonnegative (sub_nonneg.mpr member.2))
        simpa only [one_mul] using mul_le_mul_of_nonneg_right kernelOne integrandNonnegative)
    have initialComparison : coordinate start ≤ coordinate start * Real.exp (rate * (time - start)) := by
      have kernelOne : 1 ≤ Real.exp (rate * (time - start)) :=
        Real.one_le_exp_iff.mpr (mul_nonneg rateNonnegative (sub_nonneg.mpr inside.1))
      simpa only [mul_one] using mul_le_mul_of_nonneg_left kernelOne
        (coordinateNonnegative start ⟨le_rfl, ordered⟩)
    have enlargedCoordinate := (coordinateBound time inside).trans
      (add_le_add initialComparison (mul_le_mul_of_nonneg_left coordinateComparison constantNonnegative))
    have sumBound := add_le_add enlargedCoordinate (memoryBound time inside)
    have integralIdentity :
        (coordinate start * Real.exp (rate * (time - start)) +
          constant * ∫ current in start..time, Real.exp (rate * (time - current)) *
            (omega * (coordinate current + epsilon * memory current) + forcing current)) +
        (memory start * Real.exp (rate * (time - start)) +
          constant * ∫ current in start..time, Real.exp (rate * (time - current)) *
            (omega * coordinate current + memoryForcing current)) =
        (coordinate start + memory start) * Real.exp (rate * (time - start)) +
          constant * ∫ current in start..time,
            (Real.exp (rate * (time - current)) *
              (omega * (coordinate current + epsilon * memory current) + forcing current) +
            Real.exp (rate * (time - current)) * (omega * coordinate current + memoryForcing current)) := by
      rw [intervalIntegral.integral_add coordinateKernelIntegrable memoryKernelIntegrable]
      ring
    rw [integralIdentity] at sumBound
    have combinedComparison := intervalIntegral.integral_mono_on inside.1
      (coordinateKernelIntegrable.add memoryKernelIntegrable) combinedKernelIntegrable (by
        intro current member
        have epsilonMemory : epsilon * memory current ≤ memory current :=
          mul_le_of_le_one_left (memoryNonnegative current (prefixSubset member)) epsilonOne
        have scaled := mul_le_mul_of_nonneg_left epsilonMemory omegaNonnegative
        have slack := mul_nonneg omegaNonnegative (memoryNonnegative current (prefixSubset member))
        have point : (omega * (coordinate current + epsilon * memory current) + forcing current) +
            (omega * coordinate current + memoryForcing current) ≤
            forcing current + memoryForcing current + (2 * omega) * (coordinate current + memory current) := by
          nlinarith only [scaled, slack]
        simpa only [mul_add] using mul_le_mul_of_nonneg_left point (Real.exp_pos (rate * (time - current))).le)
    exact sumBound.trans (add_le_add_left
      (mul_le_mul_of_nonneg_left combinedComparison constantNonnegative) _)
  have resolved := EulerNonuniqueness.exponential_volterra_gronwall_on_Icc
    (trajectory := fun time => coordinate time + memory time)
    (forcing := fun time => forcing time + memoryForcing time)
    (initial := coordinate start + memory start) (rate := rate) (feedback := 2 * omega) (multiplier := constant)
    (coordinateContinuous.add memoryContinuous) (forcingContinuous.add memoryForcingContinuous)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) omegaNonnegative) constantNonnegative ordered inequality
  intro time inside
  exact ⟨(resolved time inside).2.1, (resolved time inside).2.2⟩

end EulerNonuniqueness.General
