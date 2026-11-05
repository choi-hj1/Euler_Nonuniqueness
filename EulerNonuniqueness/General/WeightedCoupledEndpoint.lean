import Mathlib

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

theorem coupled_endpoint_le_of_weighted_response
    {coordinate memory forcing memoryForcing shape : ℝ → ℝ}
    {constant shapeConstant forcingConstant omega epsilon rate weight start finish : ℝ}
    (coordinateContinuous : ContinuousOn coordinate (Icc start finish))
    (memoryContinuous : ContinuousOn memory (Icc start finish))
    (forcingContinuous : ContinuousOn forcing (Icc start finish))
    (memoryForcingContinuous : ContinuousOn memoryForcing (Icc start finish))
    (shapeContinuous : ContinuousOn shape (Icc start finish))
    (constantNonnegative : 0 ≤ constant) (forcingConstantNonnegative : 0 ≤ forcingConstant)
    (omegaNonnegative : 0 ≤ omega) (omegaWeight : omega ≤ weight)
    (epsilonNonnegative : 0 ≤ epsilon) (epsilonOne : epsilon ≤ 1)
    (weightPositive : 0 < weight) (rateWeight : rate ≤ weight) (ordered : start ≤ finish)
    (coordinateNonnegative : ∀ time ∈ Icc start finish, 0 ≤ coordinate time)
    (memoryNonnegative : ∀ time ∈ Icc start finish, 0 ≤ memory time)
    (forcingNonnegative : ∀ time ∈ Icc start finish, 0 ≤ forcing time)
    (memoryForcingNonnegative : ∀ time ∈ Icc start finish, 0 ≤ memoryForcing time)
    (coordinateBound : coordinate finish ≤ coordinate start + constant * ∫ current in start..finish,
      omega * (coordinate current + epsilon * memory current) + forcing current)
    (memoryBound : memory finish ≤ memory start * Real.exp (rate * (finish - start)) +
      constant * ∫ current in start..finish,
        Real.exp (rate * (finish - current)) * (omega * coordinate current + memoryForcing current))
    (weightedResponse :
      (∫ current in start..finish, Real.exp (-weight * (current - start)) * (coordinate current + memory current)) ≤
        shapeConstant * (∫ current in start..finish, Real.exp (-weight * (current - start)) * shape current) +
        (forcingConstant / weight) * ∫ current in start..finish,
          Real.exp (-weight * (current - start)) * (forcing current + memoryForcing current)) :
    IntervalIntegrable (fun current => Real.exp (-weight * (current - start)) * shape current) volume start finish ∧
    coordinate finish + memory finish ≤ Real.exp (weight * (finish - start)) *
      (coordinate start + memory start +
        (2 * constant * omega * shapeConstant) *
          (∫ current in start..finish, Real.exp (-weight * (current - start)) * shape current) +
        (constant * (1 + 2 * forcingConstant)) *
          ∫ current in start..finish, Real.exp (-weight * (current - start)) *
            (forcing current + memoryForcing current)) := by
  have weightContinuous : Continuous (fun current : ℝ => Real.exp (-weight * (current - start))) := by fun_prop
  refine ⟨(weightContinuous.continuousOn.mul shapeContinuous).intervalIntegrable_of_Icc (μ := volume) ordered, ?_⟩
  let kernel := fun current => Real.exp (weight * (finish - current))
  let coordinateInput := fun current => omega * (coordinate current + epsilon * memory current) + forcing current
  let memoryInput := fun current => omega * coordinate current + memoryForcing current
  let combinedInput := fun current => forcing current + memoryForcing current +
    (2 * omega) * (coordinate current + memory current)
  have kernelContinuous : Continuous kernel := by dsimp only [kernel]; fun_prop
  have coordinateInputContinuous : ContinuousOn coordinateInput (Icc start finish) :=
    (continuousOn_const.mul (coordinateContinuous.add (continuousOn_const.mul memoryContinuous))).add forcingContinuous
  have memoryInputContinuous : ContinuousOn memoryInput (Icc start finish) :=
    (continuousOn_const.mul coordinateContinuous).add memoryForcingContinuous
  have combinedInputContinuous : ContinuousOn combinedInput (Icc start finish) :=
    (forcingContinuous.add memoryForcingContinuous).add
      (continuousOn_const.mul (coordinateContinuous.add memoryContinuous))
  have coordinateComparison := intervalIntegral.integral_mono_on ordered
    (coordinateInputContinuous.intervalIntegrable_of_Icc (μ := volume) ordered)
    ((kernelContinuous.continuousOn.mul coordinateInputContinuous).intervalIntegrable_of_Icc (μ := volume) ordered) (by
      intro current inside
      have inputNonnegative : 0 ≤ coordinateInput current :=
        add_nonneg (mul_nonneg omegaNonnegative (add_nonneg (coordinateNonnegative current inside)
          (mul_nonneg epsilonNonnegative (memoryNonnegative current inside)))) (forcingNonnegative current inside)
      have kernelOne : 1 ≤ kernel current := Real.one_le_exp_iff.mpr
        (mul_nonneg weightPositive.le (sub_nonneg.mpr inside.2))
      simpa only [one_mul] using mul_le_mul_of_nonneg_right kernelOne inputNonnegative)
  have oldKernelContinuous : Continuous (fun current : ℝ => Real.exp (rate * (finish - current))) := by fun_prop
  have memoryComparison := intervalIntegral.integral_mono_on ordered
    ((oldKernelContinuous.continuousOn.mul memoryInputContinuous).intervalIntegrable_of_Icc (μ := volume) ordered)
    ((kernelContinuous.continuousOn.mul memoryInputContinuous).intervalIntegrable_of_Icc (μ := volume) ordered) (by
      intro current inside
      exact mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right rateWeight (sub_nonneg.mpr inside.2)))
        (add_nonneg (mul_nonneg omegaNonnegative (coordinateNonnegative current inside)) (memoryForcingNonnegative current inside)))
  have initialCoordinate : coordinate start ≤ coordinate start * Real.exp (weight * (finish - start)) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.one_le_exp_iff.mpr (mul_nonneg weightPositive.le (sub_nonneg.mpr ordered)))
      (coordinateNonnegative start ⟨le_rfl, ordered⟩)
  have initialMemory : memory start * Real.exp (rate * (finish - start)) ≤
      memory start * Real.exp (weight * (finish - start)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right rateWeight (sub_nonneg.mpr ordered))) (memoryNonnegative start ⟨le_rfl, ordered⟩)
  have combinedComparison := intervalIntegral.integral_mono_on ordered
    ((kernelContinuous.continuousOn.mul coordinateInputContinuous).intervalIntegrable_of_Icc (μ := volume) ordered |>.add
      ((kernelContinuous.continuousOn.mul memoryInputContinuous).intervalIntegrable_of_Icc (μ := volume) ordered))
    ((kernelContinuous.continuousOn.mul combinedInputContinuous).intervalIntegrable_of_Icc (μ := volume) ordered) (by
      intro current inside
      have bounded := mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (memoryNonnegative current inside) epsilonOne) omegaNonnegative
      have slack := mul_nonneg omegaNonnegative (memoryNonnegative current inside)
      have point : coordinateInput current + memoryInput current ≤ combinedInput current := by
        dsimp only [coordinateInput, memoryInput, combinedInput]
        nlinarith only [bounded, slack]
      simpa only [mul_add] using mul_le_mul_of_nonneg_left point (Real.exp_pos (weight * (finish - current))).le)
  have coordinateKernelI := (kernelContinuous.continuousOn.mul coordinateInputContinuous).intervalIntegrable_of_Icc (μ := volume) ordered
  have memoryKernelI := (kernelContinuous.continuousOn.mul memoryInputContinuous).intervalIntegrable_of_Icc (μ := volume) ordered
  have joined := add_le_add
    (coordinateBound.trans (add_le_add initialCoordinate (mul_le_mul_of_nonneg_left coordinateComparison constantNonnegative)))
    (memoryBound.trans (add_le_add initialMemory (mul_le_mul_of_nonneg_left memoryComparison constantNonnegative)))
  have joinedBound : coordinate finish + memory finish ≤
      (coordinate start + memory start) * Real.exp (weight * (finish - start)) +
        constant * ∫ current in start..finish, kernel current * combinedInput current := by
    have integralJoined :
        (∫ current in start..finish, kernel current * coordinateInput current) +
        (∫ current in start..finish, kernel current * memoryInput current) ≤
        ∫ current in start..finish, kernel current * combinedInput current := by
      rw [← intervalIntegral.integral_add coordinateKernelI memoryKernelI]
      exact combinedComparison
    have scaled := mul_le_mul_of_nonneg_left integralJoined constantNonnegative
    dsimp only [coordinateInput, memoryInput] at joined
    nlinarith only [joined, scaled]
  let weighted := fun function : ℝ → ℝ => ∫ current in start..finish,
    Real.exp (-weight * (current - start)) * function current
  have weightedContinuous : Continuous (fun current : ℝ => Real.exp (-weight * (current - start))) := by fun_prop
  have forceI := (weightedContinuous.continuousOn.mul (forcingContinuous.add memoryForcingContinuous)).intervalIntegrable_of_Icc (μ := volume) ordered
  have stateI := (weightedContinuous.continuousOn.mul (coordinateContinuous.add memoryContinuous)).intervalIntegrable_of_Icc (μ := volume) ordered
  have identity : (∫ current in start..finish, kernel current * combinedInput current) =
      Real.exp (weight * (finish - start)) *
        (weighted (fun current => forcing current + memoryForcing current) +
          (2 * omega) * weighted (fun current => coordinate current + memory current)) := by
    rw [← intervalIntegral.integral_const_mul]
    have kernelIdentity (current : ℝ) : kernel current =
        Real.exp (weight * (finish - start)) * Real.exp (-weight * (current - start)) := by
      dsimp only [kernel]
      rw [← Real.exp_add]
      congr 1
      ring
    simp_rw [kernelIdentity]
    rw [← intervalIntegral.integral_add forceI (stateI.const_mul (2 * omega))]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro current _
    dsimp only [combinedInput]
    ring
  have forceNonnegative : 0 ≤ weighted (fun current => forcing current + memoryForcing current) :=
    intervalIntegral.integral_nonneg ordered (fun current inside => mul_nonneg (Real.exp_pos _).le
      (add_nonneg (forcingNonnegative current inside) (memoryForcingNonnegative current inside)))
  have ratioBound : omega / weight ≤ 1 := (div_le_one weightPositive).mpr omegaWeight
  have forceComparison : (2 * omega) * (forcingConstant / weight) *
      weighted (fun current => forcing current + memoryForcing current) ≤
        (2 * forcingConstant) * weighted (fun current => forcing current + memoryForcing current) := by
    have scaled := mul_le_mul_of_nonneg_right ratioBound
      (mul_nonneg (show 0 ≤ 2 * forcingConstant by positivity) forceNonnegative)
    convert scaled using 1 <;> ring
  have weightedScaled := mul_le_mul_of_nonneg_left weightedResponse
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) omegaNonnegative)
  rw [identity] at joinedBound
  have interior :
      constant * (weighted (fun current => forcing current + memoryForcing current) +
        (2 * omega) * weighted (fun current => coordinate current + memory current)) ≤
      (2 * constant * omega * shapeConstant) * weighted shape +
        (constant * (1 + 2 * forcingConstant)) * weighted (fun current => forcing current + memoryForcing current) := by
    have scaled := mul_le_mul_of_nonneg_left weightedScaled constantNonnegative
    have scaledForce := mul_le_mul_of_nonneg_left forceComparison constantNonnegative
    nlinarith only [scaled, scaledForce]
  have finalComparison := mul_le_mul_of_nonneg_left interior (Real.exp_pos (weight * (finish - start))).le
  dsimp only [weighted] at finalComparison
  nlinarith only [joinedBound, finalComparison]

end EulerNonuniqueness.General
