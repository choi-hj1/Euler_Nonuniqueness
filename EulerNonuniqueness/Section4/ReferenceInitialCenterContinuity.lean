import EulerNonuniqueness.Section4.InitialDiskUniformBounds

noncomputable section

namespace EulerNonuniqueness.Paper

theorem initialDiskCenter_continuous_of_unstable_bound
    {Parameter : Type*} [TopologicalSpace Parameter]
    (scales : Scales) (index : ℕ) (phase : ℝ) (patch : Fin 4)
    (unstable : Parameter → ℝ) (unstableContinuous : Continuous unstable)
    (small : ∀ parameter, |unstable parameter| ≤ 1) :
    Continuous (fun parameter => initialDiskCenter scales index phase (unstable parameter) patch) := by
  have denominatorContinuous : Continuous (fun parameter => Real.sqrt (1 - rhombusRatio * (1 + unstable parameter))) := by
    fun_prop
  have denominatorNonzero : ∀ parameter, Real.sqrt (1 - rhombusRatio * (1 + unstable parameter)) ≠ 0 := by
    intro parameter
    have bound := initialDiagonal_denominator_bound (small parameter)
    linarith
  have positiveContinuous : Continuous (fun parameter => initialPositiveDiagonal scales index phase (unstable parameter)) := by
    unfold initialPositiveDiagonal
    exact continuous_const.div (Complex.continuous_ofReal.comp denominatorContinuous)
      (fun parameter => Complex.ofReal_ne_zero.mpr (denominatorNonzero parameter))
  have amplitudeContinuous : Continuous (fun parameter => scales.length index * Real.sqrt (rhombusRatio * (1 + unstable parameter)) /
      Real.sqrt (1 - rhombusRatio * (1 + unstable parameter))) := by
    apply Continuous.div _ denominatorContinuous denominatorNonzero
    fun_prop
  have exponentialContinuous : Continuous (fun parameter =>
      Complex.exp (Complex.I * (phase + Real.pi / 2 + unstable parameter / Real.sqrt 2 : ℝ))) := by
    fun_prop
  have negativeContinuous : Continuous (fun parameter => initialNegativeDiagonal scales index phase (unstable parameter)) :=
    (Complex.continuous_ofReal.comp amplitudeContinuous).mul exponentialContinuous
  unfold initialDiskCenter
  split_ifs
  · exact continuous_const.add positiveContinuous
  · exact continuous_const.add positiveContinuous.neg
  · exact continuous_const.add negativeContinuous
  · exact continuous_const.add negativeContinuous.neg

end EulerNonuniqueness.Paper
