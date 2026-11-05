import EulerNonuniqueness.General.BilinearOperatorCalculus

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem linearGroup_generator_commute
    (group : ℝ → Space →L[ℝ] Space) (generator : Space →L[ℝ] Space)
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (actualDerivative : ∀ time : ℝ, HasDerivAt group ((group time).comp generator) time)
    (time : ℝ) : generator.comp (group time) = (group time).comp generator := by
  have firstDerivative := (actualDerivative 0).clm_comp (hasDerivAt_const (0 : ℝ) (group time))
  have secondDerivative := (hasDerivAt_const (0 : ℝ) (group time)).clm_comp (actualDerivative 0)
  simp only [atZero, ContinuousLinearMap.id_comp, ContinuousLinearMap.zero_comp,
    ContinuousLinearMap.comp_zero, zero_add, add_zero] at firstDerivative secondDerivative
  have functionEquality : (fun current => (group current).comp (group time)) =
      fun current => (group time).comp (group current) := by
    funext current
    rw [← addition, ← addition, add_comm]
  rw [functionEquality] at firstDerivative
  exact firstDerivative.unique secondDerivative

def quadraticConjugate (group : ℝ → Space →L[ℝ] Space) (time : ℝ) (bilinear : BilinearEnd Space) :
    BilinearEnd Space :=
  bilinearPostcompose (group (-time)) (bilinear.bilinearComp (group time) (group time))

def quadraticCommutator (generator : Space →L[ℝ] Space) (bilinear : BilinearEnd Space) :
    BilinearEnd Space :=
  -bilinearPostcompose generator bilinear +
    bilinear.bilinearComp generator (ContinuousLinearMap.id ℝ Space) +
    bilinear.bilinearComp (ContinuousLinearMap.id ℝ Space) generator

theorem quadraticConjugate_hasDerivAt
    (group : ℝ → Space →L[ℝ] Space) (generator : Space →L[ℝ] Space)
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (actualDerivative : ∀ time : ℝ, HasDerivAt group ((group time).comp generator) time)
    (bilinear : BilinearEnd Space) (time : ℝ) :
    HasDerivAt (fun current => quadraticConjugate group current bilinear)
      (quadraticCommutator generator (quadraticConjugate group time bilinear)) time := by
  have inner : HasDerivAt (fun current : ℝ => -current) (-1) time := by
    simpa only [id_eq] using (hasDerivAt_id time).neg
  have backward : HasDerivAt (fun current => group (-current))
      (-((group (-time)).comp generator)) time := by
    simpa only [neg_one_smul] using (actualDerivative (-time)).scomp time inner
  have precomposed := hasDerivAt_bilinearComp_fixed bilinear (actualDerivative time) (actualDerivative time)
  have actual := hasDerivAt_bilinearPostcompose backward precomposed
  have commuteValue (value : Space) : group (-time) (generator value) = generator (group (-time) value) := by
    exact congrArg (fun operator : Space →L[ℝ] Space => operator value)
      (linearGroup_generator_commute group generator atZero addition actualDerivative (-time)).symm
  convert actual using 1
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  simp [quadraticCommutator, quadraticConjugate, bilinearPostcompose, commuteValue]
  abel

theorem quadraticConjugate_norm_le
    (group : ℝ → Space →L[ℝ] Space) {bound : ℝ} (boundNonnegative : 0 ≤ bound)
    (groupBound : ∀ time : ℝ, ∀ value : Space, ‖group time value‖ ≤ bound * ‖value‖)
    (time : ℝ) (bilinear : BilinearEnd Space) :
    ‖quadraticConjugate group time bilinear‖ ≤ bound ^ 3 * ‖bilinear‖ := by
  have operatorBound (current : ℝ) : ‖group current‖ ≤ bound :=
    (group current).opNorm_le_bound boundNonnegative (groupBound current)
  calc
    _ ≤ ‖group (-time)‖ * ‖bilinear.bilinearComp (group time) (group time)‖ := norm_bilinearPostcompose_le _ _
    _ ≤ ‖group (-time)‖ * (‖bilinear‖ * ‖group time‖ * ‖group time‖) :=
      mul_le_mul_of_nonneg_left (norm_bilinearComp_le _ _ _) (norm_nonneg _)
    _ ≤ bound * (‖bilinear‖ * bound * bound) := by gcongr <;> exact operatorBound _
    _ = _ := by ring

end

end EulerNonuniqueness.General
