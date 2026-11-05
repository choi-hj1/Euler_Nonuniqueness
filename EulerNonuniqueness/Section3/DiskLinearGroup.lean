import EulerNonuniqueness.Section3.PeriodicHilbertGroup

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

local instance diskGroupHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance diskGroupC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance diskGroupC1BoundedSMul : IsBoundedSMul ℝ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℝ) (E := PeriodicC1HolderHalf)

def diskLinearFlow (time : ℝ) (radial angular : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  (periodicHilbertFlow time radial,
    angular + periodicHilbertC1 radial - periodicHilbertC1 (periodicHilbertFlow time radial))

theorem diskLinearFlow_neutral (time : ℝ) (radial angular : PeriodicC1HolderHalf) :
    (diskLinearFlow time radial angular).2 + periodicHilbertC1 (diskLinearFlow time radial angular).1 =
      angular + periodicHilbertC1 radial := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (angular.val.1 label + (periodicHilbertC1 radial).val.1 label -
    (periodicHilbertC1 (periodicHilbertFlow time radial)).val.1 label) +
    (periodicHilbertC1 (periodicHilbertFlow time radial)).val.1 label =
    angular.val.1 label + (periodicHilbertC1 radial).val.1 label
  ring

theorem diskLinearFlow_zero (radial angular : PeriodicC1HolderHalf) :
    diskLinearFlow 0 radial angular = (radial, angular) := by
  apply Prod.ext
  · exact periodicHilbertFlow_zero radial
  · change angular + periodicHilbertC1 radial - periodicHilbertC1 (periodicHilbertFlow 0 radial) = angular
    rw [periodicHilbertFlow_zero]
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change angular.val.1 label + (periodicHilbertC1 radial).val.1 label -
      (periodicHilbertC1 radial).val.1 label = angular.val.1 label
    ring

theorem diskLinearFlow_add (firstTime secondTime : ℝ) (radial angular : PeriodicC1HolderHalf) :
    diskLinearFlow firstTime (diskLinearFlow secondTime radial angular).1
      (diskLinearFlow secondTime radial angular).2 = diskLinearFlow (firstTime + secondTime) radial angular := by
  apply Prod.ext
  · exact periodicHilbertFlow_add firstTime secondTime radial
  · change (angular + periodicHilbertC1 radial - periodicHilbertC1 (periodicHilbertFlow secondTime radial)) +
      periodicHilbertC1 (periodicHilbertFlow secondTime radial) -
      periodicHilbertC1 (periodicHilbertFlow firstTime (periodicHilbertFlow secondTime radial)) = _
    rw [periodicHilbertFlow_add]
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change ((angular.val.1 label + (periodicHilbertC1 radial).val.1 label -
      (periodicHilbertC1 (periodicHilbertFlow secondTime radial)).val.1 label) +
      (periodicHilbertC1 (periodicHilbertFlow secondTime radial)).val.1 label) -
      (periodicHilbertC1 (periodicHilbertFlow (firstTime + secondTime) radial)).val.1 label =
      angular.val.1 label + (periodicHilbertC1 radial).val.1 label -
      (periodicHilbertC1 (periodicHilbertFlow (firstTime + secondTime) radial)).val.1 label
    ring

theorem diskLinearFlow_angular_formula (time : ℝ) (radial angular : PeriodicC1HolderHalf)
    (meanZero : c1AngularIntegralCCLM radial = 0) :
    (diskLinearFlow time radial angular).2 =
      angular + (1 - Real.cos (time / 2)) • periodicHilbertC1 radial +
        (-Real.sin (time / 2)) • radial := by
  change angular + periodicHilbertC1 radial - periodicHilbertC1 (periodicHilbertFlow time radial) = _
  rw [periodicHilbertC1_flow, periodicMeanZeroPartCCLM_of_integral_zero radial meanZero]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change angular.val.1 label + (periodicHilbertC1 radial).val.1 label -
      (Real.cos (time / 2) • (periodicHilbertC1 radial).val.1 label +
        Real.sin (time / 2) • radial.val.1 label) =
    angular.val.1 label + (1 - Real.cos (time / 2)) • (periodicHilbertC1 radial).val.1 label +
      (-Real.sin (time / 2)) • radial.val.1 label
  simp only [Complex.real_smul]
  push_cast
  ring

theorem diskLinearFlow_angular_hasDerivAt (time : ℝ) (radial angular : PeriodicC1HolderHalf)
    (meanZero : c1AngularIntegralCCLM radial = 0) :
    HasDerivAt (fun current => (diskLinearFlow current radial angular).2)
      ((-1 / 2 : ℝ) • (diskLinearFlow time radial angular).1) time := by
  have halfDerivative : HasDerivAt (fun current : ℝ => current / 2) (1 / 2) time := by
    simpa only [id_eq] using (hasDerivAt_id time).div_const 2
  have functionEquality : (fun current => (diskLinearFlow current radial angular).2) =
      fun current => angular + (1 - Real.cos (current / 2)) • periodicHilbertC1 radial +
        (-Real.sin (current / 2)) • radial :=
    funext (fun current => diskLinearFlow_angular_formula current radial angular meanZero)
  rw [functionEquality]
  have result := ((((halfDerivative.cos).const_sub 1).smul_const (periodicHilbertC1 radial)).const_add angular).add
    ((halfDerivative.sin.neg).smul_const radial)
  convert result using 1
  change (-1 / 2 : ℝ) • periodicHilbertFlow time radial = _
  rw [periodicHilbertFlow_of_mean_zero time radial meanZero]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (-1 / 2 : ℝ) • (Real.cos (time / 2) • radial.val.1 label +
      (-Real.sin (time / 2)) • (periodicHilbertC1 radial).val.1 label) =
    (-(-Real.sin (time / 2) * (1 / 2))) • (periodicHilbertC1 radial).val.1 label +
      (-(Real.cos (time / 2) * (1 / 2))) • radial.val.1 label
  simp only [Complex.real_smul]
  push_cast
  ring

theorem diskLinearFlow_equations (time : ℝ) (radial angular : PeriodicC1HolderHalf)
    (meanZero : c1AngularIntegralCCLM radial = 0) :
    HasDerivAt (fun current => (diskLinearFlow current radial angular).1)
      ((-1 / 2 : ℝ) • periodicHilbertC1 (diskLinearFlow time radial angular).1) time ∧
    HasDerivAt (fun current => (diskLinearFlow current radial angular).2)
      ((-1 / 2 : ℝ) • (diskLinearFlow time radial angular).1) time :=
  ⟨periodicHilbertFlow_hasDerivAt time radial,
    diskLinearFlow_angular_hasDerivAt time radial angular meanZero⟩

theorem diskLinearFlow_angular_norm_bound (time : ℝ) (radial angular : PeriodicC1HolderHalf) :
    ‖(diskLinearFlow time radial angular).2‖ ≤
      ‖angular‖ + 2 * periodicHilbertBound * (4 + 2 * periodicHilbertBound) * ‖radial‖ := by
  have propagated : ‖periodicHilbertC1 (periodicHilbertFlow time radial)‖ ≤
      2 * periodicHilbertBound * ((3 + 2 * periodicHilbertBound) * ‖radial‖) :=
    (periodicHilbertC1_norm_bound _).trans
      (mul_le_mul_of_nonneg_left (periodicHilbertFlow_norm_bound time radial)
        (mul_nonneg (by norm_num) periodicHilbertBound_nonneg))
  change ‖angular + periodicHilbertC1 radial - periodicHilbertC1 (periodicHilbertFlow time radial)‖ ≤ _
  calc
    _ ≤ (‖angular‖ + ‖periodicHilbertC1 radial‖) + ‖periodicHilbertC1 (periodicHilbertFlow time radial)‖ :=
      (norm_sub_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ (‖angular‖ + 2 * periodicHilbertBound * ‖radial‖) +
        2 * periodicHilbertBound * ((3 + 2 * periodicHilbertBound) * ‖radial‖) :=
      add_le_add (add_le_add_left (periodicHilbertC1_norm_bound radial) _) propagated
    _ = _ := by ring

theorem diskLinearFlow_uniform_bound (time : ℝ) (radial angular : PeriodicC1HolderHalf) :
    ‖(diskLinearFlow time radial angular).1‖ + ‖(diskLinearFlow time radial angular).2‖ ≤
      (3 + 10 * periodicHilbertBound + 4 * periodicHilbertBound ^ 2) * (‖radial‖ + ‖angular‖) := by
  let coefficient := 3 + 10 * periodicHilbertBound + 4 * periodicHilbertBound ^ 2
  have coefficientLarge : 1 ≤ coefficient := by
    dsimp only [coefficient]
    nlinarith [periodicHilbertBound_nonneg, sq_nonneg periodicHilbertBound]
  calc
    _ ≤ (3 + 2 * periodicHilbertBound) * ‖radial‖ +
        (‖angular‖ + 2 * periodicHilbertBound * (4 + 2 * periodicHilbertBound) * ‖radial‖) :=
      add_le_add (periodicHilbertFlow_norm_bound time radial) (diskLinearFlow_angular_norm_bound time radial angular)
    _ = coefficient * ‖radial‖ + ‖angular‖ := by dsimp only [coefficient]; ring
    _ ≤ coefficient * ‖radial‖ + coefficient * ‖angular‖ :=
      add_le_add_left (le_mul_of_one_le_left (norm_nonneg angular) coefficientLarge) _
    _ = _ := by dsimp only [coefficient]; ring

end

end EulerNonuniqueness.Paper
