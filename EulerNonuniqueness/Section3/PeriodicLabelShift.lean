import EulerNonuniqueness.Section3.ContourPhaseParameter
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

def periodicLabelShift (angular : PeriodicC1HolderHalf) (label : ℝ) : ℝ :=
  label + (angular.val.1 label).re

def periodicLabelSlope (angular : PeriodicC1HolderHalf) (label : ℝ) : ℝ :=
  1 + (angular.val.2.val.1 label).re

theorem periodicLabelShift_hasDerivAt (angular : PeriodicC1HolderHalf) (label : ℝ) :
    HasDerivAt (periodicLabelShift angular) (periodicLabelSlope angular label) label :=
  (hasDerivAt_id label).add
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt label (PeriodicC1HolderHalf.hasDerivAt angular label))

theorem periodicLabelShift_continuous (angular : PeriodicC1HolderHalf) : Continuous (periodicLabelShift angular) :=
  continuous_id.add (Complex.continuous_re.comp angular.val.1.continuous)

theorem periodicLabelSlope_continuous (angular : PeriodicC1HolderHalf) : Continuous (periodicLabelSlope angular) :=
  continuous_const.add (Complex.continuous_re.comp angular.val.2.val.1.continuous)

theorem periodicLabelSlope_lower (angular : PeriodicC1HolderHalf) (label : ℝ) :
    1 - ‖angular‖ ≤ periodicLabelSlope angular label := by
  have bound := (Complex.abs_re_le_norm (angular.val.2.val.1 label)).trans
    (PeriodicC1HolderHalf.speed_bound angular label)
  dsimp only [periodicLabelSlope]
  linarith [(abs_le.mp bound).1]

theorem periodicLabelSlope_upper (angular : PeriodicC1HolderHalf) (label : ℝ) :
    |periodicLabelSlope angular label| ≤ 1 + ‖angular‖ := by
  exact (abs_add 1 (angular.val.2.val.1 label).re).trans (by
    rw [abs_one]
    exact add_le_add_left ((Complex.abs_re_le_norm _).trans (PeriodicC1HolderHalf.speed_bound angular label)) 1)

theorem periodicLabelShift_add_period (angular : PeriodicC1HolderHalf) (label : ℝ) :
    periodicLabelShift angular (label + 2 * Real.pi) = periodicLabelShift angular label + 2 * Real.pi := by
  unfold periodicLabelShift
  rw [PeriodicC1HolderHalf.periodic angular label]
  ring

theorem periodicLabelSlope_periodic (angular : PeriodicC1HolderHalf) :
    Function.Periodic (periodicLabelSlope angular) (2 * Real.pi) := by
  intro label
  dsimp only [periodicLabelSlope]
  rw [PeriodicHolderHalf.periodic angular.val.2 label]

theorem periodicLabelShift_surjective (angular : PeriodicC1HolderHalf) : Function.Surjective (periodicLabelShift angular) := by
  have bound (label : ℝ) : |(angular.val.1 label).re| ≤ ‖angular‖ :=
    (Complex.abs_re_le_norm _).trans (PeriodicC1HolderHalf.value_bound angular label)
  apply (periodicLabelShift_continuous angular).surjective
  · apply tendsto_atTop.mpr
    intro threshold
    filter_upwards [eventually_ge_atTop (threshold + ‖angular‖)] with label large
    dsimp only [periodicLabelShift]
    linarith [(abs_le.mp (bound label)).1]
  · apply tendsto_atBot.mpr
    intro threshold
    filter_upwards [eventually_le_atBot (threshold - ‖angular‖)] with label small
    dsimp only [periodicLabelShift]
    linarith [(abs_le.mp (bound label)).2]

theorem periodicLabelShift_strictMono (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1) :
    StrictMono (periodicLabelShift angular) :=
  strictMono_of_hasDerivAt_pos (periodicLabelShift_hasDerivAt angular)
    (fun label => (by linarith : 0 < 1 - ‖angular‖).trans_le (periodicLabelSlope_lower angular label))

def periodicLabelHomeomorph (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1) : ℝ ≃ₜ ℝ :=
  ((periodicLabelShift_strictMono angular small).orderIsoOfSurjective (periodicLabelShift angular)
    (periodicLabelShift_surjective angular)).toHomeomorph

theorem periodicLabelHomeomorph_apply (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1) (label : ℝ) :
    periodicLabelHomeomorph angular small label = periodicLabelShift angular label := rfl

theorem periodicLabelHomeomorph_symm_hasDerivAt (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1) (label : ℝ) :
    HasDerivAt (periodicLabelHomeomorph angular small).symm
      (periodicLabelSlope angular ((periodicLabelHomeomorph angular small).symm label))⁻¹ label := by
  have positive : 0 < periodicLabelSlope angular ((periodicLabelHomeomorph angular small).symm label) :=
    (by linarith : 0 < 1 - ‖angular‖).trans_le (periodicLabelSlope_lower angular _)
  apply (periodicLabelShift_hasDerivAt angular ((periodicLabelHomeomorph angular small).symm label)).of_local_left_inverse
    (periodicLabelHomeomorph angular small).symm.continuous.continuousAt positive.ne'
  exact Eventually.of_forall (periodicLabelHomeomorph angular small).apply_symm_apply

theorem periodicLabelHomeomorph_symm_add_period (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1) (label : ℝ) :
    (periodicLabelHomeomorph angular small).symm (label + 2 * Real.pi) =
      (periodicLabelHomeomorph angular small).symm label + 2 * Real.pi := by
  apply (periodicLabelHomeomorph angular small).injective
  rw [(periodicLabelHomeomorph angular small).apply_symm_apply, periodicLabelHomeomorph_apply,
    periodicLabelShift_add_period]
  change label + 2 * Real.pi = periodicLabelHomeomorph angular small ((periodicLabelHomeomorph angular small).symm label) + 2 * Real.pi
  rw [(periodicLabelHomeomorph angular small).apply_symm_apply]

theorem periodicLabelShift_lipschitz_bound (angular : PeriodicC1HolderHalf) (first second : ℝ) :
    |periodicLabelShift angular first - periodicLabelShift angular second| ≤ (1 + ‖angular‖) * |first - second| := by
  have bound : |(angular.val.1 first).re - (angular.val.1 second).re| ≤ ‖angular‖ * |first - second| := by
    rw [← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans (PeriodicC1HolderHalf.lipschitz_bound angular first second)
  have identity : periodicLabelShift angular first - periodicLabelShift angular second =
      (first - second) + ((angular.val.1 first).re - (angular.val.1 second).re) := by
    unfold periodicLabelShift
    ring
  rw [identity]
  exact (abs_add _ _).trans ((add_le_add_left bound _).trans_eq (by ring))

theorem periodicLabelShift_lower_lipschitz_bound (angular : PeriodicC1HolderHalf) (first second : ℝ) :
    (1 - ‖angular‖) * |first - second| ≤ |periodicLabelShift angular first - periodicLabelShift angular second| := by
  have bound : |(angular.val.1 first).re - (angular.val.1 second).re| ≤ ‖angular‖ * |first - second| := by
    rw [← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans (PeriodicC1HolderHalf.lipschitz_bound angular first second)
  have identity : first - second =
      (periodicLabelShift angular first - periodicLabelShift angular second) -
        ((angular.val.1 first).re - (angular.val.1 second).re) := by
    unfold periodicLabelShift
    ring
  have triangle := abs_sub (periodicLabelShift angular first - periodicLabelShift angular second)
    ((angular.val.1 first).re - (angular.val.1 second).re)
  rw [← identity] at triangle
  nlinarith

theorem periodicLabelHomeomorph_symm_lipschitz_bound (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (first second : ℝ) :
    |(periodicLabelHomeomorph angular (small.trans (by norm_num))).symm first -
      (periodicLabelHomeomorph angular (small.trans (by norm_num))).symm second| ≤ 2 * |first - second| := by
  let homeomorph := periodicLabelHomeomorph angular (small.trans (by norm_num))
  have bound := periodicLabelShift_lower_lipschitz_bound angular (homeomorph.symm first) (homeomorph.symm second)
  change (1 - ‖angular‖) * |homeomorph.symm first - homeomorph.symm second| ≤
    |homeomorph (homeomorph.symm first) - homeomorph (homeomorph.symm second)| at bound
  rw [homeomorph.apply_symm_apply, homeomorph.apply_symm_apply] at bound
  change |homeomorph.symm first - homeomorph.symm second| ≤ _
  nlinarith [abs_nonneg (homeomorph.symm first - homeomorph.symm second)]

end EulerNonuniqueness.Paper
