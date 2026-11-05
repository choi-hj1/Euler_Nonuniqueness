import EulerNonuniqueness.Section6.CoMovingPairIntegrability

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem ae_coMovingVorticityPair_symmetrization {vorticity : Vorticity} (center : ℂ)
    {distance : ℝ} (positive : 0 < distance)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖) (power : ℕ) :
    ∀ᵐ pair : ℂ × ℂ ∂volume.prod volume,
      coMovingVorticityPair vorticity center power pair + coMovingVorticityPair vorticity center power pair.swap =
        -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * (vorticity pair.1 •
          (vorticity pair.2 • coMovingInversePowerKernel power (center - pair.1) (center - pair.2))) := by
  have offDiagonal : ∀ᵐ pair : ℂ × ℂ ∂volume.prod volume, pair.1 ≠ pair.2 := by
    apply (Measure.ae_prod_iff_ae_ae (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mpr
    filter_upwards [] with first
    rw [ae_iff]
    change volume {second : ℂ | ¬first ≠ second} = 0
    have setIdentity : {second : ℂ | ¬first ≠ second} = {first} := by
      ext second
      simp only [Set.mem_setOf_eq, not_not, Set.mem_singleton_iff, eq_comm]
    rw [setIdentity]
    exact measure_singleton first
  filter_upwards [offDiagonal] with pair distinct
  by_cases firstZero : vorticity pair.1 = 0
  · simp [coMovingVorticityPair, firstZero]
  by_cases secondZero : vorticity pair.2 = 0
  · simp [coMovingVorticityPair, secondZero]
  have firstNonzero : center - pair.1 ≠ 0 := norm_pos_iff.mp
    (positive.trans_le (separated pair.1 (Function.mem_support.mpr firstZero)))
  have secondNonzero : center - pair.2 ≠ 0 := norm_pos_iff.mp
    (positive.trans_le (separated pair.2 (Function.mem_support.mpr secondZero)))
  have displacementDistinct : center - pair.1 ≠ center - pair.2 := by
    intro equal
    apply distinct
    linear_combination -equal
  have identity := coMoving_biotSavartKernel_symmetrization power firstNonzero secondNonzero displacementDistinct
  rw [show center - pair.2 - (center - pair.1) = pair.1 - pair.2 by abel,
    show center - pair.1 - (center - pair.2) = pair.2 - pair.1 by abel] at identity
  dsimp only [coMovingVorticityPair, Prod.swap]
  simp only [Complex.real_smul]
  linear_combination ((vorticity pair.1 : ℂ) * (vorticity pair.2 : ℂ)) * identity

theorem integral_coMovingVorticityPair_symmetrization {vorticity : Vorticity}
    (integrable : Integrable vorticity) {radius bound distance : ℝ}
    (supported : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (bounded : ∀ position, |vorticity position| ≤ bound)
    (center : ℂ) (positive : 0 < distance)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖) (power : ℕ) :
    (∫ pair : ℂ × ℂ, coMovingVorticityPair vorticity center power pair ∂volume.prod volume) =
      -(Complex.I / ((4 * Real.pi : ℝ) : ℂ)) *
        ∫ pair : ℂ × ℂ, vorticity pair.1 •
          (vorticity pair.2 • coMovingInversePowerKernel power (center - pair.1) (center - pair.2)) ∂volume.prod volume := by
  have joint := integrable_coMovingVorticityPair integrable supported bounded center positive separated power
  have swappedJoint : Integrable (fun pair : ℂ × ℂ => coMovingVorticityPair vorticity center power pair.swap)
      (volume.prod volume) := joint.swap
  have identity := integral_congr_ae (ae_coMovingVorticityPair_symmetrization center positive separated power)
  rw [integral_add joint swappedJoint, integral_const_mul, integral_prod_swap] at identity
  push_cast at identity ⊢
  simp only [div_eq_mul_inv, mul_inv_rev] at identity ⊢
  linear_combination (1 / 2 : ℂ) * identity

end EulerNonuniqueness.Section6
