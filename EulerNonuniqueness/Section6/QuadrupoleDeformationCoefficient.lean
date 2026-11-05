import EulerNonuniqueness.Section6.MovingPatchPairDeformation
import EulerNonuniqueness.Section1.Scales

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

set_option synthInstance.maxHeartbeats 100000

theorem four_patch_internal_deformation_bound {count : ℕ}
    {configuration : FiniteContourConfiguration count} (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration)
    (receiver : Fin count) (member : receiver ∈ selected) (densityNonzero : configuration.density receiver ≠ 0)
    (atMostThree : (selected.erase receiver).card ≤ 3)
    (centers : Fin count → ℂ) {radius circulation deformation distance : ℝ}
    (radiusEquation : ∀ index ∈ selected, configuration.radius index = radius)
    (circulationEquation : ∀ index ∈ selected,
      |configuration.density index * (Real.pi * configuration.radius index ^ 2)| = circulation)
    (deformationNonnegative : 0 ≤ deformation) (deformationSmall : deformation ≤ 1 / 16)
    (lower : ∀ index ∈ selected, Metric.ball (centers index) (radius * (1 - deformation)) ⊆ flow.domain time index)
    (upper : ∀ index ∈ selected, flow.domain time index ⊆ Metric.ball (centers index) (radius * (1 + deformation)))
    (radiusSmall : 8 * radius ≤ distance)
    (separated : ∀ source ∈ selected.erase receiver,
      distance ≤ ‖flow.centroid time receiver - flow.centroid time source‖) :
    ‖flow.subfamilyInternalDeformationResidual selected time receiver‖ ≤
      3456 * circulation * radius ^ 2 * deformation / (Real.pi * distance ^ 3) := by
  have radiusPositive : 0 < radius := by
    rw [← radiusEquation receiver member]
    exact configuration.radius_pos receiver
  have distancePositive : 0 < distance := lt_of_lt_of_le (by positivity : 0 < 8 * radius) radiusSmall
  have circulationNonnegative : 0 ≤ circulation := by
    rw [← circulationEquation receiver member]
    exact abs_nonneg _
  have estimate := flow.subfamilyInternalDeformationResidual_bound_of_trapping selected inside receiver member
    densityNonzero centers (fun _ => deformation) (fun _ _ => deformationNonnegative) (fun _ _ => deformationSmall)
    (fun index indexMember => by simpa only [radiusEquation index indexMember] using lower index indexMember)
    (fun index indexMember => by simpa only [radiusEquation index indexMember] using upper index indexMember)
    (fun source sourceMember => by
      rw [radiusEquation receiver member, radiusEquation source (Finset.mem_erase.mp sourceMember).2]
      constructor
      · exact radiusSmall.trans (separated source sourceMember)
      · exact (show 4 * radius ≤ 8 * radius by linarith).trans (radiusSmall.trans (separated source sourceMember)))
  apply estimate.trans
  calc
    _ ≤ ∑ _source ∈ selected.erase receiver,
        1152 * circulation * radius ^ 2 * deformation / (Real.pi * distance ^ 3) := by
      apply Finset.sum_le_sum
      intro source sourceMember
      have sourceInside := (Finset.mem_erase.mp sourceMember).2
      rw [circulationEquation source sourceInside,
        radiusEquation source sourceInside, radiusEquation receiver member]
      calc
        _ = 1152 * circulation * radius ^ 2 * deformation /
            (Real.pi * ‖flow.centroid time receiver - flow.centroid time source‖ ^ 3) := by ring
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ distancePositive.le (separated source sourceMember) 3) Real.pi_pos.le)
    _ = ((selected.erase receiver).card : ℝ) *
        (1152 * circulation * radius ^ 2 * deformation / (Real.pi * distance ^ 3)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 3 * (1152 * circulation * radius ^ 2 * deformation / (Real.pi * distance ^ 3)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast atMostThree) (by positivity)
    _ = _ := by ring

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

namespace EulerNonuniqueness.Paper

theorem Scales.internal_deformation_coefficient (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : ℕ) {separation : ℝ}
    (separationPositive : 0 < separation) (deformation : ℝ) :
    3456 * scales.circulation index * scales.radius index ^ 2 * deformation /
        (Real.pi * (separation * scales.length index) ^ 3) =
      (13824 / (scales.amplitude * separation ^ 3) * scales.omega index ^ (-2 : ℤ) * deformation) *
        scales.length index := by
  rw [scales.radius_sq amplitudePositive frequencyPositive ratioPositive, Scales.circulation]
  have omegaNonzero := (scales.omega_pos frequencyPositive ratioPositive index).ne'
  have lengthNonzero := (scales.length_pos index).ne'
  simp only [zpow_neg, zpow_ofNat]
  field_simp [amplitudePositive.ne', separationPositive.ne', omegaNonzero, lengthNonzero, Real.pi_ne_zero]
  <;> ring

end EulerNonuniqueness.Paper
