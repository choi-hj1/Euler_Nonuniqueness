import EulerNonuniqueness.Section3.C1HolderContinuousOperations
import EulerNonuniqueness.Section3.C1HolderInverseContinuity
import EulerNonuniqueness.Section3.CrossContourPhaseIdentity

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

local instance crossContourBanachContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd
local instance crossContourBanachContinuousNeg : ContinuousNeg PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousNeg
local instance crossContourBanachContinuousSub : ContinuousSub PeriodicC1HolderHalf :=
  ⟨by simpa only [sub_eq_add_neg] using
    (continuous_fst.add continuous_snd.neg :
      Continuous (fun pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf => pair.1 + -pair.2))⟩
local instance crossContourBanachHolderNormedSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance crossContourBanachC1NormedSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

def c1Phase (data : PeriodicC1HolderHalf) {lower : ℝ} (lower_pos : 0 < lower)
    (separated : ∀ label, lower ≤ ‖data.val.1 label‖) : PeriodicC1HolderHalf :=
  c1Product data (c1Inverse (c1Conjugate data) lower_pos
    (fun label => by rw [c1Conjugate_value, norm_star]; exact separated label))

theorem c1Phase_value (data : PeriodicC1HolderHalf) {lower : ℝ} (lower_pos : 0 < lower)
    (separated : ∀ label, lower ≤ ‖data.val.1 label‖) (label : ℝ) :
    (c1Phase data lower_pos separated).val.1 label =
      data.val.1 label / star (data.val.1 label) := by
  rw [c1Phase, c1Product_value, c1Inverse_value, c1Conjugate_value, div_eq_mul_inv]

set_option maxHeartbeats 1000000 in
theorem c1Phase_continuous {X : Type*} [TopologicalSpace X]
    (data : X → PeriodicC1HolderHalf) (data_continuous : Continuous data)
    {lower : ℝ} (lower_pos : 0 < lower)
    (separated : ∀ parameter label, lower ≤ ‖(data parameter).val.1 label‖) :
    Continuous (fun parameter => c1Phase (data parameter) lower_pos (separated parameter)) := by
  let conjugated : X → SeparatedC1Holder lower := fun parameter =>
    ⟨c1Conjugate (data parameter), fun label => by
      rw [c1Conjugate_value, norm_star]
      exact separated parameter label⟩
  have conjugated_continuous : Continuous conjugated :=
    (c1ConjugateCLM.continuous.comp data_continuous).subtype_mk _
  have inverse_continuous := (c1InverseOnSeparated_continuous lower_pos).comp conjugated_continuous
  exact c1Product_continuous.comp (data_continuous.prodMk inverse_continuous)

def crossContourDifference (target : PeriodicC1HolderHalf) (source : ℂ) : PeriodicC1HolderHalf :=
  target - c1Constant source

def crossContourPhaseIntegrand (target source : PeriodicC1HolderHalf)
    {lower : ℝ} (lower_pos : 0 < lower)
    (separated : ∀ sourceLabel targetLabel,
      lower ≤ ‖target.val.1 targetLabel - source.val.1 sourceLabel‖) (sourceLabel : ℝ) :
    PeriodicC1HolderHalf :=
  c1Product (c1Phase (crossContourDifference target (source.val.1 sourceLabel)) lower_pos
    (separated sourceLabel)) (c1Constant (star (source.val.2.val.1 sourceLabel)))

set_option maxHeartbeats 1000000 in
theorem crossContourPhaseIntegrand_continuous (target source : PeriodicC1HolderHalf)
    {lower : ℝ} (lower_pos : 0 < lower)
    (separated : ∀ sourceLabel targetLabel,
      lower ≤ ‖target.val.1 targetLabel - source.val.1 sourceLabel‖) :
    Continuous (crossContourPhaseIntegrand target source lower_pos separated) := by
  have difference_continuous : Continuous (fun label => crossContourDifference target (source.val.1 label)) :=
    continuous_const.sub (c1ConstantCLM.continuous.comp source.val.1.continuous)
  have phase_continuous := c1Phase_continuous _ difference_continuous lower_pos separated
  have tangent_continuous : Continuous (fun label => c1Constant (star (source.val.2.val.1 label))) :=
    c1ConstantCLM.continuous.comp (continuous_star.comp source.val.2.val.1.continuous)
  exact c1Product_continuous.comp (phase_continuous.prodMk tangent_continuous)

def crossContourVelocityBanach (target source : PeriodicC1HolderHalf)
    {lower : ℝ} (lower_pos : 0 < lower)
    (separated : ∀ sourceLabel targetLabel,
      lower ≤ ‖target.val.1 targetLabel - source.val.1 sourceLabel‖) : PeriodicC1HolderHalf :=
  (1 / (4 * Real.pi)) •
    ∫ label in (-Real.pi)..Real.pi, crossContourPhaseIntegrand target source lower_pos separated label

theorem crossContourPhaseIntegrand_value (target source : PeriodicC1HolderHalf)
    {lower : ℝ} (lower_pos : 0 < lower)
    (separated : ∀ sourceLabel targetLabel,
      lower ≤ ‖target.val.1 targetLabel - source.val.1 sourceLabel‖)
    (sourceLabel targetLabel : ℝ) :
    (crossContourPhaseIntegrand target source lower_pos separated sourceLabel).val.1 targetLabel =
      pointContourPhase source.val.1 (target.val.1 targetLabel) sourceLabel *
        star (source.val.2.val.1 sourceLabel) := by
  rw [crossContourPhaseIntegrand, c1Product_value, c1Phase_value, c1Constant_value]
  change ((target.val.1 targetLabel - source.val.1 sourceLabel) /
    star (target.val.1 targetLabel - source.val.1 sourceLabel)) * _ = _
  rw [pointContourPhase, show source.val.1 sourceLabel - target.val.1 targetLabel =
    -(target.val.1 targetLabel - source.val.1 sourceLabel) by ring, star_neg, neg_div_neg_eq]

set_option maxHeartbeats 1000000 in
theorem crossContourVelocityBanach_value (target source : PeriodicC1HolderHalf)
    {lower : ℝ} (lower_pos : 0 < lower)
    (separated : ∀ sourceLabel targetLabel,
      lower ≤ ‖target.val.1 targetLabel - source.val.1 sourceLabel‖) (label : ℝ) :
    (crossContourVelocityBanach target source lower_pos separated).val.1 label =
      pointContourVelocity source.val.1 source.val.2.val.1 (target.val.1 label) (-Real.pi) Real.pi := by
  have integrable : IntervalIntegrable (crossContourPhaseIntegrand target source lower_pos separated)
      volume (-Real.pi) Real.pi :=
    (crossContourPhaseIntegrand_continuous target source lower_pos separated).intervalIntegrable _ _
  have commute := (contourLabelEvaluation label).intervalIntegral_comp_comm integrable
  have closed : source.val.1 (-Real.pi) = source.val.1 Real.pi := by
    have periodic := PeriodicC1HolderHalf.periodic source (-Real.pi)
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at periodic
    exact periodic.symm
  have point_separated : ∀ parameter ∈ Icc (-Real.pi) Real.pi,
      source.val.1 parameter - target.val.1 label ≠ 0 := by
    intro parameter parameter_mem
    apply norm_pos_iff.mp
    rw [norm_sub_rev]
    exact lower_pos.trans_le (separated parameter label)
  have phase_identity := pointContourVelocity_eq_phase_integral
    (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]) source.val.1.continuous
    source.val.2.val.1.continuous (fun parameter _ => PeriodicC1HolderHalf.hasDerivAt source parameter)
    point_separated closed
  rw [phase_identity]
  change (contourLabelEvaluation label) ((1 / (4 * Real.pi)) •
    ∫ parameter in (-Real.pi)..Real.pi, crossContourPhaseIntegrand target source lower_pos separated parameter) = _
  rw [map_smul, ← commute]
  congr 1
  apply intervalIntegral.integral_congr
  intro parameter parameter_mem
  exact crossContourPhaseIntegrand_value target source lower_pos separated parameter label

end

end EulerNonuniqueness.Paper
