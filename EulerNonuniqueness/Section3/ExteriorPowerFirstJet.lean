import EulerNonuniqueness.Section3.C1PowerFirstJetWeights
import EulerNonuniqueness.Section3.ExteriorGeneralContourSeries

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup
  forcingModeC1ComplexModule forcingModeC1ComplexSpace

def rotatedExteriorPowerFirstJet (phase : Circle) (base : PeriodicC1HolderHalf)
    (power : ℕ) (coefficient : ℂ) : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  (c1ProductCLM (c1Constant ((phase : ℂ)⁻¹ ^ (power + 2) * coefficient))).comp
    (c1ConjugateCLM.comp (c1NaturalPowerFirstJet base (power + 1)))

theorem rotatedExteriorPowerFirstJet_apply (phase : Circle) (base direction : PeriodicC1HolderHalf)
    (power : ℕ) (coefficient : ℂ) :
    rotatedExteriorPowerFirstJet phase base power coefficient direction =
      ((phase : ℂ)⁻¹ ^ (power + 2) * coefficient) •
        c1Conjugate (c1NaturalPowerFirstJet base (power + 1) direction) := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rfl

theorem rotatedExteriorPowerFirstJet_norm_bound (phase : Circle) (base : PeriodicC1HolderHalf)
    (bound : ‖base‖ ≤ 3) (power : ℕ) (coefficient : ℂ) :
    ‖rotatedExteriorPowerFirstJet phase base power coefficient‖ ≤
      (48 : ℝ) ^ (power + 1) * ‖coefficient‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro direction
  rw [rotatedExteriorPowerFirstJet_apply, norm_smul, norm_mul, norm_pow, norm_inv,
    Circle.norm_coe, inv_one, one_pow, one_mul]
  have bound := (c1Conjugate_norm_bound _).trans
    (c1NaturalPowerFirstJet_apply_geometric_bound base direction bound (power + 1))
  have estimate := mul_le_mul_of_nonneg_left bound (norm_nonneg coefficient)
  convert estimate using 1 <;> ring

theorem rotatedExteriorPowerFirstJet_error_identity (phase : Circle)
    (first base : PeriodicC1HolderHalf) (power : ℕ) (coefficient : ℂ) :
    rotatedExteriorPower phase first power coefficient - rotatedExteriorPower phase base power coefficient -
      rotatedExteriorPowerFirstJet phase base power coefficient (first - base) =
      ((phase : ℂ)⁻¹ ^ (power + 2) * coefficient) •
        c1Conjugate (c1NaturalPowerJetError first base (power + 1)) := by
  rw [rotatedExteriorPowerFirstJet_apply]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (((phase : ℂ)⁻¹ ^ (power + 2) * coefficient) *
      star ((c1NaturalPower first (power + 1)).val.1 label) -
      ((phase : ℂ)⁻¹ ^ (power + 2) * coefficient) *
        star ((c1NaturalPower base (power + 1)).val.1 label)) -
      ((phase : ℂ)⁻¹ ^ (power + 2) * coefficient) *
        star ((c1NaturalPowerFirstJet base (power + 1) (first - base)).val.1 label) =
    ((phase : ℂ)⁻¹ ^ (power + 2) * coefficient) *
      star ((c1NaturalPower first (power + 1)).val.1 label -
        (c1NaturalPower base (power + 1)).val.1 label -
        (c1NaturalPowerFirstJet base (power + 1) (first - base)).val.1 label)
  simp only [star_sub]
  ring

theorem rotatedExteriorPowerFirstJet_error_bound (phase : Circle)
    (first base : PeriodicC1HolderHalf) (firstBound : ‖first‖ ≤ 3) (baseBound : ‖base‖ ≤ 3)
    (power : ℕ) (coefficient : ℂ) :
    ‖rotatedExteriorPower phase first power coefficient - rotatedExteriorPower phase base power coefficient -
      rotatedExteriorPowerFirstJet phase base power coefficient (first - base)‖ ≤
      ((96 : ℝ) ^ (power + 1) * ‖coefficient‖) * ‖first - base‖ ^ 2 := by
  rw [rotatedExteriorPowerFirstJet_error_identity, norm_smul, norm_mul, norm_pow, norm_inv,
    Circle.norm_coe, inv_one, one_pow, one_mul]
  have bound := (c1Conjugate_norm_bound _).trans
    (c1NaturalPowerJetError_geometric_bound first base firstBound baseBound (power + 1))
  have estimate := mul_le_mul_of_nonneg_left bound (norm_nonneg coefficient)
  convert estimate using 1 <;> ring

end EulerNonuniqueness.Paper
