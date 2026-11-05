import EulerNonuniqueness.Section8.SmoothQuadraticIntegral

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem integral_smooth_vorticity_transport_eq_quadratic {vorticity potential : Vorticity}
    (sourceSmooth : ContDiff ℝ ∞ vorticity) (sourceCompact : HasCompactSupport vorticity)
    (potentialSmooth : ContDiff ℝ ∞ potential) (potentialCompact : HasCompactSupport potential) :
    (∫ position, vorticity position * fderiv ℝ potential position (biotSavart vorticity position)) =
      ∫ position, transportQuadratic (fun other => (biotSavart vorticity other).re)
        (fun other => (biotSavart vorticity other).im) potential position := by
  let first := fun position => (biotSavart vorticity position).re
  let second := fun position => (biotSavart vorticity position).im
  let paired := fun position => first position * fderiv ℝ potential position 1 +
    second position * fderiv ℝ potential position Complex.I
  have velocitySmooth := contDiff_biotSavart_of_contDiff_compactSupport sourceSmooth sourceCompact
  have firstSmooth : ContDiff ℝ ∞ first := Complex.reCLM.contDiff.comp velocitySmooth
  have secondSmooth : ContDiff ℝ ∞ second := Complex.imCLM.contDiff.comp velocitySmooth
  have pairedSmooth : ContDiff ℝ ∞ paired :=
    (firstSmooth.mul (contDiff_directionalDerivative potentialSmooth 1)).add
      (secondSmooth.mul (contDiff_directionalDerivative potentialSmooth Complex.I))
  have pairedCompact : HasCompactSupport paired :=
    (potentialCompact.fderiv_apply ℝ 1).mul_left.add (potentialCompact.fderiv_apply ℝ Complex.I).mul_left
  obtain ⟨radius, positive, bounded⟩ := sourceCompact.isCompact.isBounded.exists_pos_norm_le
  have supported : Function.support vorticity ⊆ Metric.closedBall 0 radius := by
    intro position nonzero
    simpa using bounded position (subset_tsupport _ nonzero)
  have curl := (curl_biotSavart_of_integrable_support
    (sourceSmooth.continuous.integrable_of_hasCompactSupport sourceCompact) supported pairedSmooth pairedCompact).2
  have pairedEquality : (fun position => vorticity position * fderiv ℝ potential position (biotSavart vorticity position)) =
      (fun position => vorticity position * paired position) := by
    funext position
    rw [realLinearMap_apply_complex]
  rw [pairedEquality, ← curl]
  have derivativeEquality : (fun position => fderiv ℝ paired position (Complex.I * biotSavart vorticity position)) =
      (fun position => -second position * fderiv ℝ paired position 1 + first position * fderiv ℝ paired position Complex.I) := by
    funext position
    rw [realLinearMap_apply_complex]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, zero_add]
    rfl
  rw [derivativeEquality]
  exact integral_smooth_transport_quadratic firstSmooth secondSmooth potentialSmooth potentialCompact
    (divergence_biotSavart_smooth sourceSmooth sourceCompact)

end EulerNonuniqueness
