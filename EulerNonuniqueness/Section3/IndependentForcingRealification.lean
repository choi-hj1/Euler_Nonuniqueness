import EulerNonuniqueness.Section3.IndependentForcingSpectralSolver
import EulerNonuniqueness.General.ComplexPairRealification
import EulerNonuniqueness.General.RealifiedComplexApplication

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

local instance independentRealificationC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

local instance independentRealificationOutputGroup : NormedAddCommGroup
    ((PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf × PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

local instance independentRealificationInputGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf × PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf × PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

def contourIndependentRealification :
    (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℝ] PeriodicC1HolderHalf :=
  ContinuousLinearMap.fst ℝ PeriodicC1HolderHalf PeriodicC1HolderHalf +
    c1ConjugateCLM.comp (ContinuousLinearMap.snd ℝ PeriodicC1HolderHalf PeriodicC1HolderHalf)

theorem contourIndependentRealification_eq_twice_real (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    contourIndependentRealification pair =
      (2 : ℝ) • EulerNonuniqueness.General.complexPairReal c1ConjugateCLM pair := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change pair.1.val.1 label + star (pair.2.val.1 label) =
    (2 : ℝ) • ((1 / 2 : ℂ) * (pair.1.val.1 label + star (pair.2.val.1 label)))
  rw [Complex.real_smul]
  push_cast
  ring

theorem contourIndependentRealification_positive (direction : PeriodicC1HolderHalf) :
    contourIndependentRealification (direction, 0) = direction := by
  change direction + c1ConjugateCLM 0 = direction
  rw [map_zero, add_zero]

theorem contourIndependentRealification_norm_le (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    ‖contourIndependentRealification pair‖ ≤ 2 * ‖pair‖ := by
  change ‖pair.1 + c1Conjugate pair.2‖ ≤ _
  have first := norm_fst_le pair
  have second := norm_snd_le pair
  exact ((norm_add_le _ _).trans (add_le_add_left (c1Conjugate_norm_bound pair.2) _)).trans (by linarith)

theorem contourIndependentEmbedding_norm_le (direction : PeriodicC1HolderHalf) :
    ‖contourIndependentEmbedding direction‖ ≤ ‖direction‖ := by
  change max ‖direction‖ ‖c1Conjugate direction‖ ≤ ‖direction‖
  exact max_le le_rfl (c1Conjugate_norm_bound direction)

theorem contourIndependentRealification_generator (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    contourIndependentRealification (independentDiskRotatingDerivative pair) =
      diskRotatingDerivative (contourIndependentRealification pair) := by
  rw [contourIndependentRealification_eq_twice_real, contourIndependentRealification_eq_twice_real]
  unfold independentDiskRotatingDerivative
  with_reducible
    have commutes := EulerNonuniqueness.General.complexPairReal_extension c1ConjugateCLM
      c1ConjugateCLM_complex_smul c1ConjugateCLM_involution diskRotatingDerivative pair
    rw [commutes]
    exact (diskRotatingDerivative.map_smul (2 : ℝ) _).symm

def independentForcingRealLinearCorrection (degree : ℕ) (coefficient : ℂ) (direction : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf :=
  contourIndependentRealification
    (coefficient • independentForcingLinearCorrection degree (contourIndependentEmbedding direction))

theorem independentForcingRealLinearCorrection_add (degree : ℕ) (coefficient : ℂ)
    (first second : PeriodicC1HolderHalf) :
    independentForcingRealLinearCorrection degree coefficient (first + second) =
      independentForcingRealLinearCorrection degree coefficient first +
        independentForcingRealLinearCorrection degree coefficient second := by
  simp only [independentForcingRealLinearCorrection, map_add, smul_add]

theorem independentForcingRealLinearCorrection_real_smul (degree : ℕ) (coefficient : ℂ)
    (scalar : ℝ) (direction : PeriodicC1HolderHalf) :
    independentForcingRealLinearCorrection degree coefficient (scalar • direction) =
      scalar • independentForcingRealLinearCorrection degree coefficient direction := by
  unfold independentForcingRealLinearCorrection
  with_reducible
    exact EulerNonuniqueness.General.realifiedComplexApplication_real_smul
      contourIndependentRealification contourIndependentEmbedding
      (independentForcingLinearCorrection degree) coefficient scalar direction

theorem independentForcingRealLinearCorrection_norm_le (degree : ℕ) (coefficient : ℂ)
    (direction : PeriodicC1HolderHalf) :
    ‖independentForcingRealLinearCorrection degree coefficient direction‖ ≤
      (2 * ‖coefficient‖ * ‖independentForcingLinearCorrection degree‖) * ‖direction‖ := by
  unfold independentForcingRealLinearCorrection
  with_reducible
    exact EulerNonuniqueness.General.realifiedComplexApplication_norm_le
      contourIndependentRealification contourIndependentEmbedding
      (independentForcingLinearCorrection degree) coefficient direction
      contourIndependentRealification_norm_le contourIndependentEmbedding_norm_le

end

end EulerNonuniqueness.Paper
