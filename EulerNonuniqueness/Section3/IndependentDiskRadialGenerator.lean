import EulerNonuniqueness.Section3.IndependentDiskSpectrum
import EulerNonuniqueness.Section3.IndependentFullRadialResonance

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance independentRadialGeneratorGroup : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

def independentRadialGenerator :
    (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  (((c1MultiplierCCLM standardCircleBanach).comp
      ((-1 / 2 : ℂ) • periodicHilbertC1CCLM -
        (Complex.I / 2) • periodicMeanZeroPartCCLM)).prod
    ((c1MultiplierCCLM (c1Conjugate standardCircleBanach)).comp
      ((-1 / 2 : ℂ) • periodicHilbertC1CCLM +
        (Complex.I / 2) • periodicMeanZeroPartCCLM))).comp independentFullRadial

theorem independentRadialGenerator_apply (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    independentRadialGenerator pair =
      (c1Product standardCircleBanach
          ((-1 / 2 : ℂ) • periodicHilbertC1 (independentFullRadial pair) -
            (Complex.I / 2) • periodicMeanZeroPartCCLM (independentFullRadial pair)),
        c1Product (c1Conjugate standardCircleBanach)
          ((-1 / 2 : ℂ) • periodicHilbertC1 (independentFullRadial pair) +
            (Complex.I / 2) • periodicMeanZeroPartCCLM (independentFullRadial pair))) := rfl

theorem independentFullRadial_embedding (direction : PeriodicC1HolderHalf) :
    independentFullRadial (EulerNonuniqueness.General.complexPairEmbedding c1ConjugateCLM direction) =
      diskRadialPart direction := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [independentFullRadial_value]
  change (star (standardCircle label) * direction.val.1 label +
    standardCircle label * star (direction.val.1 label)) / 2 =
    (1 / 2 : ℝ) • (star (standardCircle label) * direction.val.1 label +
      star (star (standardCircle label) * direction.val.1 label))
  simp only [Complex.real_smul, star_mul, star_star]
  push_cast
  ring

theorem periodicHilbertC1_real_value (data : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (data.val.1 label) = data.val.1 label) (label : ℝ) :
    star ((periodicHilbertC1 data).val.1 label) = (periodicHilbertC1 data).val.1 label := by
  rw [periodicHilbertC1_value]
  exact periodicHilbertCLM_real (c1ValueHolder data) realValues label

theorem periodicMeanZeroPart_real_value (data : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (data.val.1 label) = data.val.1 label) (label : ℝ) :
    star ((periodicMeanZeroPartCCLM data).val.1 label) = (periodicMeanZeroPartCCLM data).val.1 label := by
  have secondReal := periodicHilbertC1_real_value (periodicHilbertC1 data)
    (periodicHilbertC1_real_value data realValues) label
  have square := congrArg (fun value : PeriodicC1HolderHalf => value.val.1 label) (periodicHilbertC1_sq data)
  change (periodicHilbertC1 (periodicHilbertC1 data)).val.1 label =
    -(periodicMeanZeroPartCCLM data).val.1 label at square
  rw [square, star_neg] at secondReal
  exact neg_injective secondReal

theorem independentRadialGenerator_embedding (direction : PeriodicC1HolderHalf) :
    independentRadialGenerator (EulerNonuniqueness.General.complexPairEmbedding c1ConjugateCLM direction) =
      EulerNonuniqueness.General.complexPairEmbedding c1ConjugateCLM (diskRotatingDerivative direction) := by
  rw [independentRadialGenerator_apply, independentFullRadial_embedding]
  have actual := (diskRotatingDerivative_apply direction).trans (disk_contour_generator direction)
  apply Prod.ext
  · change _ = diskRotatingDerivative direction
    rw [actual]
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change standardCircle label * ((-1 / 2 : ℂ) * _ - Complex.I / 2 * _) =
      standardCircle label * ((-(1 / 2 : ℝ)) • _ - Complex.I / 2 * _)
    simp only [Complex.real_smul]
    norm_num
    left
    rfl
  · change _ = c1Conjugate (diskRotatingDerivative direction)
    rw [actual]
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change star (standardCircle label) * ((-1 / 2 : ℂ) * _ + Complex.I / 2 * _) =
      star (standardCircle label * ((-(1 / 2 : ℝ)) •
        (periodicHilbertC1 (diskRadialPart direction)).val.1 label -
        Complex.I / 2 * (periodicMeanZeroPartCCLM (diskRadialPart direction)).val.1 label))
    simp only [Complex.real_smul, star_mul, star_sub,
      periodicHilbertC1_real_value _ (diskRadialPart_real direction),
      periodicMeanZeroPart_real_value _ (diskRadialPart_real direction)]
    simp only [map_div₀, map_neg, map_one, map_ofNat, Complex.star_def, Complex.conj_I]
    norm_num
    simp only [map_ofNat]
    ring

theorem independentDiskRotatingDerivative_eq_radialGenerator :
    independentDiskRotatingDerivative = independentRadialGenerator := by
  apply EulerNonuniqueness.General.complexPair_linear_ext c1ConjugateCLM
    c1ConjugateCLM_complex_smul c1ConjugateCLM_involution
  intro direction
  rw [independentRadialGenerator_embedding]
  exact EulerNonuniqueness.General.complexPairExtension_embedding c1ConjugateCLM
    c1ConjugateCLM_complex_smul c1ConjugateCLM_involution diskRotatingDerivative direction

theorem independentDiskRotatingDerivative_full_radial (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    independentFullRadial (independentDiskRotatingDerivative pair) =
      (-1 / 2 : ℂ) • periodicHilbertC1 (independentFullRadial pair) := by
  rw [independentDiskRotatingDerivative_eq_radialGenerator, independentRadialGenerator_apply]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [independentFullRadial_value]
  change (star (standardCircle label) * (standardCircle label *
      ((-1 / 2 : ℂ) * (periodicHilbertC1 (independentFullRadial pair)).val.1 label -
        Complex.I / 2 * (periodicMeanZeroPartCCLM (independentFullRadial pair)).val.1 label)) +
    standardCircle label * (star (standardCircle label) *
      ((-1 / 2 : ℂ) * (periodicHilbertC1 (independentFullRadial pair)).val.1 label +
        Complex.I / 2 * (periodicMeanZeroPartCCLM (independentFullRadial pair)).val.1 label))) / 2 =
      (-1 / 2 : ℂ) * (periodicHilbertC1 (independentFullRadial pair)).val.1 label
  have unit : star (standardCircle label) * standardCircle label = 1 := by
    rw [standardCircle_star_eq_inv, inv_mul_cancel₀]
    exact Complex.exp_ne_zero _
  calc
    _ = (star (standardCircle label) * standardCircle label) *
        ((-1 / 2 : ℂ) * (periodicHilbertC1 (independentFullRadial pair)).val.1 label) := by ring
    _ = _ := by rw [unit, one_mul]

theorem independentDiskRotatingDerivative_radial_apply (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    independentDiskRotatingDerivative pair =
      (c1Product standardCircleBanach
          ((-1 / 2 : ℂ) • periodicHilbertC1 (independentFullRadial pair) -
            (Complex.I / 2) • periodicMeanZeroPartCCLM (independentFullRadial pair)),
        c1Product (c1Conjugate standardCircleBanach)
          ((-1 / 2 : ℂ) • periodicHilbertC1 (independentFullRadial pair) +
            (Complex.I / 2) • periodicMeanZeroPartCCLM (independentFullRadial pair))) := by
  rw [independentDiskRotatingDerivative_eq_radialGenerator, independentRadialGenerator_apply]

theorem independentDiskRotatingDerivative_square_radial (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    independentDiskRotatingDerivative (independentDiskRotatingDerivative pair) =
      (c1Product standardCircleBanach
          ((-1 / 4 : ℂ) • periodicMeanZeroPartCCLM (independentFullRadial pair) +
            (Complex.I / 4) • periodicHilbertC1 (independentFullRadial pair)),
        c1Product (c1Conjugate standardCircleBanach)
          ((-1 / 4 : ℂ) • periodicMeanZeroPartCCLM (independentFullRadial pair) -
            (Complex.I / 4) • periodicHilbertC1 (independentFullRadial pair))) := by
  rw [independentDiskRotatingDerivative_radial_apply (independentDiskRotatingDerivative pair),
    independentDiskRotatingDerivative_full_radial, periodicHilbertC1_smul_complex,
    periodicHilbertC1_sq, map_smul, periodicMeanZeroPart_hilbert]
  apply Prod.ext <;> apply PeriodicC1HolderHalf.ext_value <;> intro label
  · let mean : ℂ := (periodicMeanZeroPartCCLM (independentFullRadial pair)).val.1 label
    let hilbert : ℂ := (periodicHilbertC1 (independentFullRadial pair)).val.1 label
    change standardCircle label * ((-1 / 2 : ℂ) * ((-1 / 2 : ℂ) * (-mean)) -
      Complex.I / 2 * ((-1 / 2 : ℂ) * hilbert)) =
      standardCircle label * ((-1 / 4 : ℂ) * mean + Complex.I / 4 * hilbert)
    ring
  · let mean : ℂ := (periodicMeanZeroPartCCLM (independentFullRadial pair)).val.1 label
    let hilbert : ℂ := (periodicHilbertC1 (independentFullRadial pair)).val.1 label
    change star (standardCircle label) * ((-1 / 2 : ℂ) * ((-1 / 2 : ℂ) * (-mean)) +
      Complex.I / 2 * ((-1 / 2 : ℂ) * hilbert)) =
      star (standardCircle label) * ((-1 / 4 : ℂ) * mean - Complex.I / 4 * hilbert)
    ring

theorem independentDiskPositiveProjection_radial (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    independentDiskPositiveProjection pair =
      (0, (2 : ℂ) • c1Product (c1Conjugate standardCircleBanach)
        (periodicHilbertPositiveProjection (independentFullRadial pair))) := by
  unfold independentDiskPositiveProjection EulerNonuniqueness.General.complexCubicPositive
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  rw [independentDiskRotatingDerivative_square_radial, independentDiskRotatingDerivative_radial_apply,
    periodicHilbertPositiveProjection_apply]
  apply Prod.ext <;> apply PeriodicC1HolderHalf.ext_value <;> intro label
  · change (-2 : ℂ) * (standardCircle label * ((-1 / 4 : ℂ) *
        (periodicMeanZeroPartCCLM (independentFullRadial pair)).val.1 label + Complex.I / 4 *
          (periodicHilbertC1 (independentFullRadial pair)).val.1 label)) -
      Complex.I * (standardCircle label * ((-1 / 2 : ℂ) *
        (periodicHilbertC1 (independentFullRadial pair)).val.1 label - Complex.I / 2 *
          (periodicMeanZeroPartCCLM (independentFullRadial pair)).val.1 label)) = 0
    ring_nf
    simp only [Complex.I_sq]
    ring
  · change (-2 : ℂ) * (star (standardCircle label) * ((-1 / 4 : ℂ) *
        (periodicMeanZeroPartCCLM (independentFullRadial pair)).val.1 label - Complex.I / 4 *
          (periodicHilbertC1 (independentFullRadial pair)).val.1 label)) -
      Complex.I * (star (standardCircle label) * ((-1 / 2 : ℂ) *
        (periodicHilbertC1 (independentFullRadial pair)).val.1 label + Complex.I / 2 *
          (periodicMeanZeroPartCCLM (independentFullRadial pair)).val.1 label)) =
      2 * (star (standardCircle label) * ((1 / 2 : ℂ) *
        ((periodicMeanZeroPartCCLM (independentFullRadial pair)).val.1 label + Complex.I *
          (periodicHilbertC1 (independentFullRadial pair)).val.1 label)))
    ring_nf
    simp only [Complex.I_sq]
    ring
theorem independentDiskNegativeProjection_radial (pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    independentDiskNegativeProjection pair =
      ((2 : ℂ) • c1Product standardCircleBanach
        (periodicHilbertNegativeProjection (independentFullRadial pair)), 0) := by
  unfold independentDiskNegativeProjection EulerNonuniqueness.General.complexCubicNegative
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  rw [independentDiskRotatingDerivative_square_radial, independentDiskRotatingDerivative_radial_apply,
    periodicHilbertNegativeProjection_apply]
  apply Prod.ext <;> apply PeriodicC1HolderHalf.ext_value <;> intro label
  · change (-2 : ℂ) * (standardCircle label * ((-1 / 4 : ℂ) *
        (periodicMeanZeroPartCCLM (independentFullRadial pair)).val.1 label + Complex.I / 4 *
          (periodicHilbertC1 (independentFullRadial pair)).val.1 label)) +
      Complex.I * (standardCircle label * ((-1 / 2 : ℂ) *
        (periodicHilbertC1 (independentFullRadial pair)).val.1 label - Complex.I / 2 *
          (periodicMeanZeroPartCCLM (independentFullRadial pair)).val.1 label)) =
      2 * (standardCircle label * ((1 / 2 : ℂ) *
        ((periodicMeanZeroPartCCLM (independentFullRadial pair)).val.1 label - Complex.I *
          (periodicHilbertC1 (independentFullRadial pair)).val.1 label)))
    ring_nf
    simp only [Complex.I_sq]
    ring
  · change (-2 : ℂ) * (star (standardCircle label) * ((-1 / 4 : ℂ) *
        (periodicMeanZeroPartCCLM (independentFullRadial pair)).val.1 label - Complex.I / 4 *
          (periodicHilbertC1 (independentFullRadial pair)).val.1 label)) +
      Complex.I * (star (standardCircle label) * ((-1 / 2 : ℂ) *
        (periodicHilbertC1 (independentFullRadial pair)).val.1 label + Complex.I / 2 *
          (periodicMeanZeroPartCCLM (independentFullRadial pair)).val.1 label)) = 0
    ring_nf
    simp only [Complex.I_sq]
    ring

end

end EulerNonuniqueness.Paper
