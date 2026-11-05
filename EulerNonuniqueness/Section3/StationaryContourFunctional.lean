import EulerNonuniqueness.Section3.ContourAntiholomorphicFunctional
import EulerNonuniqueness.Section3.MovingStrainSpectralRelabelDomain
import EulerNonuniqueness.Section3.CenteredForcingFixedRelabel
import EulerNonuniqueness.Section3.ContourCirclePositiveMoments

noncomputable section

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

local instance stationaryFunctionalC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem contourAntiholomorphicFunctional_stationary_base (kernel : ℂ → ℂ)
    (state : PeriodicC1HolderHalf) (small : ‖diskNeutralCLM state‖ < 1 / 2)
    (kernelContinuous : Continuous (fun label => kernel (standardCircle label))) :
    contourAntiholomorphicFunctional kernel (diskStationaryChart (diskRelabelNeutralCLM state)) =
      contourAntiholomorphicFunctional kernel standardCircleBanach := by
  rw [movingStrainSpectral_stationary_base_eq_fixedRelabel state small]
  exact contourAntiholomorphicFunctional_fixedRelabel_of_continuous_comp
    kernel (diskNeutralCLM state) small standardCircleBanach kernelContinuous

theorem contourPolynomialMoment_stationary_base_positive
    (state : PeriodicC1HolderHalf) (small : ‖diskNeutralCLM state‖ < 1 / 2) (degree : ℕ) :
    contourPolynomialMoment (degree + 1) (diskStationaryChart (diskRelabelNeutralCLM state)) = 0 := by
  rw [movingStrainSpectral_stationary_base_eq_fixedRelabel state small,
    contourPolynomialMoment_fixedRelabel, contourPolynomialMoment_circle_positive]

theorem contourAntiholomorphicFunctional_pair_eq_relative_increments
    (kernel : ℂ → ℂ) (initial final : PeriodicC1HolderHalf)
    (initialSmall : ‖diskNeutralCLM initial‖ < 1 / 2)
    (finalSmall : ‖diskNeutralCLM final‖ < 1 / 2)
    (kernelContinuous : Continuous (fun label => kernel (standardCircle label))) :
    contourAntiholomorphicFunctional kernel (diskPhysicalSpectralChart initial) -
      contourAntiholomorphicFunctional kernel (diskPhysicalSpectralChart final) =
      (contourAntiholomorphicFunctional kernel
          (diskStationaryChart (diskRelabelNeutralCLM initial) + diskPhysicalSpectralDefect initial) -
        contourAntiholomorphicFunctional kernel (diskStationaryChart (diskRelabelNeutralCLM initial))) -
      (contourAntiholomorphicFunctional kernel
          (diskStationaryChart (diskRelabelNeutralCLM final) + diskPhysicalSpectralDefect final) -
        contourAntiholomorphicFunctional kernel (diskStationaryChart (diskRelabelNeutralCLM final))) := by
  have initialIdentity := contourAntiholomorphicFunctional_stationary_base kernel initial initialSmall kernelContinuous
  have finalIdentity := contourAntiholomorphicFunctional_stationary_base kernel final finalSmall kernelContinuous
  have reconstruction (state : PeriodicC1HolderHalf) :
      diskStationaryChart (diskRelabelNeutralCLM state) + diskPhysicalSpectralDefect state =
        diskPhysicalSpectralChart state := by
    unfold diskPhysicalSpectralDefect
    abel
  rw [reconstruction, reconstruction, initialIdentity, finalIdentity]
  abel

end EulerNonuniqueness.Paper
