import OAI.RepresentationTheory.Weil.Local.PlanarRadialCompact
import OAI.RepresentationTheory.Weil.Local.PlanarRadialTransfer

/-! # Planar Compact Transfer -/

namespace OAI.RepresentationTheory.Weil.Local.PlanarCompactTransfer.Construction

noncomputable section

/-! The derivative-transfer integrals exist for every smooth radial amplitude with an upper cutoff. -/

open _root_.MeasureTheory Set
open scoped ContDiff

theorem planarRadial_compactSupport_of_support_subset (F : ℝ → ℂ) (U : ℝ)
    (hF : Function.support F ⊆ Iic U) : HasCompactSupport (PlanarRadialCompact.Construction.planarRadial F) := by
  apply PlanarRadialCompact.Construction.planarRadial_compactSupport F (U + 1)
  intro t ht
  by_contra h
  have hle : t ≤ U := hF h
  linarith

theorem planarRadialTransferIntegrable_of_compact (b : ℝ) (F : ℝ → ℂ)
    (hF : ContDiff ℝ ∞ F) (U : ℝ) (hU : Function.support F ⊆ Iic U) :
    PlanarRadialTransfer.Construction.planarRadialTransferIntegrable b F (deriv F) (deriv (deriv F)) := by
  have hd : ContDiff ℝ ∞ (deriv F) := hF.iterate_deriv 1
  have hdd : ContDiff ℝ ∞ (deriv (deriv F)) := hF.iterate_deriv 2
  have hs1 : Function.support (deriv F) ⊆ Iic U :=
    support_deriv_subset.trans (closure_minimal hU isClosed_Iic)
  have hs2 : Function.support (deriv (deriv F)) ⊆ Iic U :=
    support_deriv_subset.trans (closure_minimal hs1 isClosed_Iic)
  have hc0 := PlanarRadialCompact.Construction.planarRadial_continuous F hF.continuous
  have hc1 := PlanarRadialCompact.Construction.planarRadial_continuous (deriv F) hd.continuous
  have hc2 := PlanarRadialCompact.Construction.planarRadial_continuous (deriv (deriv F)) hdd.continuous
  have hk0 := planarRadial_compactSupport_of_support_subset F U hU
  have hk1 := planarRadial_compactSupport_of_support_subset (deriv F) U hs1
  have hk2 := planarRadial_compactSupport_of_support_subset (deriv (deriv F)) U hs2
  have hcx : Continuous (PlanarRadialCompact.Construction.planarRadialX (deriv F)) := by
    change Continuous (fun z : ℝ × ℝ => ((2 * z.1 : ℝ) : ℂ) * PlanarRadialCompact.Construction.planarRadial (deriv F) z)
    fun_prop
  have hcy : Continuous (PlanarRadialCompact.Construction.planarRadialY (deriv F)) := by
    change Continuous (fun z : ℝ × ℝ => ((2 * z.2 : ℝ) : ℂ) * PlanarRadialCompact.Construction.planarRadial (deriv F) z)
    fun_prop
  have hcxx : Continuous (PlanarRadialCompact.Construction.planarRadialXX (deriv F) (deriv (deriv F))) := by
    change Continuous (fun z : ℝ × ℝ => 2 * PlanarRadialCompact.Construction.planarRadial (deriv F) z +
      ((4 * z.1 ^ 2 : ℝ) : ℂ) * PlanarRadialCompact.Construction.planarRadial (deriv (deriv F)) z)
    fun_prop
  have hcyy : Continuous (PlanarRadialCompact.Construction.planarRadialYY (deriv F) (deriv (deriv F))) := by
    change Continuous (fun z : ℝ × ℝ => 2 * PlanarRadialCompact.Construction.planarRadial (deriv F) z +
      ((4 * z.2 ^ 2 : ℝ) : ℂ) * PlanarRadialCompact.Construction.planarRadial (deriv (deriv F)) z)
    fun_prop
  have hkx : HasCompactSupport (PlanarRadialCompact.Construction.planarRadialX (deriv F)) := hk1.mul_left
  have hky : HasCompactSupport (PlanarRadialCompact.Construction.planarRadialY (deriv F)) := hk1.mul_left
  have hkxx : HasCompactSupport (PlanarRadialCompact.Construction.planarRadialXX (deriv F) (deriv (deriv F))) :=
    hk1.mul_left.add hk2.mul_left
  have hkyy : HasCompactSupport (PlanarRadialCompact.Construction.planarRadialYY (deriv F) (deriv (deriv F))) :=
    hk1.mul_left.add hk2.mul_left
  have hv := PlanarQuadraticPhase.Construction.planarQuadraticPhase_continuous b
  have hvx : Continuous (PlanarQuadraticPhase.Construction.planarQuadraticPhaseX b) := by unfold PlanarQuadraticPhase.Construction.planarQuadraticPhaseX; fun_prop
  have hvy : Continuous (PlanarQuadraticPhase.Construction.planarQuadraticPhaseY b) := by unfold PlanarQuadraticPhase.Construction.planarQuadraticPhaseY; fun_prop
  have hvxx : Continuous (PlanarQuadraticPhase.Construction.planarQuadraticPhaseXX b) := by unfold PlanarQuadraticPhase.Construction.planarQuadraticPhaseXX; fun_prop
  have hvyy : Continuous (PlanarQuadraticPhase.Construction.planarQuadraticPhaseYY b) := by unfold PlanarQuadraticPhase.Construction.planarQuadraticPhaseYY; fun_prop
  have hi (u v : ℝ × ℝ → ℂ) (hc : Continuous u) (hk : HasCompactSupport u) (hv : Continuous v) :
      Integrable (u * v) := (hc.mul hv).integrable_of_hasCompactSupport hk.mul_right
  exact ⟨hi _ _ hc0 hk0 hvxx, hi _ _ hcx hkx hvx, hi _ _ hcxx hkxx hv,
    hi _ _ hc0 hk0 hvx, hi _ _ hcx hkx hv, hi _ _ hc0 hk0 hvyy,
    hi _ _ hcy hky hvy, hi _ _ hcyy hkyy hv, hi _ _ hc0 hk0 hvy, hi _ _ hcy hky hv⟩

end

end OAI.RepresentationTheory.Weil.Local.PlanarCompactTransfer.Construction
