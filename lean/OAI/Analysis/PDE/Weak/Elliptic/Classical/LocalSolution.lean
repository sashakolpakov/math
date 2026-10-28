import OAI.Analysis.PDE.Weak.Elliptic.Classical.Solution

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- Local H¹ representatives, including representatives coming from overlapping
periodic cells, determine one smooth classical solution on the entire interior. -/
theorem smooth_classical_representative_of_local_weak_solution
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ ∞ A) {lam : ℝ} (hlam : 0 < lam)
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω)
    (hell : ∀ x ∈ Ω, ∀ z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (w g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hg : ContDiff ℝ ∞ g)
    (hlocal : ∀ x ∈ Ω, ∃ (U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (p : H1Pair m)
      (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))),
      IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧ p ∈ H1Zero univ ∧
      (∀ᵐ y ∂volume, y ∈ U → p.1 y = w y) ∧
      (∀ᵐ y ∂volume, y ∈ U → f y = g y) ∧
      WeakDivergenceEquation U (fun y ↦ A y (p.2 y)) f) :
    ∃ u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ, ContDiffOn ℝ ∞ u Ω ∧
      (∀ᵐ y ∂volume, y ∈ Ω → u y = w y) ∧
      (∀ x ∈ Ω, -classicalDivergence (fun y ↦ A y (OAI.Analysis.PDE.Variational.cellGradient u y)) x = g x) := by
  have hreps (q : ℕ) (x : OAI.Analysis.PDE.Variational.CellCoordinates m) (hx : x ∈ Ω) :
      ∃ (V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ),
        IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ ContDiff ℝ q v ∧
          (∀ᵐ y ∂volume, y ∈ V → w y = v y) := by
    obtain ⟨U, p, f, hU, hxU, hUΩ, hp, hpw, hfg, he⟩ := hlocal x hx
    obtain ⟨V, v, hV, hxV, hVU, hv, hpv⟩ := smooth_elliptic_contDiff_local_representative
      q A hA hlam hU (fun y hy z ↦ hell y (hUΩ hy) z) p hp f g hg hfg he hxU
    refine ⟨V, v, hV, hxV, hVU.trans hUΩ, hv, ?_⟩
    filter_upwards [hpw, hpv] with y hy hz
    intro hys
    exact (hy (hVU hys)).symm.trans (hz hys)
  obtain ⟨u, hu, hue⟩ := exists_smoothOn_representative hΩ w hreps
  refine ⟨u, hu, hue, ?_⟩
  intro x hx
  obtain ⟨U, p, f, hU, hxU, hUΩ, hp, hpw, hfg, he⟩ := hlocal x hx
  obtain ⟨V, v, hV, hxV, hVU, hv, hpv⟩ := smooth_elliptic_contDiff_local_representative
    2 A hA hlam hU (fun y hy z ↦ hell y (hUΩ hy) z) p hp f g hg hfg he hxU
  have hfgV : ∀ᵐ y ∂volume, y ∈ V → f y = g y :=
    hfg.mono fun y hy hys ↦ hy (hVU hys)
  have heV : WeakDivergenceEquation V (fun y ↦ A y (p.2 y)) f :=
    OAI.Analysis.PDE.Variational.weakEquation_congr_on he hVU (Eventually.of_forall fun _ _ ↦ rfl)
      (Eventually.of_forall fun _ _ ↦ rfl)
  have hvPDE := classical_equation_of_H1_representative hV A (hA.of_le (by simp))
    p hp f g hg.continuous hfgV heV v hv hpv
  have heq : EqOn u v V := by
    apply continuous_eqOn_of_local_ae hV
      (hu.continuousOn.mono (hVU.trans hUΩ)) hv.continuous.continuousOn
    filter_upwards [hue, hpw, hpv] with y hy hz ht
    intro hys
    exact (hy (hUΩ (hVU hys))).trans ((hz (hVU hys)).symm.trans (ht hys))
  have hevent : u =ᶠ[𝓝 x] v := Filter.eventuallyEq_of_mem (hV.mem_nhds hxV) heq
  rw [classical_elliptic_operator_congr A hevent]
  exact hvPDE.2 x hxV

end OAI.Analysis.PDE.Weak
