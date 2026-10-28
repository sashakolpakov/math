import OAI.Analysis.PDE.Weak.SobolevEllipticInterior
import OAI.Analysis.PDE.Weak.Elliptic.Classical.Glue
import OAI.Analysis.PDE.Weak.Elliptic.Classical.Locality

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- A genuine weak H¹ solution with smooth coefficients and smooth load has
one smooth interior representative satisfying the pointwise classical PDE. -/
theorem smooth_classical_representative_of_weak_solution
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ ∞ A) {lam : ℝ} (hlam : 0 < lam)
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω)
    (hell : ∀ x ∈ Ω, ∀ z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (p : H1Pair m) (hp : p ∈ H1Zero univ)
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hg : ContDiff ℝ ∞ g)
    (hfg : ∀ᵐ x ∂volume, x ∈ Ω → f x = g x)
    (he : WeakDivergenceEquation Ω (fun y ↦ A y (p.2 y)) f) :
    ∃ u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ, ContDiffOn ℝ ∞ u Ω ∧
      (∀ᵐ y ∂volume, y ∈ Ω → u y = p.1 y) ∧
      (∀ x ∈ Ω, -classicalDivergence (fun y ↦ A y (OAI.Analysis.PDE.Variational.cellGradient u y)) x = g x) := by
  have hlocal (q : ℕ) (x : OAI.Analysis.PDE.Variational.CellCoordinates m) (hx : x ∈ Ω) :=
    smooth_elliptic_contDiff_local_representative q A hA hlam hΩ hell p hp f g hg hfg he hx
  obtain ⟨u, hu, hue⟩ := exists_smoothOn_representative hΩ p.1 hlocal
  refine ⟨u, hu, hue, ?_⟩
  intro x hx
  obtain ⟨V, v, hV, hxV, hVΩ, hv, hfv⟩ := hlocal 2 x hx
  have hfgV : ∀ᵐ y ∂volume, y ∈ V → f y = g y :=
    hfg.mono fun y hy hys ↦ hy (hVΩ hys)
  have heV : WeakDivergenceEquation V (fun y ↦ A y (p.2 y)) f :=
    OAI.Analysis.PDE.Variational.weakEquation_congr_on he hVΩ (Eventually.of_forall fun _ _ ↦ rfl)
      (Eventually.of_forall fun _ _ ↦ rfl)
  have hvPDE := classical_equation_of_H1_representative hV A (hA.of_le (by simp))
    p hp f g hg.continuous hfgV heV v hv hfv
  have heq : EqOn u v V := by
    apply continuous_eqOn_of_local_ae hV (hu.continuousOn.mono hVΩ) hv.continuous.continuousOn
    filter_upwards [hue, hfv] with y hy hz
    intro hys
    exact (hy (hVΩ hys)).trans (hz hys)
  have hevent : u =ᶠ[𝓝 x] v := Filter.eventuallyEq_of_mem (hV.mem_nhds hxV) heq
  rw [classical_elliptic_operator_congr A hevent]
  exact hvPDE.2 x hxV

end OAI.Analysis.PDE.Weak
