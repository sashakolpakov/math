import OAI.Analysis.Normed.Function.Sobolev.HalfspaceEmbedding
import OAI.Analysis.PDE.Weak.Boundary.Halfspace.Family

open Set Filter _root_.MeasureTheory
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.Normed.Function.Sobolev

open OAI.Analysis.PDE.Weak OAI.Analysis.PDE.Variational

/-- A true weak Dirichlet solution with smooth coefficients and load has
representatives of every finite differentiability order across the flat
boundary, locally agreeing with the solution on the open halfspace. -/
theorem halfspace_weak_solution_contDiff_representative
    {m : ℕ} (k : Fin (m + 1))
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ ∞ A) {lam : ℝ} (hlam : 0 < lam)
    (q : ℕ) {U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U)
    (hell : ∀x ∈ U, ∀z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (p : OAI.Analysis.PDE.Weak.H1Pair m) (hp : p ∈ OAI.Analysis.PDE.Weak.H1Zero {x | 0 < x k})
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hg : ContDiff ℝ ∞ g)
    (hfg : ∀ᵐx, x ∈ {x | 0 < x k} ∩ U → f x = g x)
    (he : OAI.Analysis.PDE.Weak.WeakDivergenceEquation ({x | 0 < x k} ∩ U) (fun x ↦ A x (p.2 x)) f)
    {x₀ : OAI.Analysis.PDE.Variational.CellCoordinates m} (hx₀ : x₀ ∈ U) :
    ∃(V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (w : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ),
      IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧ ContDiff ℝ q w ∧
      ∀ᵐx, x ∈ {x | 0 < x k} ∩ V → p.1 x = w x := by
  obtain ⟨V,K,F,hV,hxV,hVU,hK,_hKU,hFeq,hFs,hFd⟩ :=
    OAI.Analysis.PDE.Weak.halfspace_smooth_derivative_family k A hA hlam (m + q) hU hell p hp f g hg hfg he hx₀
  obtain ⟨w,hw,hweq⟩ := exists_contDiff_halfspace_representative_of_compact_L2_derivatives
    k (show m + 1 + q < m + q + 2 by omega) F hK hFs hFd
  refine ⟨V,w,hV,hxV,hVU,hw,?_⟩
  filter_upwards [hFeq,hweq] with x hxF hxw
  intro hx
  exact (hxF hx.2).symm.trans (hxw hx.1)

end OAI.Analysis.Normed.Function.Sobolev
