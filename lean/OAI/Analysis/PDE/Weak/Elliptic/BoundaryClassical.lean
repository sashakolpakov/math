import OAI.Analysis.PDE.Weak.Elliptic.BoundaryTrace
import OAI.Analysis.PDE.Weak.Elliptic.Classical.Equation
import OAI.Analysis.Normed.Function.Sobolev.HalfspaceRegularity

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- A genuine weak halfspace Dirichlet solution has a local classical
representative of any prescribed finite order at least two, satisfying both
the pointwise interior PDE and the pointwise zero boundary condition. -/
theorem halfspace_weak_solution_classical_dirichlet
    (j : Fin (m + 1))
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ ∞ A) {lam : ℝ} (hlam : 0 < lam)
    (q : ℕ) (hq : 2 ≤ q) {U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U)
    (hell : ∀ x ∈ U, ∀ z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (p : H1Pair m) (hp : p ∈ H1Zero {x | 0 < x j})
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hg : ContDiff ℝ ∞ g)
    (hfg : ∀ᵐ x ∂volume, x ∈ {x | 0 < x j} ∩ U → f x = g x)
    (he : WeakDivergenceEquation ({x | 0 < x j} ∩ U) (fun x ↦ A x (p.2 x)) f)
    {x₀ : OAI.Analysis.PDE.Variational.CellCoordinates m} (hx₀ : x₀ ∈ U) :
    ∃ (V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (w : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ),
      IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧ ContDiff ℝ q w ∧
      (∀ᵐ x ∂volume, x ∈ {x | 0 < x j} ∩ V → p.1 x = w x) ∧
      (∀ᵐ x ∂volume, x ∈ {x | 0 < x j} ∩ V → p.2 x = OAI.Analysis.PDE.Variational.cellGradient w x) ∧
      (∀ x ∈ {x | 0 < x j} ∩ V,
        -classicalDivergence (fun y ↦ A y (OAI.Analysis.PDE.Variational.cellGradient w y)) x = g x) ∧
      (∀ x ∈ V, x j = 0 → w x = 0) := by
  obtain ⟨V, w, hV, hxV, hVU, hw, heq⟩ :=
    OAI.Analysis.Normed.Function.Sobolev.halfspace_weak_solution_contDiff_representative
      j A hA hlam q hU hell p hp f g hg hfg he hx₀
  have hpall : p ∈ H1Zero univ := by
    apply closure_mono (s := smoothH1Graph {x | 0 < x j}) (t := smoothH1Graph univ) _ hp
    rintro v ⟨u, hu, hs, _, rfl⟩
    exact ⟨u, hu, hs, subset_univ _, rfl⟩
  have hsub : {x | 0 < x j} ∩ V ⊆ {x | 0 < x j} ∩ U :=
    fun _ hx ↦ ⟨hx.1, hVU hx.2⟩
  have heV : WeakDivergenceEquation ({x | 0 < x j} ∩ V) (fun x ↦ A x (p.2 x)) f := by
    intro φ hφ hs hφV
    exact he φ hφ hs (hφV.trans hsub)
  have hw2 : ContDiff ℝ 2 w := hw.of_le (by exact_mod_cast hq)
  obtain ⟨hgrad, hpde⟩ := classical_equation_of_H1_representative
    ((isOpen_lt continuous_const (continuous_apply j)).inter hV)
    A (hA.of_le (by simp)) p hpall f g hg.continuous
    (hfg.mono fun x hx hxs ↦ hx (hsub hxs)) heV w hw2 heq
  exact ⟨V, w, hV, hxV, hVU, hw, heq, hgrad, hpde,
    OAI.Analysis.PDE.Weak.H1Zero.halfspace_boundary_zero_on j hp hV hw.continuous.continuousOn heq⟩

end OAI.Analysis.PDE.Weak
