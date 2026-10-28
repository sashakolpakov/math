import OAI.Analysis.PDE.Weak.Elliptic.Classical.Divergence
import OAI.Analysis.PDE.Weak.Elliptic.SmoothGradient
import OAI.Analysis.PDE.Weak.Elliptic.LocalH2

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem contDiff_one_cellGradient {u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hu : ContDiff ℝ 2 u) : ContDiff ℝ 1 (OAI.Analysis.PDE.Variational.cellGradient u) := by
  apply (contDiff_piLp 2).mpr
  intro i
  change ContDiff ℝ 1 (fun x ↦ fderiv ℝ u x (Pi.single i 1))
  exact (hu.fderiv_right (by norm_num)).clm_apply contDiff_const

/-- The C² representative of a genuine H¹ weak solution satisfies the
classical elliptic equation at every point, with its actual classical gradient. -/
theorem classical_equation_of_H1_representative
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω)
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m) (hA : ContDiff ℝ 1 A)
    (p : H1Pair m) (hp : p ∈ H1Zero univ)
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hg : Continuous g)
    (hfg : ∀ᵐ x ∂volume, x ∈ Ω → f x = g x)
    (he : WeakDivergenceEquation Ω (fun y ↦ A y (p.2 y)) f)
    (u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hu : ContDiff ℝ 2 u)
    (hpu : ∀ᵐ x ∂volume, x ∈ Ω → p.1 x = u x) :
    (∀ᵐ x ∂volume, x ∈ Ω → p.2 x = OAI.Analysis.PDE.Variational.cellGradient u x) ∧
      ∀ x ∈ Ω, -classicalDivergence (fun y ↦ A y (OAI.Analysis.PDE.Variational.cellGradient u y)) x = g x := by
  have hgrad := OAI.Analysis.PDE.Weak.H1Zero.gradient_eq_of_value_eq hΩ hp u (hu.of_le (by norm_num)) hpu
  refine ⟨hgrad, ?_⟩
  have he' : WeakDivergenceEquation Ω (fun y ↦ A y (OAI.Analysis.PDE.Variational.cellGradient u y)) g := by
    apply OAI.Analysis.PDE.Variational.weakEquation_congr_on he (subset_refl _)
    · filter_upwards [hgrad] with x hx
      intro hxs
      rw [hx hxs]
    · filter_upwards [hfg] with x hx
      exact fun hxs ↦ (hx hxs).symm
  exact he'.classical_eq hΩ (hA.clm_apply (contDiff_one_cellGradient hu)) hg

end OAI.Analysis.PDE.Weak
