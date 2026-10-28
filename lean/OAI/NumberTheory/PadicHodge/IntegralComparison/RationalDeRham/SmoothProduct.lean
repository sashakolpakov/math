import OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.WedgeNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.SymbolProducts
import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.Adapter

/-! # Smooth Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.SmoothProduct.Wedge

noncomputable section

/-! The actual comparison from algebraic differential forms to smooth
forms preserves exterior multiplication in every degree. -/

open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.SymbolProducts.Betti

variable {E M A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CommRing A] [Algebra ℂ A]
  (φ : A →ₐ[ℂ] C(M, ℂ))
  (hφ : ∀ a : A, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (φ a))

local instance : Algebra ℚ A := Algebra.compHom A (algebraMap ℚ ℂ)

def smoothMap (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form ℂ A n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n :=
  (AlgebraicGeometry.Comparison.Betti.Smooth.CochainMap.smoothFormMap φ hφ n).comp (GeometricComparison.Forms.Adapter.FormsAdapter.to66 A n)

@[simp] theorem smoothMap_symbol (n : ℕ) (a : A) (v : Fin n → A) :
    smoothMap φ hφ n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A a v) = AlgebraicGeometry.Comparison.Betti.HigherSmoothSymbols.smoothSymbol φ hφ n (Fin.cons a v) := by
  simp only [smoothMap, LinearMap.comp_apply, GeometricComparison.Forms.Adapter.FormsAdapter.to66_symbol,
    AlgebraicGeometry.Comparison.Betti.Smooth.CochainMap.smoothFormMap_symbol]

theorem smoothMap_differential (n : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form ℂ A n) :
    smoothMap φ hφ (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential ℂ A n x) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (smoothMap φ hφ n x) := by
  unfold smoothMap
  simp only [LinearMap.comp_apply, GeometricComparison.Forms.Adapter.FormsAdapter.to66_differential,
    AlgebraicGeometry.Comparison.Betti.Smooth.CochainMap.smoothFormMap_d]

def smoothWedge (p q : ℕ) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p →ₗ[ℂ]
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M q →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + q) :=
  LinearMap.mk₂ ℂ AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge
    (fun x x' y => AlgebraicGeometry.Comparison.Betti.Smooth.Wedge.manifoldWedge_add_left x x' y)
    (fun c x y => AlgebraicGeometry.Comparison.Betti.Smooth.Wedge.manifoldWedge_smul_left c x y)
    (fun x y y' => AlgebraicGeometry.Comparison.Betti.Smooth.Wedge.manifoldWedge_add_right x y y')
    (fun c x y => AlgebraicGeometry.Comparison.Betti.Smooth.Wedge.manifoldWedge_smul_right c x y)

theorem smoothMap_wedge (p q : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form ℂ A p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form ℂ A q) :
    smoothMap φ hφ (p + q) (Wedge.wedge ℂ A p q x y) =
      AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge (smoothMap φ hφ p x) (smoothMap φ hφ q y) := by
  let L : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form ℂ A p →ₗ[ℂ] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form ℂ A q →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + q) :=
    ((Wedge.wedge ℂ A p q).restrictScalars₁₂ ℂ ℂ).compr₂ (smoothMap φ hφ (p + q))
  let D : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form ℂ A p →ₗ[ℂ] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form ℂ A q →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + q) :=
    (smoothWedge p q).compl₁₂ (smoothMap φ hφ p) (smoothMap φ hφ q)
  have h : L = D := by
    apply Leibniz.Wedge.linearMap_ext_symbols ℂ A p
    intro a v
    apply Leibniz.Wedge.linearMap_ext_symbols ℂ A q
    intro b w
    change smoothMap φ hφ (p + q) (Wedge.wedge ℂ A p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A a v) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A b w)) =
      AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge (smoothMap φ hφ p (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A a v))
        (smoothMap φ hφ q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol ℂ A b w))
    rw [Wedge.wedge_symbol, smoothMap_symbol, smoothMap_symbol, smoothMap_symbol]
    exact (Smooth.SymbolProducts.Betti.smoothSymbol_product φ hφ p q a b v w).symm
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.SmoothProduct.Wedge
