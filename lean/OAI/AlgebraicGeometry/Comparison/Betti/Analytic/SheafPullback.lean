import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.OpenPullback
import OAI.AlgebraicGeometry.Comparison.Betti.SingularGlobalNaturality

/-! # Sheaf Pullback -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytic.SheafPullback.Smooth

noncomputable section

/-! Actual smooth pullback descends to the analytic de Rham sheaf complex. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : TopCat.{0}} [ChartedSpace E M] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  (f : M ⟶ N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)

def analyticFormDirectImage (n : ℕ) :
    (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf F N n : ConstantSheafSections.ComplexSheaves N) ⟶
      (TopologicalSheafPullback.sheafDirectImage f).obj (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M n) where
  hom :=
    { app := fun U => (OpenPullback.Smooth.analyticOpenPullback f hf U.unop).f n
      naturality := fun _U _V i => congrArg (fun k => k.f n)
        (OpenPullback.Smooth.analyticOpenPullback_restrict f hf (leOfHom i.unop)) }

def analyticDeRhamDirectImage :
    (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex F N : CochainComplex (ConstantSheafSections.ComplexSheaves N) ℕ) ⟶
      ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M) where
  f n := analyticFormDirectImage f hf n
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    have h := (OpenPullback.Smooth.analyticOpenPullback f hf U.unop).comm i (i + 1)
    change (OpenPullback.Smooth.analyticOpenPullback f hf U.unop).f i ≫
        ((Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M).d i (i + 1)).hom.app (op ((Opens.map f).obj U.unop)) =
      ((Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex F N).d i (i + 1)).hom.app U ≫
        (OpenPullback.Smooth.analyticOpenPullback f hf U.unop).f (i + 1)
    erw [Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex_d E M i, Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex_d F N i]
    simpa only [Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamComplex_d] using! h

def analyticDeRhamPullback :
    ((TopologicalSheafPullback.sheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex F N) ⟶
      (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M : CochainComplex (ConstantSheafSections.ComplexSheaves M) ℕ) :=
  ((SingularGlobalNaturality.sheafImageCochainAdjunction f).homEquiv
    (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex F N) (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M)).symm
      (analyticDeRhamDirectImage f hf)

theorem analyticDeRhamPullback_normalization :
    (SingularGlobalNaturality.sheafImageCochainAdjunction f).homEquiv _ _ (analyticDeRhamPullback f hf) =
      analyticDeRhamDirectImage f hf :=
  (SingularGlobalNaturality.sheafImageCochainAdjunction f).homEquiv _ _ |>.apply_symm_apply _

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytic.SheafPullback.Smooth
