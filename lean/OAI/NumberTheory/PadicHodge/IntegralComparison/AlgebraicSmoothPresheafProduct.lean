import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SmoothProducts
import OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.CechCup
import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafFormsAdapter
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap

/-! # Algebraic Smooth Presheaf Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraicSmoothPresheafProduct

noncomputable section

/-! The original algebraic-to-smooth morphism of presheaf complexes
preserves the actual local exterior products. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.Manifold ContDiff

variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

attribute [local instance] AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.sectionAlgebra

local instance sectionRational (U : X.left.Opens) : Algebra ℚ Γ(X.left, U) :=
  Algebra.compHom Γ(X.left, U) (algebraMap ℚ ℂ)

def nativeMap : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex ℂ X ⟶ AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X :=
  (GeometricComparison.SheafFormsAdapter.FormsAdapter.presheafComplexIso X).inv ≫ AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.presheafSmoothCochainMap X

def pairing (p q : ℕ) (U : X.left.Opensᵒᵖ) :
    ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X p).obj U →ₗ[ℂ]
      ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X q).obj U →ₗ[ℂ]
        ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X (p + q)).obj U :=
  Open.SmoothProducts.wedge (AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U.unop) p q

theorem pairing_natural (p q : ℕ) {U V : X.left.Opensᵒᵖ} (f : U ⟶ V)
    (x : ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X p).obj U)
    (y : ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X q).obj U) :
    ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X (p + q)).map f (pairing X p q U x y) =
      pairing X p q V (((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X p).map f x)
        (((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X q).map f y) :=
  Open.SmoothProducts.wedge_restrict _ (AlgebraicGeometry.Comparison.Betti.Open.SmoothForms.analyticOpen_mono X (leOfHom f.unop)) p q x y

theorem nativeMap_app (n : ℕ) (U : X.left.Opensᵒᵖ)
    (x : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf ℂ X n).obj U) :
    ((nativeMap X).f n).app U x =
      (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U.unop) n).symm
        (RationalDeRham.SmoothProduct.Wedge.smoothMap (AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.sectionEvaluationOn X U.unop)
          (AlgebraicGeometry.Comparison.Betti.Open.SmoothEvaluation.sectionEvaluationOn_smooth X U.unop) n x) := rfl

theorem nativeMap_pairing (p q : ℕ) (U : X.left.Opensᵒᵖ)
    (x : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf ℂ X p).obj U)
    (y : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf ℂ X q).obj U) :
    ((nativeMap X).f (p + q)).app U (RationalDeRham.CechCup.sectionPairing ℂ X p q U x y) =
      pairing X p q U (((nativeMap X).f p).app U x) (((nativeMap X).f q).app U y) := by
  rw [nativeMap_app, nativeMap_app, nativeMap_app]
  change (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U.unop) (p + q)).symm
    (RationalDeRham.SmoothProduct.Wedge.smoothMap (AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.sectionEvaluationOn X U.unop)
      (AlgebraicGeometry.Comparison.Betti.Open.SmoothEvaluation.sectionEvaluationOn_smooth X U.unop) (p + q)
      (RationalDeRham.Wedge.wedge ℂ Γ(X.left, U.unop) p q x y)) = _
  exact (congrArg
    (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U.unop) (p + q)).symm
    (RationalDeRham.SmoothProduct.Wedge.smoothMap_wedge (AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.sectionEvaluationOn X U.unop)
      (AlgebraicGeometry.Comparison.Betti.Open.SmoothEvaluation.sectionEvaluationOn_smooth X U.unop) p q x y)).trans
    (Open.SmoothProducts.intrinsic_symm_wedge _ p q _ _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraicSmoothPresheafProduct
