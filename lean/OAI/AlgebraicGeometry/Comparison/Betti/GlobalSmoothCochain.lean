import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.CochainNaturality

/-! # Global Smooth Cochain -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.GlobalSmoothCochain

noncomputable section

/-! The constructed cochain map on actual smooth complex varieties. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

/-- Every algebraic differential form on global sections is realized smoothly. -/
def globalSmoothFormMap (n : ℕ) : Algebraic.Forms.Form Γ(X.left, ⊤) n →ₗ[ℂ]
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) n :=
  Betti.Smooth.CochainMap.smoothFormMap (RegularFunctions.globalSectionContinuousAlgHom X)
    (fun s => RegularSmoothness.globalEvaluation_real_contMDiff X s ∞) n

/-- The actual algebraic-to-smooth map of global section complexes. -/
def globalSmoothCochainMap : Algebraic.Forms.algebraicDeRhamComplex Γ(X.left, ⊤) ⟶
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
  Betti.Smooth.CochainMap.smoothCochainMap (RegularFunctions.globalSectionContinuousAlgHom X)
    (fun s => RegularSmoothness.globalEvaluation_real_contMDiff X s ∞)

theorem globalSmoothFormMap_d (n : ℕ) (a : Algebraic.Forms.Form Γ(X.left, ⊤) n) :
    globalSmoothFormMap X (n + 1) (Algebraic.Forms.differential Γ(X.left, ⊤) n a) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (globalSmoothFormMap X n a) :=
  Betti.Smooth.CochainMap.smoothFormMap_d (RegularFunctions.globalSectionContinuousAlgHom X)
    (fun s => RegularSmoothness.globalEvaluation_real_contMDiff X s ∞) n a

variable {X} {Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral Y.left] [Smooth Y.hom]

/-- Naturality follows from actual evaluation and manifold pullback in every degree. -/
theorem globalSmoothCochainMap_naturality (f : X ⟶ Y) :
    Algebraic.Forms.complexPullback (Algebraic.Sheaves.sectionPullback f ⊤) ≫ globalSmoothCochainMap X =
      globalSmoothCochainMap Y ≫ Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)
        (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map f ∞) :=
  Betti.Smooth.CochainNaturality.smoothCochainMap_naturality (RegularFunctions.globalSectionContinuousAlgHom X)
    (fun s => RegularSmoothness.globalEvaluation_real_contMDiff X s ∞) (RegularFunctions.globalSectionContinuousAlgHom Y)
    (fun s => RegularSmoothness.globalEvaluation_real_contMDiff Y s ∞) (Algebraic.Sheaves.sectionPullback f ⊤)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map f ∞)
    (fun _ _ => rfl)

end

end OAI.AlgebraicGeometry.Comparison.Betti.GlobalSmoothCochain
