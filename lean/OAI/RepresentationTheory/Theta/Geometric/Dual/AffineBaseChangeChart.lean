import OAI.RepresentationTheory.Theta.Geometric.Dual.TensorPointDiagram
import OAI.RepresentationTheory.Theta.Geometric.Dual.TensorLocalHolomorphic
import OAI.RepresentationTheory.Theta.Geometric.Dual.SectionEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Lifts
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Affine Base Change Chart -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart

noncomputable section

section

/-! The tensor chart for a native affine base change evaluates at exactly
the actual constant dual-number point, including both projections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct _root_.Manifold

def dualConstantPoint (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X :=
  lift (𝟙 _) (toUnit _ ≫ p)

theorem dualConstantPoint_natural {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    dualConstantPoint X p ≫ (𝟙 (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ⊗ₘ f) =
      dualConstantPoint Y (p ≫ f) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [dualConstantPoint]

theorem dualTensorPoint_constant {A : Type} [CommRing A] [Algebra ℂ A]
    (p : A →ₐ[ℂ] ℂ) :
    TensorPointDiagram.dualTensorPoint p ≫ (pullbackSpecIso ℂ (DualNumber ℂ) A).inv =
      (dualConstantPoint (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A) (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv A p)).left := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((TensorPointDiagram.dualTensorPoint_first p).trans
      (congrArg Over.Hom.left (lift_fst (𝟙 (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ))
        (toUnit (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv A p))).symm)
  · have H := TensorPointDiagram.dualTensorPoint_second p
    have hp : Spec.map (CommRingCat.ofHom ((Algebra.ofId ℂ (DualNumber ℂ)).comp p).toRingHom) =
        (toUnit (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv A p).left := by
      change Spec.map (CommRingCat.ofHom ((algebraMap ℂ (DualNumber ℂ)).comp p.toRingHom)) = _
      exact Spec.map_comp (CommRingCat.ofHom p.toRingHom)
        (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)))
    exact (Category.assoc _ _ _).trans (H.trans (hp.trans
      (congrArg Over.Hom.left (lift_snd (𝟙 (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ))
        (toUnit (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv A p))).symm))

def dualAffineBaseChangeChart (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] :
    Spec (.of (DualNumber ℂ ⊗[ℂ] Γ(X.left, ⊤))) ⟶ (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left :=
  (pullbackSpecIso ℂ (DualNumber ℂ) Γ(X.left, ⊤)).inv ≫
    (𝟙 (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ⊗ₘ (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv).left

theorem dualAffineBaseChangeChart_point (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    TensorPointDiagram.dualTensorPoint (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p) ≫ dualAffineBaseChangeChart X =
      (dualConstantPoint X p).left := by
  have H := congrArg (fun f => f ≫ (𝟙 (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ⊗ₘ (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv).left)
    (dualTensorPoint_constant (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p))
  have hn := congrArg Over.Hom.left (dualConstantPoint_natural (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv
    (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv Γ(X.left, ⊤) (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p)))
  have hp : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv Γ(X.left, ⊤) (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p) ≫
      (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv = p := (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X).symm_apply_apply p
  exact (Category.assoc _ _ _).symm.trans (H.trans (hn.trans
    (congrArg (fun q => (dualConstantPoint X q).left) hp)))

end

/-! Actual regular functions on the native affine base change have
holomorphic constant and infinitesimal coefficients along period maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct _root_.Manifold

theorem dualConstantPoint_sectionValue (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (s : Γ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left, ⊤)) :
    SectionEvaluation.dualGlobalSectionValue (dualConstantPoint X p).left s =
      TensorEvaluation.dualTensorEvaluation (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p)
        ((Scheme.ΓSpecIso (.of (DualNumber ℂ ⊗[ℂ] Γ(X.left, ⊤)))).hom
          ((dualAffineBaseChangeChart X).appTop s)) := by
  have H := congrArg (fun f => SectionEvaluation.dualGlobalSectionValue f s) (dualAffineBaseChangeChart_point X p)
  exact H.symm.trans ((SectionEvaluation.dualGlobalSectionValue_pullback _ (dualAffineBaseChangeChart X) s).trans
    (SectionEvaluation.dualGlobalSectionValue_spec _ ((dualAffineBaseChangeChart X).appTop s)))

theorem dualConstantPoint_sectionValue_differentiableAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] [IsIntegral X.left] [Smooth X.hom]
    (p : V → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z : V)
    (hp : MDifferentiableAt (𝓘(ℂ, V))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p z)
    (s : Γ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left, ⊤)) :
    CoefficientHolomorphic.DualCoefficientDifferentiableAt
      (fun w => SectionEvaluation.dualGlobalSectionValue (dualConstantPoint X (p w)).left s) z := by
  have heq := funext (fun w => dualConstantPoint_sectionValue X (p w) s)
  rw [heq]
  exact TensorLocalHolomorphic.nativeDualTensorEvaluation_coefficients_differentiableAt X p z hp _

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart
