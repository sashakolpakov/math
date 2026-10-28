import OAI.RepresentationTheory.Theta.Geometric.Dual.TensorEvaluation
import OAI.RepresentationTheory.Theta.Geometric.OpenRegularFunctionValues
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! # Section Evaluation -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.SectionEvaluation

noncomputable section

section

/-! Infinitesimal coefficients of scalar-extended affine regular
functions are holomorphic along actual native period maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints
open scoped TensorProduct _root_.Manifold

theorem affineNativePointEquiv_regularFunctionValue (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (r : Γ(X.left, ⊤)) :
    AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p r = RegularFunctionContinuity.regularFunctionValue X r p :=
  AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv_eval X p r

theorem nativeDualTensorEvaluation_snd_differentiable
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] [IsIntegral X.left] [Smooth X.hom]
    (p : V → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (hp : MDifferentiable (𝓘(ℂ, V))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p)
    (u : DualNumber ℂ ⊗[ℂ] Γ(X.left, ⊤)) :
    Differentiable ℂ (fun z => (TensorEvaluation.dualTensorEvaluation (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X (p z)) u).snd) := by
  apply TensorEvaluation.dualTensorEvaluation_snd_differentiable
  intro r
  have heq : (fun z => AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X (p z) r) = RegularFunctionContinuity.regularFunctionValue X r ∘ p :=
    funext (fun z => affineNativePointEquiv_regularFunctionValue X (p z) r)
  rw [heq]
  intro z
  exact (((OpenRegularFunctionValues.regularFunctionValue_contMDiff X r 1).mdifferentiableAt one_ne_zero).comp z (hp z)).differentiableAt

end

/-! Actual global regular sections evaluated on dual-number scheme
points, and their infinitesimal holomorphy on scalar-extended affine charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints
open scoped TensorProduct _root_.Manifold

def dualGlobalSectionValue {X : Scheme} (p : Spec (.of (DualNumber ℂ)) ⟶ X) :
    Γ(X, ⊤) →+* DualNumber ℂ :=
  (Scheme.ΓSpecIso (.of (DualNumber ℂ))).hom.hom.comp p.appTop.hom

theorem dualGlobalSectionValue_spec {R : Type} [CommRing R] (f : R →+* DualNumber ℂ)
    (s : Γ(Spec (.of R), ⊤)) :
    dualGlobalSectionValue (Spec.map (CommRingCat.ofHom f)) s = f ((Scheme.ΓSpecIso (.of R)).hom s) := by
  have H := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)) s
  exact H

theorem dualGlobalSectionValue_pullback {X Y : Scheme}
    (p : Spec (.of (DualNumber ℂ)) ⟶ X) (f : X ⟶ Y) (s : Γ(Y, ⊤)) :
    dualGlobalSectionValue (p ≫ f) s = dualGlobalSectionValue p (f.appTop s) := by
  simp only [dualGlobalSectionValue, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]

theorem dualAffineSectionValue_snd_differentiable
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] [IsIntegral X.left] [Smooth X.hom]
    (p : V → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (hp : MDifferentiable (𝓘(ℂ, V))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p)
    (s : Γ(Spec (.of (DualNumber ℂ ⊗[ℂ] Γ(X.left, ⊤))), ⊤)) :
    Differentiable ℂ (fun z => (dualGlobalSectionValue
      (Spec.map (CommRingCat.ofHom (TensorEvaluation.dualTensorEvaluation (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X (p z))).toRingHom)) s).snd) := by
  simp only [dualGlobalSectionValue_spec, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  exact nativeDualTensorEvaluation_snd_differentiable X p hp
    ((Scheme.ΓSpecIso (.of (DualNumber ℂ ⊗[ℂ] Γ(X.left, ⊤)))).hom s)

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.SectionEvaluation
