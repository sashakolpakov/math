import OAI.AlgebraicGeometry.Comparison.Betti.RegularFunctions
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves

/-! # Section Algebra -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.SectionAlgebra

noncomputable section

/-! The canonical spectrum-of-sections isomorphism respects the original complex scalars. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

def affineGlobalSectionAlgEquiv (A : CommAlgCat.{0} ℂ) :
    Γ((Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A).left, ⊤) ≃ₐ[ℂ] A where
  toRingEquiv := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  commutes' c := by
    let k := CommRingCat.ofHom (algebraMap ℂ A)
    have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality k)
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      ((Spec.map k).appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) =
        k ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
          ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) at h
    rw [Iso.inv_hom_id_apply] at h
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      ((Spec.map k).appLE ⊤ ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) =
        algebraMap ℂ A c
    erw [← (Spec.map k).app_eq_appLE (U := ⊤)]
    exact h

def affineTestSectionPullback {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (A : CommAlgCat.{0} ℂ)
    (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) : Γ(X.left, ⊤) →ₐ[ℂ] A :=
  (affineGlobalSectionAlgEquiv A).toAlgHom.comp (Algebraic.Sheaves.sectionPullback f ⊤)

theorem affineTestSectionPullback_evaluation {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (A : CommAlgCat.{0} ℂ)
    (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (p : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (s : Γ(X.left, ⊤)) :
    p (affineTestSectionPullback A f s) =
      RegularFunctions.globalEvaluation (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A f p) s :=
  (RegularFunctions.globalEvaluation_affine A p (f.left.appTop s)).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.SectionAlgebra
