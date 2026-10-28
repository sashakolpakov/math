import OAI.RepresentationTheory.Theta.Geometric.Complex.PointsDetectSections
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.TopSectionValues
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints

/-! # Coefficient Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.CoefficientDetection

noncomputable section

/-! Complex algebra characters detect elements of a reduced algebra
of finite type. The proof uses the actual regular-section evaluations
on its affine scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints

variable (C : Type) [CommRing C] [Algebra ℂ C]

theorem complexCoefficientSectionValue (q : C →ₐ[ℂ] ℂ) (a : C) :
    RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue (Spec.map (CommRingCat.ofHom q.toRingHom)) ⊤ (by trivial)
      ((Scheme.ΓSpecIso (.of C)).inv a) = q a := by
  rw [TopSectionValues.complexSectionValue_top_formula]
  have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom q.toRingHom))
    ((Scheme.ΓSpecIso (.of C)).inv a)
  have hi : (Scheme.ΓSpecIso (.of C)).hom ((Scheme.ΓSpecIso (.of C)).inv a) = a :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of C)).inv_hom_id a
  exact h.trans (congrArg q hi)

theorem complexCoefficientCharacters_ext [Algebra.FiniteType ℂ C] [IsReduced C]
    (a b : C) (h : ∀ q : C →ₐ[ℂ] ℂ, q a = q b) : a = b := by
  let X := Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ C
  have : LocallyOfFiniteType X.hom := by
    change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℂ C)))
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr (inferInstanceAs (Algebra.FiniteType ℂ C)))
  have : IsReduced X.left := inferInstanceAs (IsReduced (Spec (.of C)))
  have hs : (Scheme.ΓSpecIso (.of C)).inv a = (Scheme.ΓSpecIso (.of C)).inv b := by
    apply RepresentationTheory.Theta.Geometric.Complex.PointsDetectSections.complexSectionValue_top_ext X
    intro p
    obtain ⟨q, rfl⟩ := (Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv C).surjective p
    change RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue (X := Spec (.of C)) (Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv C q).left ⊤ (by trivial)
      ((Scheme.ΓSpecIso (.of C)).inv a) =
      RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue (X := Spec (.of C)) (Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv C q).left ⊤ (by trivial)
        ((Scheme.ΓSpecIso (.of C)).inv b)
    rw [Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv_left]
    exact (complexCoefficientSectionValue C q a).trans ((h q).trans (complexCoefficientSectionValue C q b).symm)
  exact (Scheme.ΓSpecIso (.of C)).commRingCatIsoToRingEquiv.symm.injective hs

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.CoefficientDetection
