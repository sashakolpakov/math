import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Scalars
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.CoefficientScalars

/-! # Coefficient Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.CoefficientScalars

noncomputable section

/-! On every actual affine family open, native scalar pullback fixes
the constant coefficient and scales the first-order regular coefficient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

theorem dualOpenSectionCoefficientEquiv_scalar (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [LocallyOfFiniteType X.hom] [IsReduced X.left]
    (U : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (hU : IsAffineOpen U) (c : ℂ)
    (s : Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, U)) :
    let : IsAffine (Product.dualReducedOpenOver X U).left := Dual.ReductionOpens.dualAffineOpen_reduction X U hU
    SectionEquivalence.dualOpenSectionCoefficientEquiv X U hU (Scalars.dualOpenScalarSection X U c s) =
      Dual.CoefficientScalars.dualCoefficientScale (((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).topIso.hom
        (algebraMap ℂ Γ((Product.dualReducedOpenOver X U).left, ⊤) c)) (SectionEquivalence.dualOpenSectionCoefficientEquiv X U hU s) := by
  let : IsAffine (Product.dualReducedOpenOver X U).left := Dual.ReductionOpens.dualAffineOpen_reduction X U hU
  let : LocallyOfFiniteType (Product.dualReducedOpenOver X U).hom := by
    change LocallyOfFiniteType (((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).ι ≫ X.hom)
    infer_instance
  let : IsReduced (Product.dualReducedOpenOver X U).left :=
    inferInstanceAs (IsReduced ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).toScheme)
  change Dual.NumberCoefficients.dualNumberRingMap _ (DualAffine.SectionCoefficients.dualAffineSectionCoefficients (Product.dualReducedOpenOver X U)
    ((Product.dualOpenProductIso X U).hom.appTop
      (U.topIso.inv (U.topIso.hom ((Scalars.dualOpenScalar X U c).appTop (U.topIso.inv s)))))) = _
  rw [Iso.hom_inv_id_apply]
  have h := congrArg (fun f : (LieRanks.dualNumberTest ℂ ⊗ Product.dualReducedOpenOver X U).left ⟶ U.toScheme =>
    f.appTop (U.topIso.inv s)) (Scalars.dualOpenProductIso_scalar X U c)
  change (Product.dualOpenProductIso X U).hom.appTop ((Scalars.dualOpenScalar X U c).appTop (U.topIso.inv s)) =
    (Dual.Scalars.dualFamilyScalar (Product.dualReducedOpenOver X U) c).left.appTop
      ((Product.dualOpenProductIso X U).hom.appTop (U.topIso.inv s)) at h
  rw [h, DualAffine.CoefficientScalars.dualAffineSectionCoefficients_scalar]
  exact Dual.CoefficientScalars.dualCoefficientScale_natural ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).topIso.hom.hom
    (algebraMap ℂ Γ((Product.dualReducedOpenOver X U).left, ⊤) c) _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.CoefficientScalars
