import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Product
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.ReductionCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.FunctionsBaseChange

/-! # Coefficient Reduction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.CoefficientReduction

noncomputable section

/-! The constant coordinate on each actual affine family open is
the original structure-sheaf restriction along the reduction morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] [IsReduced X.left]
    (U : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (hU : IsAffineOpen U)

theorem dualOpenSectionCoefficientEquiv_fst (s : Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, U)) :
    (SectionEquivalence.dualOpenSectionCoefficientEquiv X U hU s).fst = (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.app U s := by
  let : IsAffine (Product.dualReducedOpenOver X U).left := Dual.ReductionOpens.dualAffineOpen_reduction X U hU
  let : LocallyOfFiniteType (Product.dualReducedOpenOver X U).hom := by
    change LocallyOfFiniteType (((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).ι ≫ X.hom)
    infer_instance
  let : IsReduced (Product.dualReducedOpenOver X U).left :=
    inferInstanceAs (IsReduced ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).toScheme)
  change ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).topIso.hom
    (DualAffine.SectionCoefficients.dualAffineSectionCoefficients (Product.dualReducedOpenOver X U)
      ((Product.dualOpenProductIso X U).hom.appTop (U.topIso.inv s))).fst = _
  rw [DualAffine.ReductionCoefficients.dualAffineSectionCoefficients_fst]
  have hp := congrArg (fun f : (Product.dualReducedOpenOver X U).left ⟶ U.toScheme =>
    ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).topIso.hom (f.appTop (U.topIso.inv s)))
      (Product.dualOpenProductIso_reduction X U)
  refine hp.trans ?_
  have h := ConcreteCategory.congr_hom
    (HilbertConstruction.Open.FunctionsBaseChange.morphismRestrict_appTop_topIso (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left U) (U.topIso.inv s)
  change ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).topIso.hom
      ((Product.dualOpenReduction X U).appTop (U.topIso.inv s)) =
    (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.app U (U.topIso.hom (U.topIso.inv s)) at h
  exact h.trans (congrArg ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.app U)
    (Iso.inv_hom_id_apply U.topIso s))

theorem dualOpenUnit_normalized (u : Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, U)ˣ)
    (hu : (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.app U u.val = 1) :
    (Units.map (SectionEquivalence.dualOpenSectionCoefficientEquiv X U hU).toMonoidHom u).val.fst = 1 :=
  (dualOpenSectionCoefficientEquiv_fst X U hU u.val).trans hu

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.CoefficientReduction
