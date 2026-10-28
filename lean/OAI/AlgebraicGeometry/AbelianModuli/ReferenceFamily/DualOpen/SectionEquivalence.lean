import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Product
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberRingEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.SectionCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.LiftSectionMap

/-! # Section Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence

noncomputable section

/-! Regular sections on each actual affine open of the dual-number
family are exactly dual numbers over the regular sections of its reduction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens)

def dualOpenSectionCoefficientEquiv (hU : IsAffineOpen U) :
    Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, U) ≃+*
      DualNumber Γ(X.left, (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U) := by
  letI : IsAffine (Product.dualReducedOpenOver X U).left := Dual.ReductionOpens.dualAffineOpen_reduction X U hU
  letI : IsIso (Product.dualOpenProductIso X U).hom.appTop :=
    inferInstanceAs (IsIso (Scheme.Γ.map (Product.dualOpenProductIso X U).hom.op))
  exact (U.topIso.symm ≪≫ asIso (Product.dualOpenProductIso X U).hom.appTop).commRingCatIsoToRingEquiv.trans
    ((DualAffine.SectionCoefficients.dualAffineSectionCoefficients (Product.dualReducedOpenOver X U)).trans
      (Dual.NumberRingEquivalence.dualNumberRingEquiv ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).topIso.commRingCatIsoToRingEquiv))

theorem dualOpenProductMap_lands :
    (⊤ : (LieRanks.dualNumberTest ℂ ⊗ Product.dualReducedOpenOver X U).left.Opens) ≤ Product.dualOpenProductMap X U ⁻¹ᵁ U := by
  intro y _
  have h := congrArg (fun f => f y) (Product.dualOpenProductIso_hom_ι X U)
  change (Product.dualOpenProductMap X U) y ∈ U
  rw [← h]
  exact ((Product.dualOpenProductIso X U).hom y).property

theorem dualOpenSectionCoefficientEquiv_apply (hU : IsAffineOpen U)
    (s : Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, U)) :
    let : IsAffine (Product.dualReducedOpenOver X U).left := Dual.ReductionOpens.dualAffineOpen_reduction X U hU
    dualOpenSectionCoefficientEquiv X U hU s =
      Dual.NumberCoefficients.dualNumberRingMap ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).topIso.hom.hom
        (DualAffine.SectionCoefficients.dualAffineSectionCoefficients (Product.dualReducedOpenOver X U)
          ((Product.dualOpenProductMap X U).appLE U ⊤ (dualOpenProductMap_lands X U) s)) := by
  let : IsAffine (Product.dualReducedOpenOver X U).left := Dual.ReductionOpens.dualAffineOpen_reduction X U hU
  change Dual.NumberCoefficients.dualNumberRingMap _ (DualAffine.SectionCoefficients.dualAffineSectionCoefficients (Product.dualReducedOpenOver X U)
    ((Product.dualOpenProductIso X U).hom.appTop (U.topIso.inv s))) = _
  rw [Open.LiftSectionMap.openLift_sectionMap U (Product.dualOpenProductIso X U).hom (Product.dualOpenProductMap X U)
    (Product.dualOpenProductIso_hom_ι X U) (dualOpenProductMap_lands X U)]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence
