import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoefficientSectionBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionFrameCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ScalarSectionGlobalValue

/-! # Coefficient Section Basis -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.CoefficientSectionBasis

noncomputable section

/-! A complete section basis over the global ring of a field spectrum
is a basis over the original field, with the same actual section maps. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
variable {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (M : X.Modules)
variable {ι : Type v}

def fieldCoefficientSectionBasis
    (b : Module.Basis ι Γ(Spec (.of K), ⊤) ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor p.appTop.hom).obj M)) :
    Module.Basis ι K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M) :=
  Affine.CoefficientSectionBasis.affineCoefficientSectionBasis p M b

theorem fieldCoefficientSectionBasis_family
    (b : Module.Basis ι Γ(Spec (.of K), ⊤) ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor p.appTop.hom).obj M)) :
    Coefficient.RingSectionBasis.coefficientRingBasisFamily (Coefficient.ModulePresheaf.schemeCoefficientMap p) M (fieldCoefficientSectionBasis p M b) =
      Coefficient.RingSectionBasis.coefficientRingBasisFamily p.appTop.hom M b :=
  Affine.CoefficientSectionBasis.affineCoefficientSectionBasis_family p M b

theorem field_completeSectionFamily_has_basis
    (s : ι → (Line.Bundles.structureModule X ⟶ M))
    (hs : Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination p.appTop.hom M s)) :
    ∃ b : Module.Basis ι K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M),
      Coefficient.RingSectionBasis.coefficientRingBasisFamily (Coefficient.ModulePresheaf.schemeCoefficientMap p) M b = s := by
  let b := Coefficient.SectionFrameCriterion.coefficientSectionBasisOfBijective p.appTop.hom M s hs
  exact ⟨fieldCoefficientSectionBasis p M b,
    (fieldCoefficientSectionBasis_family p M b).trans
      (Coefficient.SectionFrameCriterion.coefficientSectionBasisOfBijective_family p.appTop.hom M s hs)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.CoefficientSectionBasis
