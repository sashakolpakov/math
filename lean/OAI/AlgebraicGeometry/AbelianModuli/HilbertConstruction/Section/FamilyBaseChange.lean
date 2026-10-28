import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PulledSectionCompletenessCriterion

/-! # Family Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.FamilyBaseChange

noncomputable section

/-! A complete family remains complete when the actual section tensor
comparison is bijective. The induced new basis consists of the specified
pulled-back sections. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
universe u v
variable {X Y : Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable (a : Y ⟶ X) (c : R →+* Γ(X, ⊤)) (M : X.Modules) (q : B →+* Γ(Y, ⊤))
variable (hq : q.comp (algebraMap R B) = a.appTop.hom.comp c)

theorem completeSectionFamily_pullback_of_tensor_bijective
    {κ : Type v} (s : κ → (Line.Bundles.structureModule X ⟶ M))
    (hs : Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s))
    (ht : Function.Bijective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M q hq ⊤)) :
    Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination q ((Scheme.Modules.pullback a).obj M)
      (fun i => Ample.LineBundles.pullbackSection a (s i))) := by
  let e := LinearEquiv.ofBijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s) hs
  let E := TensorProduct.congr (LinearEquiv.refl R B) e
  have he : E.toLinearMap = (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s).lTensor B := by
    apply TensorProduct.ext'
    intro b x
    rfl
  have hb : Function.Bijective ((Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s).lTensor B) := by
    rw [← he]
    exact E.bijective
  exact (PulledSectionCompletenessCriterion.sectionTensorCoefficients_bijective_iff a c M q hq s).mp (ht.comp hb)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.FamilyBaseChange
