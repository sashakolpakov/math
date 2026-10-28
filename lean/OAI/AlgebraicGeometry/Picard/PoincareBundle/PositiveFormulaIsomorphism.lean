import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PositiveFormula

/-! # Positive Formula Isomorphism -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.PositiveFormulaIsomorphism

noncomputable section

/-! Transfer the actual normalized ample formula along an isomorphism of its biextension line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
  (Q Q' : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left)

/-- The inducing ample line and its zero normalization are preserved by the actual line isomorphism. -/
theorem of_iso (e : Q.sheaf ≅ Q'.sheaf) (h : AbelianScheme.IsogenyQuotient.PositiveFormula.Construction.PositivePoincareFormula A Q) :
    AbelianScheme.IsogenyQuotient.PositiveFormula.Construction.PositivePoincareFormula A Q' := by
  obtain ⟨L, hL, hzero, ⟨hformula⟩⟩ := h
  exact ⟨L, hL, hzero, ⟨AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr e.symm (Iso.refl _)) (Iso.refl _) ≪≫ hformula⟩⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.PositiveFormulaIsomorphism
