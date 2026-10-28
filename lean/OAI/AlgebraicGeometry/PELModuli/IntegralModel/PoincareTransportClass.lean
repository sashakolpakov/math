import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Iso

/-! # Poincare Transport Class -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PoincareTransportClass

noncomputable section

/-! A genuine PEL comparison preserves the actual Poincare class after
evaluation at every point of the pulled-back dual-by-abelian product. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ} {S T Z : Scheme.{0}}

omit [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] in
theorem poincare_transport_class (A : PEL.Has.PolarizedActionData E g δ N S) (f h : T ⟶ S)
    (e : PEL.Iso.PolarizedActionIso (A.pullback f) (A.pullback h))
    (p : Z ⟶ ((A.polarized.dual.abelian.pullback f).scheme ⊗
      (A.polarized.abelian.pullback f).scheme).left) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
        (p ≫ (e.polarized.dual.hom ⊗ₘ e.polarized.abelian.hom).left ≫
          AbelianModuli.HilbertConstruction.PolarizationData.poincareBaseChangeMap A.polarized.dual h)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.polarized.dual.poincare) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (p ≫ AbelianModuli.HilbertConstruction.PolarizationData.poincareBaseChangeMap A.polarized.dual f)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.polarized.dual.poincare) := by
  have he := (PEL.Has.PulledBackPELDataIso.ofActionIso e).poincare
  exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp p _ _).trans
    ((congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass p) he).trans
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp p _ _).symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PoincareTransportClass
