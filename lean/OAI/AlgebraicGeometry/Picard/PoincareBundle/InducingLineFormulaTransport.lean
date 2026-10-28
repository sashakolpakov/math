import OAI.AlgebraicGeometry.Picard.PoincareBundle.PositivePoincareMultiple

/-! # Inducing Line Formula Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingLineFormulaTransport

noncomputable section

/-! Transport an actual inducing-line formula through an isomorphism of its inducing lines. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} (A : Over S) [GrpObj A]
  (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (e : L.sheaf ≅ M.sheaf)

/-- Isomorphic inducing lines have actual isomorphic multiplication formulas. -/
def formula
    (t : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (L.pullback (fst A A).left).sheaf)
      (L.pullback (snd A A).left).sheaf ≅ (L.pullback μ[A].left).sheaf) :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (M.pullback (fst A A).left).sheaf)
      (M.pullback (snd A A).left).sheaf ≅ (M.pullback μ[A].left).sheaf :=
  AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (Iso.refl _) ((Scheme.Modules.pullback (fst A A).left).mapIso e.symm))
    ((Scheme.Modules.pullback (snd A A).left).mapIso e.symm) ≪≫ t ≪≫
    (Scheme.Modules.pullback μ[A].left).mapIso e

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingLineFormulaTransport
