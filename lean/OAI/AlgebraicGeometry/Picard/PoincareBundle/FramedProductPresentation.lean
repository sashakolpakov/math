import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.FiberPresentation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PresentedIsoRestriction
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedInducingFormula

/-! # Framed Product Presentation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedProductPresentation

noncomputable section

/-! A coordinate presentation of the actual framed inducing product and its restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFormulaSymmetry

theorem comparison_comp {S : Scheme.{u}} {E K T : Over S}
    (L : Line.Bundles.LineBundle E.left) (q : T ⟶ K) (p : K ⟶ E) :
    Line.Fibers.fiberPullbackIso L q p (q ≫ p) rfl = (Scheme.Modules.pullbackComp q.left p.left).app L.sheaf := by
  apply Iso.ext
  exact Category.comp_id _

variable {S : Scheme.{u}} {A : Over S} [GrpObj A]
  (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : Line.Bundles.LineBundle A.left)
  (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (Line.Fibers.fiber L (fst A A))) (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L μ[A])

def mapIso {K : Over S} (p : K ⟶ A ⊗ A) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule K.left ≅ Line.Fibers.fiber (Line.Comparison.Bundle.fromShared Q) p) :
    Line.Fibers.fiber (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.factorLine A L)) p ≅ Line.Fibers.fiber (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.targetLine A L)) p :=
  @asIso _ _ _ _ (FramedInducingFormula.product Q L e p s) (FramedInducingFormula.product_isIso Q L e p s)

/-- Present the framed product on its two individual input fibers and its output fiber. -/
def presentation {K : Over S} (p : K ⟶ A ⊗ A) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule K.left ≅ Line.Fibers.fiber (Line.Comparison.Bundle.fromShared Q) p)
    (x y z : K ⟶ A) (hx : p ≫ fst A A = x) (hy : p ≫ snd A A = y) (hz : p ≫ μ[A] = z) :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (Line.Fibers.fiber L x) (Line.Fibers.fiber L y) ≅ Line.Fibers.fiber L z :=
  (Tensor.FiberComposition.comparison L (fst A A) (snd A A) p x y hx hy).symm ≪≫
    FramedProductPresentation.mapIso Q L e p s ≪≫ Line.Fibers.fiberPullbackIso L p μ[A] z hz

/-- The middle isomorphism has the exact composition square needed by coordinate presentations. -/
theorem mapIso_restriction {K T : Over S} (p : K ⟶ A ⊗ A)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule K.left ≅ Line.Fibers.fiber (Line.Comparison.Bundle.fromShared Q) p) (q : T ⟶ K) :
    (Scheme.Modules.pullback q.left).mapIso (FramedProductPresentation.mapIso Q L e p s) ≪≫
        (Scheme.Modules.pullbackComp q.left p.left).app (InducingFormulaSymmetry.targetLine A L).sheaf =
      (Scheme.Modules.pullbackComp q.left p.left).app (InducingFormulaSymmetry.factorLine A L).sheaf ≪≫
        FramedProductPresentation.mapIso Q L e (q ≫ p) (GlobalPullbackFrame.atPoint p (Line.Comparison.Bundle.fromShared Q) s q (q ≫ p) rfl) := by
  have h := FramedInducingFormula.evaluation Q L e p s q (q ≫ p) rfl
  rw [comparison_comp, comparison_comp] at h
  exact Iso.ext h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedProductPresentation
