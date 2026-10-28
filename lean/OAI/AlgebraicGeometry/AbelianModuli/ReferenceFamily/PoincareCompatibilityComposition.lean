import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.CompatibilityBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PointFaithfulness

/-! # Poincare Compatibility Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareCompatibilityComposition

noncomputable section

/-! Literal Poincare compatibility is closed under composition of
both family maps, without requiring a moduli isomorphism as an input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.CompatibilityBaseChange

universe u
variable {S : Scheme.{u}} {g : ℕ} {A B C : HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : HilbertConstruction.Dual.Data.DualAbelianData A) (E : HilbertConstruction.Dual.Data.DualAbelianData B) (F : HilbertConstruction.Dual.Data.DualAbelianData C)

theorem poincareCompatibility_comp
    (d : D.abelian.scheme ⟶ E.abelian.scheme) (e : A.scheme ⟶ B.scheme)
    (f : E.abelian.scheme ⟶ F.abelian.scheme) (q : B.scheme ⟶ C.scheme)
    (hde : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ e).left (HilbertConstruction.Line.Bundles.LineBundle.classOf E.poincare) = HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)
    (hfq : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (f ⊗ₘ q).left (HilbertConstruction.Line.Bundles.LineBundle.classOf F.poincare) = HilbertConstruction.Line.Bundles.LineBundle.classOf E.poincare) :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((d ≫ f) ⊗ₘ (e ≫ q)).left (HilbertConstruction.Line.Bundles.LineBundle.classOf F.poincare) = HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare := by
  rw [← tensorHom_comp_tensorHom, Over.comp_left, HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, hfq, hde]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareCompatibilityComposition
