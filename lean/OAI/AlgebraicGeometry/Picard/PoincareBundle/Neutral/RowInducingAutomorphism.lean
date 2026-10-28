import OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedInducingFormula
import OAI.AlgebraicGeometry.Picard.PoincareBundle.ProperFiberAutomorphismScalar
import OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalOriginLineFrames

/-! # Row Inducing Automorphism -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.RowInducingAutomorphism

noncomputable section

/-! The inducing formula along a framed neutral row gives a genuine line automorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

section

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFormulaSymmetry
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback

variable {S : Scheme.{u}} {A : Over S} [GrpObj A]
  (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : Line.Bundles.LineBundle A.left)
  (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (Line.Fibers.fiber L (fst A A))) (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L μ[A])
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ≅ Line.Fibers.fiber (Line.Comparison.Bundle.fromShared Q) (lift (𝟙 A) (1 : A ⟶ A)))

theorem row_multiply : lift (𝟙 A) (1 : A ⟶ A) ≫ μ[A] = 𝟙 A := by
  change (𝟙 A) * (1 : A ⟶ A) = 𝟙 A
  exact mul_one _

def sourceComparison :
    (Scheme.Modules.pullback (lift (𝟙 A) (1 : A ⟶ A)).left).obj (InducingFormulaSymmetry.factorLine A L).sheaf ≅
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (Line.Fibers.fiber L (𝟙 A)) (Line.Fibers.fiber L (1 : A ⟶ A)) :=
  Tensor.LinePullback.pullbackIso (lift (𝟙 A) (1 : A ⟶ A)).left _ _ (Line.Fibers.fiber_isLine L (fst A A)) (Line.Fibers.fiber_isLine L (snd A A)) ≪≫
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr
      (Line.Fibers.fiberPullbackIso L (lift (𝟙 A) (1 : A ⟶ A)) (fst A A) (𝟙 A) (lift_fst _ _))
      (Line.Fibers.fiberPullbackIso L (lift (𝟙 A) (1 : A ⟶ A)) (snd A A) (1 : A ⟶ A) (lift_snd _ _))

def productIso : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (Line.Fibers.fiber L (𝟙 A)) (Line.Fibers.fiber L (1 : A ⟶ A)) ≅ Line.Fibers.fiber L (𝟙 A) := by
  let r := lift (𝟙 A) (1 : A ⟶ A)
  let z := FramedInducingFormula.product Q L e r s
  have hz : IsIso z := FramedInducingFormula.product_isIso Q L e r s
  exact (sourceComparison L).symm ≪≫ @asIso _ _ _ _ z hz ≪≫
    Line.Fibers.fiberPullbackIso L r μ[A] (𝟙 A) row_multiply

/-- Inserting a neutral-line frame gives an automorphism of the original inducing line. -/
def automorphism (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ≅ Line.Fibers.fiber L (1 : A ⟶ A)) : Line.Fibers.fiber L (𝟙 A) ≅ Line.Fibers.fiber L (𝟙 A) :=
  (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (Line.Fibers.fiber L (𝟙 A))).symm ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr t (Iso.refl _) ≪≫
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso (Line.Fibers.fiber L (1 : A ⟶ A)) (Line.Fibers.fiber L (𝟙 A)) ≪≫ productIso Q L e s

end

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.AutomorphismUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberIsomorphismRatios OAI.AlgebraicGeometry.Picard.PoincareBundle.ProperFiberAutomorphismScalar

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : Line.Bundles.LineBundle A.left)
  (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (Line.Fibers.fiber L (fst A A))) (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L μ[A])
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ≅ Line.Fibers.fiber (Line.Comparison.Bundle.fromShared Q) (lift (𝟙 A) (1 : A ⟶ A)))
  (o : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (𝟙_ (Over (Spec (.of k)))).left ≅ Line.Fibers.fiber L η[A])

/-- The actual neutral-row automorphism has a uniform coefficient on every test scheme;
its origin-line frames and the scalar independence are both constructed. -/
theorem uniform_coefficient {T : Over (Spec (.of k))} (x y : T ⟶ A) :
    Line.AutomorphismUnits.unitOfAut (FiberIsomorphismRatios.fiberLine L x)
      (ProperFiberAutomorphismScalar.atPoint L (automorphism Q L e s (NaturalOriginLineFrames.frame L o A)) x) =
    Line.AutomorphismUnits.unitOfAut (FiberIsomorphismRatios.fiberLine L y)
      (ProperFiberAutomorphismScalar.atPoint L (automorphism Q L e s (NaturalOriginLineFrames.frame L o A)) y) :=
  ProperFiberAutomorphismScalar.group_coefficient_eq A L (automorphism Q L e s (NaturalOriginLineFrames.frame L o A)) x y

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.RowInducingAutomorphism
