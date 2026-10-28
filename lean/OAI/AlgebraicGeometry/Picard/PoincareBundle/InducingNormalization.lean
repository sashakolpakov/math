import OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingClass

/-! # Inducing Normalization -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingNormalization.Bundle

noncomputable section

/-! The actual difference line of an origin-normalized inducing line is trivial on both identity axes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingClass.Bundle

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
  (o : (L.pullback η[A].left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)

include o

/-- The identity-valued fiber is trivial over every test scheme. -/
theorem identity_class (T : Over S) : Homomorphisms.SchemePullback.Construction.schemePicardPullback (1 : T ⟶ A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1 := by
  have hz : Homomorphisms.SchemePullback.Construction.schemePicardPullback η[A].left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1 := Quotient.sound ⟨o⟩
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((toUnit T).left ≫ η[A].left) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1
  exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (toUnit T).left η[A].left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).trans
    ((congrArg (Homomorphisms.SchemePullback.Construction.schemePicardPullback (toUnit T).left) hz).trans (map_one _))

/-- The first identity axis of the actual difference line is trivial. -/
def firstAxis :
    (Scheme.Modules.pullback (lift (𝟙 A) (1 : A ⟶ A)).left).obj (InducingClass.Bundle.line A L).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left := by
  have h : Homomorphisms.SchemePullback.Construction.schemePicardPullback (lift (𝟙 A) (1 : A ⟶ A)).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (InducingClass.Bundle.line A L)) = 1 := by
    rw [InducingClass.Bundle.classOf_line, InducingClass.Bundle.lineClass_atPoint, mul_one, identity_class A L o A, div_self', div_one]
  exact Classical.choice (Quotient.exact h)

/-- The second identity axis of the actual difference line is trivial. -/
def secondAxis :
    (Scheme.Modules.pullback (lift (1 : A ⟶ A) (𝟙 A)).left).obj (InducingClass.Bundle.line A L).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left := by
  have h : Homomorphisms.SchemePullback.Construction.schemePicardPullback (lift (1 : A ⟶ A) (𝟙 A)).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (InducingClass.Bundle.line A L)) = 1 := by
    rw [InducingClass.Bundle.classOf_line, InducingClass.Bundle.lineClass_atPoint, one_mul, identity_class A L o A, div_one, div_self']
  exact Classical.choice (Quotient.exact h)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingNormalization.Bundle
