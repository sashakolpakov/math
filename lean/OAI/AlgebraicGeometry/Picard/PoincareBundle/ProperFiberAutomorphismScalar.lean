import OAI.AlgebraicGeometry.Picard.PoincareBundle.ProperOriginCoefficients
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberIsomorphismRatios

/-! # Proper Fiber Automorphism Scalar -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ProperFiberAutomorphismScalar

noncomputable section

/-! A proper-group line automorphism has the same actual fiber coefficient at every test point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

section

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberIsomorphismRatios OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.AutomorphismUnits

variable {S : Scheme.{u}} {A : Over S} (L : Line.Bundles.LineBundle A.left)
  (e : Line.Fibers.fiber L (𝟙 A) ≅ Line.Fibers.fiber L (𝟙 A))

/-- The actual automorphism on the chosen test-point fiber, with canonical comparisons. -/
def atPoint {T : Over S} (x : T ⟶ A) : Line.Fibers.fiber L x ≅ Line.Fibers.fiber L x :=
  FiberIsomorphismRatios.pullIso L e x x x (Category.comp_id x) (Category.comp_id x)

theorem coefficient_pullback {T : Over S} (x : T ⟶ A) :
    Line.AutomorphismUnits.unitOfAut (FiberIsomorphismRatios.fiberLine L x) (atPoint L e x) =
      Units.map x.left.appTop.hom.toMonoidHom (Line.AutomorphismUnits.unitOfAut (FiberIsomorphismRatios.fiberLine L (𝟙 A)) e) := by
  have hc := Line.AutomorphismUnits.unitOfAut_conjugate
    (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_pullback x.left (Line.Fibers.fiber L (𝟙 A)) (FiberIsomorphismRatios.fiberLine L (𝟙 A))) (FiberIsomorphismRatios.fiberLine L x)
    (Line.Fibers.fiberPullbackIso L x (𝟙 A) x (Category.comp_id x)) ((Scheme.Modules.pullback x.left).mapIso e)
  exact hc.trans (Line.AutomorphismUnits.unitOfAut_pullback (FiberIsomorphismRatios.fiberLine L (𝟙 A)) x.left e)

/-- Coefficients of the geometrically identified actual fibers agree at any two points over the base. -/
theorem coefficient_eq [IsIso A.hom.appTop] {T : Over S} (x y : T ⟶ A) :
    Line.AutomorphismUnits.unitOfAut (FiberIsomorphismRatios.fiberLine L x) (atPoint L e x) = Line.AutomorphismUnits.unitOfAut (FiberIsomorphismRatios.fiberLine L y) (atPoint L e y) :=
  (coefficient_pullback L e x).trans
    ((ProperOriginCoefficients.unit_pullback_eq A.hom x.left y.left
      ((Over.w x).trans (Over.w y).symm) (Line.AutomorphismUnits.unitOfAut (FiberIsomorphismRatios.fiberLine L (𝟙 A)) e)).trans
      (coefficient_pullback L e y).symm)

end

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberIsomorphismRatios OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.AutomorphismUnits

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (L : Line.Bundles.LineBundle A.left) (e : Line.Fibers.fiber L (𝟙 A) ≅ Line.Fibers.fiber L (𝟙 A))

/-- Ordinary proper smooth connected group hypotheses suffice, in every characteristic. -/
theorem group_coefficient_eq {T : Over (Spec (.of k))} (x y : T ⟶ A) :
    Line.AutomorphismUnits.unitOfAut (FiberIsomorphismRatios.fiberLine L x) (atPoint L e x) = Line.AutomorphismUnits.unitOfAut (FiberIsomorphismRatios.fiberLine L y) (atPoint L e y) := by
  have : IsIso A.hom.appTop := Homomorphisms.ProperGroupFunctions.Construction.properGroup_appTop_isIso A
  exact coefficient_eq L e x y

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ProperFiberAutomorphismScalar
