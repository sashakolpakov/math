import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteGeometricPoints

/-! # Scheme Points -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SchemePoints.CM

noncomputable section

/-! A finite scheme over an algebraically closed field has discrete
underlying topology, and every underlying point has a unique rational
point above it. Nilpotents remain in the corresponding open subschemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  (T : Over (Spec (.of k))) [IsFinite T.hom]

theorem discreteTopology : DiscreteTopology T.left := by
  have : Finite (Over.mk (𝟙 (Spec (.of k))) ⟶ T) :=
    Picard.Homomorphisms.FiniteGeometricPoints.Construction.finite_overPoints T (𝟙 _)
  have : Finite (closedPoints T.left) :=
    Finite.of_equiv _ (Picard.Homomorphisms.FiniteGeometricPoints.Construction.rationalPointsClosedEquiv T)
  have : JacobsonSpace T.left := LocallyOfFiniteType.jacobsonSpace T.hom
  exact JacobsonSpace.discreteTopology (Set.toFinite (closedPoints T.left))

def pointsEquiv : (Over.mk (𝟙 (Spec (.of k))) ⟶ T) ≃ T.left := by
  let : DiscreteTopology T.left := CM.discreteTopology T
  exact ((Picard.Homomorphisms.FiniteGeometricPoints.Construction.rationalPointsClosedEquiv T).trans
    (Set.equivOfEq closedPoints_eq_univ)).trans (Equiv.Set.univ T.left)

theorem pointsEquiv_apply (p : Over.mk (𝟙 (Spec (.of k))) ⟶ T) :
    pointsEquiv T p = p.left (IsLocalRing.closedPoint k) := rfl

theorem pointsEquiv_naturality (U : Over (Spec (.of k))) [IsFinite U.hom]
    (f : T ⟶ U) (p : Over.mk (𝟙 (Spec (.of k))) ⟶ T) :
    pointsEquiv U (p ≫ f) = f.left (pointsEquiv T p) := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SchemePoints.CM
