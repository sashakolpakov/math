import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.GeometricFamilyGroupOperations

/-! # Laws Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup

noncomputable section

/-! Existing commutative-group laws survive arbitrary scheme base change and the canonical geometric family identification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Operations.FamilyGroupOperations.baseChange_laws {S T : Scheme.{u}} {X : Over S}
    (D : Operations.FamilyGroupOperations X) (f : T ⟶ S) (h : D.Laws) : (D.baseChange f).Laws := by
  apply (D.map_laws_iff (Over.pullback f)).mpr
  exact ⟨congrArg (Over.pullback f).map h.one_mul, congrArg (Over.pullback f).map h.mul_one,
    congrArg (Over.pullback f).map h.mul_assoc, congrArg (Over.pullback f).map h.left_inv,
    congrArg (Over.pullback f).map h.right_inv, congrArg (Over.pullback f).map h.mul_comm⟩

theorem Operations.FamilyGroupOperations.geometricBaseChange_laws {S : Scheme.{u}} {U T : Over S} {A : Over S}
    (D : Operations.FamilyGroupOperations ((Over.pullback T.hom).obj A)) (f : U ⟶ T) (h : D.Laws) :
    (D.geometricBaseChange f).Laws :=
  (D.geometricBaseChange_laws_iff f).mpr (D.baseChange_laws f.left h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup
