import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.CechClasses

/-! # Intrinsic Operators -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.IntrinsicOperators

noncomputable section

/-! Native differentials and coefficient maps in inverse literal Cech coordinates. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)

theorem abelianCechCoordinates_symm_d (F : X.Presheaf AddCommGrpCat.{0}) (n : ℕ)
    (k : Abelian.CechCoordinates.AbelianCechCochain F U n) :
    ((CategoryTheory.cechComplexFunctor U).obj F).d n (n + 1)
        ((Abelian.CechCoordinates.abelianCechCoordinates F U n).symm k) =
      (Abelian.CechCoordinates.abelianCechCoordinates F U (n + 1)).symm (Abelian.CechCoordinates.abelianCechDelta F U n k) := by
  apply (Abelian.CechCoordinates.abelianCechCoordinates F U (n + 1)).injective
  rw [Abelian.CechCoordinates.abelianCechCoordinates_d, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

theorem abelianCechCoordinates_symm_coefficient {F G : X.Presheaf AddCommGrpCat.{0}}
    (f : F ⟶ G) (n : ℕ) (k : Abelian.CechCoordinates.AbelianCechCochain F U n) :
    ((CategoryTheory.cechComplexFunctor U).map f).f n ((Abelian.CechCoordinates.abelianCechCoordinates F U n).symm k) =
      (Abelian.CechCoordinates.abelianCechCoordinates G U n).symm (Abelian.CechClasses.abelianCechCoefficient U f n k) := by
  apply (Abelian.CechCoordinates.abelianCechCoordinates G U n).injective
  rw [AddEquiv.apply_symm_apply]
  funext a
  rw [Abelian.CechCoordinates.abelianCechCoordinates_naturality, AddEquiv.apply_symm_apply]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.IntrinsicOperators
