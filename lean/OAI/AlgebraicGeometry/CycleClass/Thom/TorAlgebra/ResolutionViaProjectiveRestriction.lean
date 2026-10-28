import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DerivedBaseChange
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.AcyclicResolution

/-! # Resolution Via Projective Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ResolutionViaProjectiveRestriction

noncomputable section

/-! A right-exact functor can carry a chosen projective resolution
to a projective resolution when a faithful exact comparison detects
acyclicity after restriction to a projective object. This is the
resolution comparison used in the reduction to the diagonal. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughProjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {C' : Type u₃} [Category.{v₃} C'] [Abelian C'] [EnoughProjectives C']
  {D' : Type u₄} [Category.{v₄} D'] [Abelian D']
  (F : C ⥤ D) (F' : C' ⥤ D') (H : C ⥤ C') (G : D ⥤ D')
  [F.Additive] [F'.Additive] [H.Additive] [G.Additive]
  [H.PreservesProjectiveObjects] [H.PreservesHomology] [G.PreservesHomology] [G.Faithful]
  (e : H ⋙ F' ≅ F ⋙ G) (X : C) [Projective (H.obj X)]

include e

theorem higherDerived_isZero (n : ℕ) : IsZero ((F.leftDerived (n + 1)).obj X) := by
  have hz : IsZero (G.obj ((F.leftDerived (n + 1)).obj X)) :=
    (F'.isZero_leftDerived_obj_projective_succ n (H.obj X)).of_iso
      (DerivedBaseChange.leftDerivedIso F F' H G e X (n + 1)).symm
  apply (IsZero.iff_id_eq_zero _).mpr
  apply G.map_injective
  rw [G.map_id, G.map_zero]
  exact hz.eq_of_src _ _

def resolution [F.PreservesProjectiveObjects] [PreservesFiniteColimits F]
    (P : ProjectiveResolution X) : ProjectiveResolution (F.obj X) :=
  AcyclicResolution.resolution F P (higherDerived_isZero F F' H G e X)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ResolutionViaProjectiveRestriction
