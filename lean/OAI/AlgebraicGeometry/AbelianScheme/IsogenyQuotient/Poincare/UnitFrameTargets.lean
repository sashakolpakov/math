import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.VerticalUnits
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberPointEquality

/-! # Unit Frame Targets -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.UnitFrameTargets.Construction

noncomputable section

/-! The original Poincare unit frames commute with the canonical
transport between equal target points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem poincareHorizontalUnitFrame_target {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {T : Over S} (x y : T ⟶ D.abelian.scheme ⊗ A.scheme)
    (hx : x ≫ fst D.abelian.scheme A.scheme = 1) (hy : y ≫ fst D.abelian.scheme A.scheme = 1)
    (h : x = y) :
    AxisFrames.Construction.poincareHorizontalUnitFrame D x hx ≪≫ FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x y h =
      AxisFrames.Construction.poincareHorizontalUnitFrame D y hy := by
  cases h
  exact Iso.trans_refl _

theorem poincareVerticalUnitFrame_target {k : Type u} [Field k] {g : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {T : Over (Spec (.of k))}
    (x y : T ⟶ D.abelian.scheme ⊗ A.scheme)
    (hx : x ≫ snd D.abelian.scheme A.scheme = 1) (hy : y ≫ snd D.abelian.scheme A.scheme = 1)
    (h : x = y) :
    VerticalUnits.Construction.poincareVerticalUnitFrame D x hx ≪≫ FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x y h =
      VerticalUnits.Construction.poincareVerticalUnitFrame D y hy := by
  cases h
  exact Iso.trans_refl _

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.UnitFrameTargets.Construction
