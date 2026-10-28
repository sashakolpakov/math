import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.GroupProductRigidity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedMonoidAxes

/-! # Monoid Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.MonoidUniqueness

noncomputable section

/-! A proper smooth geometrically connected group scheme admits only one monoid multiplication with its given identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {K : Type u} [Field K]

theorem smoothMonoid_multiplication_unique (G : Over (Spec (.of K))) [grp : GrpObj G]
    [UniversallyClosed G.hom] [Smooth G.hom] [GeometricallyConnected G.hom]
    [PreconnectedSpace G.left] [IsReduced (G ⊗ G).left]
    [IsSeparated G.hom] (m : MonObj G) (hm : m.one = grp.toMonObj.one) : m.mul = grp.toMonObj.mul := by
  let : MonObj G := grp.toMonObj
  have hmr : lift (𝟙 G) (toUnit G ≫ m.one) ≫ m.mul = 𝟙 G := by
    let : MonObj G := m
    exact PointedMonoidAxes.monoid_mul_right_axis G
  have hml : lift (toUnit G ≫ m.one) (𝟙 G) ≫ m.mul = 𝟙 G := by
    let : MonObj G := m
    exact PointedMonoidAxes.monoid_mul_left_axis G
  have hRight : lift (𝟙 G) (toUnit G ≫ η[G]) ≫ m.mul = 𝟙 G :=
    (congrArg (fun e => lift (𝟙 G) (toUnit G ≫ e) ≫ m.mul) hm).symm.trans hmr
  have hLeft : lift (toUnit G ≫ η[G]) (𝟙 G) ≫ m.mul = 𝟙 G :=
    (congrArg (fun e => lift (toUnit G ≫ e) (𝟙 G) ≫ m.mul) hm).symm.trans hml
  exact GroupProductRigidity.smoothGroupProductMap_eq_of_axes G G G η[G] η[G] m.mul μ[G]
    (hRight.trans (PointedMonoidAxes.monoid_mul_right_axis G).symm) (hLeft.trans (PointedMonoidAxes.monoid_mul_left_axis G).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.MonoidUniqueness
