import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.GroupProductRigidity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.Support
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedMonoidAxes

/-! # Pointed Morphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.PointedMorphisms

noncomputable section

/-! An identity-preserving map from a proper smooth geometrically connected monoid scheme to a separated group scheme preserves multiplication. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {K : Type u} [Field K]

theorem smoothPointedMorphism_isMonHom (G H : Over (Spec (.of K)))
    [MonObj G] [GrpObj H] [UniversallyClosed G.hom] [Smooth G.hom]
    [GeometricallyConnected G.hom] [PreconnectedSpace G.left] [IsReduced (G ⊗ G).left] [IsSeparated H.hom]
    (f : G ⟶ H) (hf : η[G] ≫ f = η[H]) : IsMonHom f := by
  refine ⟨hf, ?_⟩
  apply GroupProductRigidity.smoothGroupProductMap_eq_of_axes G G H η[G] η[G]
  · rw [← Category.assoc, PointedMonoidAxes.monoid_mul_right_axis, Category.id_comp]
    exact (PointedMonoidAxes.pointed_mul_right_axis G H f hf).symm
  · rw [← Category.assoc, PointedMonoidAxes.monoid_mul_left_axis, Category.id_comp]
    exact (PointedMonoidAxes.pointed_mul_left_axis G H f hf).symm

theorem abelianPointedMorphism_isMonHom {g h : ℕ}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (B : Abelian.Schemes.AbelianScheme h (Spec (.of K)))
    (f : A.scheme ⟶ B.scheme) (hf : η[A.scheme] ≫ f = η[B.scheme]) : IsMonHom f := by
  have : ConnectedSpace A.scheme.left := A.connected_overField
  have : IsReduced (A.scheme ⊗ A.scheme).left := A.selfProduct_reduced_overField
  exact smoothPointedMorphism_isMonHom A.scheme B.scheme f hf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.PointedMorphisms
