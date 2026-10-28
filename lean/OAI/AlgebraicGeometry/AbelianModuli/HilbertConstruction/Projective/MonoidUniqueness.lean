import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.MonoidHomAxes
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PointedMapsAreHomomorphisms

/-! # Monoid Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.MonoidUniqueness

noncomputable section

/-! A projectively presented abelian scheme over a locally noetherian base has only one monoid multiplication with its given identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem projectiveAbelian_monoid_multiplication_unique
    {S : Scheme.{u}} [IsLocallyNoetherian S] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (P : ProjectivePresentations.ProjectivePresentation A.scheme)
    (m : MonObj A.scheme) (hm : m.one = A.group.toMonObj.one) : m.mul = A.group.toMonObj.mul := by
  let G := A.scheme
  let : MonObj G := A.group.toMonObj
  have hmr : lift (𝟙 G) (toUnit G ≫ m.one) ≫ m.mul = 𝟙 G := by
    let : MonObj G := m
    exact PointedMonoidAxes.monoid_mul_right_axis G
  have hml : lift (toUnit G ≫ m.one) (𝟙 G) ≫ m.mul = 𝟙 G := by
    let : MonObj G := m
    exact PointedMonoidAxes.monoid_mul_left_axis G
  have hRight : lift (𝟙 G) (1 : G ⟶ G) ≫ m.mul = 𝟙 G := by
    change lift (𝟙 G) (toUnit G ≫ η[G]) ≫ m.mul = 𝟙 G
    exact (congrArg (fun e => lift (𝟙 G) (toUnit G ≫ e) ≫ m.mul) hm).symm.trans hmr
  have hLeft : lift (1 : G ⟶ G) (𝟙 G) ≫ m.mul = 𝟙 G := by
    change lift (toUnit G ≫ η[G]) (𝟙 G) ≫ m.mul = 𝟙 G
    exact (congrArg (fun e => lift (toUnit G ≫ e) (𝟙 G) ≫ m.mul) hm).symm.trans hml
  have hone : IsMonHom (1 : G ⟶ G) := by
    change IsMonHom (toUnit G ≫ η[G])
    infer_instance
  let r := lift (𝟙 G) (1 : G ⟶ G)
  have hr : IsMonHom r := inferInstance
  have hη : η[G ⊗ G] ≫ m.mul = η[G] := by
    rw [← IsMonHom.one_hom r, Category.assoc, hRight, Category.comp_id]
  have hf : IsMonHom m.mul := PointedMapsAreHomomorphisms.projectivePointedMap_isMonHom (A.product A) A (P.product P) P m.mul hη
  exact Product.MonoidHomAxes.productMonoidHom_eq_of_axes G G G m.mul μ[G]
    (hRight.trans (mul_one (𝟙 G)).symm) (hLeft.trans (one_mul (𝟙 G)).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.MonoidUniqueness
