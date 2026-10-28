import OAI.AlgebraicGeometry.Picard.PoincareBundle.HorizontalClasses
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MapFromPointProducts

/-! # Homomorphism -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Homomorphism

noncomputable section

/-!
# The represented map preserves the group law

The target has its usual Picard universal property and an actual universal
Poincare line with invertible products. Tensor compatibility is proved from
those products, rather than assumed of the set-valued representation.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Homogeneous OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Map
open OAI.AlgebraicGeometry.Picard.PoincareBundle.TensorCongruence OAI.AlgebraicGeometry.Picard.PoincareBundle.HorizontalClasses

variable {S : Scheme.{u}} {B A D : Over S} [GrpObj A] [GrpObj D]
  (Q : Line.Bundles.LineBundle (D ⊗ A).left)
  (γv : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber Q (Vertical.ProductParameters.inputLeft D A))
    (Line.Fibers.fiber Q (Vertical.ProductParameters.inputRight D A))
    (Line.Fibers.fiber Q (Vertical.ProductParameters.outputPoint D A)))
  (hγv : IsIso (Bilinear.BilinearPullback.toHom γv))
  (HD : (Homogeneous.homogeneousSheaf A).obj.RepresentableBy D)
  (hQ : HD.homEquiv (𝟙 D) = Map.sectionClass Q γv hγv (𝟙 D))

include hQ

omit [GrpObj D] in
/-- The universal Poincare line represents the class of every point of the dual. -/
theorem universalSection_action {T : Over S} (x : T ⟶ D) :
    HD.homEquiv x = Map.sectionClass Q γv hγv x := by
  have hh := congrArg ((Homogeneous.homogeneousSheaf A).obj.map x.op) hQ
  rw [← HD.homEquiv_comp, Map.sectionClass_natural, Category.comp_id] at hh
  exact hh

variable [GrpObj B]
  (R : Line.Bundles.LineBundle (B ⊗ A).left)
  (βv : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber R (Vertical.ProductParameters.inputLeft B A))
    (Line.Fibers.fiber R (Vertical.ProductParameters.inputRight B A))
    (Line.Fibers.fiber R (Vertical.ProductParameters.outputPoint B A)))
  (hβv : IsIso (Bilinear.BilinearPullback.toHom βv))
  (βh : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber R (ParameterSchemes.inputLeft B A))
    (Line.Fibers.fiber R (ParameterSchemes.inputRight B A))
    (Line.Fibers.fiber R (ParameterSchemes.outputPoint B A)))
  (hβh : IsIso (Bilinear.BilinearPullback.toHom βh))
  (γh : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber Q (ParameterSchemes.inputLeft D A))
    (Line.Fibers.fiber Q (ParameterSchemes.inputRight D A))
    (Line.Fibers.fiber Q (ParameterSchemes.outputPoint D A)))
  (hγh : IsIso (Bilinear.BilinearPullback.toHom γh))

include βh hβh γh hγh

/-- The two actual horizontal products force multiplicativity of the represented map. -/
theorem representedMap_mul {T : Over S} (x y : T ⟶ B) :
    (x * y) ≫ Map.representedMap R βv hβv HD =
      (x ≫ Map.representedMap R βv hβv HD) * (y ≫ Map.representedMap R βv hβv HD) := by
  apply HD.homEquiv.injective
  rw [Map.representedMap_action, universalSection_action Q γv hγv HD hQ]
  have hx : Map.sectionClass R βv hβv x =
      Map.sectionClass Q γv hγv (x ≫ Map.representedMap R βv hβv HD) :=
    (Map.representedMap_action R βv hβv HD x).symm.trans (universalSection_action Q γv hγv HD hQ _)
  have hy : Map.sectionClass R βv hβv y =
      Map.sectionClass Q γv hγv (y ≫ Map.representedMap R βv hβv HD) :=
    (Map.representedMap_action R βv hβv HD y).symm.trans (universalSection_action Q γv hγv HD hQ _)
  dsimp only [Map.sectionClass]
  rw [HorizontalClasses.homogeneousClass_mul R βh hβh βv hβv, HorizontalClasses.homogeneousClass_mul Q γh hγh γv hγv]
  exact TensorCongruence.tensorHomogeneous_congr A hx hy

/-- An actual pair of products makes the represented quotient-to-dual map a group homomorphism. -/
theorem representedMap_isMonHom : IsMonHom (Map.representedMap R βv hβv HD) :=
  MapFromPointProducts.Group.isMonHom _
    (fun _ x y => representedMap_mul Q γv hγv HD hQ R βv hβv βh hβh γh hγh x y)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Homomorphism
