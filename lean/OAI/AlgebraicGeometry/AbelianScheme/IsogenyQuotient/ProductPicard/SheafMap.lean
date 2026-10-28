import OAI.AlgebraicGeometry.Picard.PoincareBundle.HorizontalClasses
import OAI.AlgebraicGeometry.Picard.PoincareBundle.HomogeneousComparison
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledGroup

/-! # Sheaf Map -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.SheafMap.Construction

noncomputable section

/-! An actual product line defines a homomorphism to the homogeneous
Picard sheaf before a dual scheme has been constructed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Map
open OAI.AlgebraicGeometry.Picard.PoincareBundle.HomogeneousComparison OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle
open OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard

universe u

theorem e45ClassEquiv_tensor {X : Scheme.{u}}
    (a b : Picard.PoincareBundle.Line.Bundles.LineBundleClass X) :
    Picard.PoincareBundle.Line.Comparison.Bundle.classEquiv X (Picard.PoincareBundle.Tensor.LineBundles.tensorClass a b) = Picard.PoincareBundle.Line.Comparison.Bundle.classEquiv X a * Picard.PoincareBundle.Line.Comparison.Bundle.classEquiv X b := by
  induction a using Quotient.inductionOn with
  | _ A =>
    induction b using Quotient.inductionOn with
    | _ B => rfl

variable {S : Scheme.{u}} {B A : Over S} [GrpObj A]
  (R : Picard.PoincareBundle.Line.Bundles.LineBundle (B ⊗ A).left)
  (βv : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber R (Picard.PoincareBundle.Vertical.ProductParameters.inputLeft B A))
    (Picard.PoincareBundle.Line.Fibers.fiber R (Picard.PoincareBundle.Vertical.ProductParameters.inputRight B A))
    (Picard.PoincareBundle.Line.Fibers.fiber R (Picard.PoincareBundle.Vertical.ProductParameters.outputPoint B A)))
  (hβv : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βv))

def productNativeHomogeneousClass {T : Over S} (x : T ⟶ B) :
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A).obj (op T) :=
  Picard.PoincareBundle.HomogeneousComparison.homogeneousClassEquiv A T (Picard.PoincareBundle.Product.Map.homogeneousClass R βv hβv x)

theorem productNativeHomogeneousClass_natural {T U : Over S} (t : U ⟶ T) (x : T ⟶ B) :
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A).map t.op (productNativeHomogeneousClass R βv hβv x) =
      productNativeHomogeneousClass R βv hβv (t ≫ x) := by
  have H := (Picard.PoincareBundle.HomogeneousComparison.homogeneousPresheafIso A).hom.naturality_apply t.op (Picard.PoincareBundle.Product.Map.homogeneousClass R βv hβv x)
  rw [Picard.PoincareBundle.Product.Map.homogeneousClass_natural] at H
  exact H.symm

def productNativePicardSheafMap : uliftYoneda.{u + 1}.obj B ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj :=
  { app T := ↾(fun x => (toSheafify (Scheme.fppfTopology.over S)
      (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A)).app T (productNativeHomogeneousClass R βv hβv x.down))
    naturality {T U} t := by
      apply ConcreteCategory.ext_apply
      intro x
      have H := (toSheafify (Scheme.fppfTopology.over S)
        (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A)).naturality_apply t (productNativeHomogeneousClass R βv hβv x.down)
      have hn := productNativeHomogeneousClass_natural R βv hβv t.unop x.down
      exact (congrArg ((toSheafify (Scheme.fppfTopology.over S)
        (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A)).app U) hn.symm).trans H }

variable [GrpObj B]
  (βh : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber R (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft B A))
    (Picard.PoincareBundle.Line.Fibers.fiber R (Picard.PoincareBundle.Product.ParameterSchemes.inputRight B A))
    (Picard.PoincareBundle.Line.Fibers.fiber R (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint B A)))
  (hβh : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βh))

include βh hβh in
set_option backward.isDefEq.respectTransparency false in
theorem productNativeHomogeneousClass_mul {T : Over S} (x y : T ⟶ B) :
    productNativeHomogeneousClass R βv hβv (x * y) =
      productNativeHomogeneousClass R βv hβv x * productNativeHomogeneousClass R βv hβv y := by
  apply Subtype.ext
  change Picard.PoincareBundle.Line.Comparison.Bundle.classEquiv (T ⊗ A).left (Picard.PoincareBundle.Vertical.Homogeneity.familyClass R (x * y)) =
    Picard.PoincareBundle.Line.Comparison.Bundle.classEquiv (T ⊗ A).left (Picard.PoincareBundle.Vertical.Homogeneity.familyClass R x) *
      Picard.PoincareBundle.Line.Comparison.Bundle.classEquiv (T ⊗ A).left (Picard.PoincareBundle.Vertical.Homogeneity.familyClass R y)
  rw [Picard.PoincareBundle.HorizontalClasses.familyClass_mul R βh hβh]
  exact e45ClassEquiv_tensor _ _

def productNativeHomogeneousClassHom (T : Over S) :
    (T ⟶ B) →* (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A).obj (op T) where
  toFun := productNativeHomogeneousClass R βv hβv
  map_mul' := productNativeHomogeneousClass_mul R βv hβv βh hβh
  map_one' := by
    have H := productNativeHomogeneousClass_mul R βv hβv βh hβh (1 : T ⟶ B) 1
    rw [one_mul] at H
    apply mul_left_cancel (a := productNativeHomogeneousClass R βv hβv (1 : T ⟶ B))
    rw [mul_one]
    exact H.symm

def productNativePicardSectionHom (T : Over S) :
    (T ⟶ B) →* (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj.obj (op T) :=
  (Picard.Homomorphisms.GroupSheafification.Construction.picardTypeSheafifyUnitHom (Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupPresheaf A) (op T)).comp
    (productNativeHomogeneousClassHom R βv hβv βh hβh T)

theorem productNativePicardSectionHom_apply (T : Over S) (x : T ⟶ B) :
    productNativePicardSectionHom R βv hβv βh hβh T x =
      (productNativePicardSheafMap R βv hβv).app (op T) (ULift.up x) := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.SheafMap.Construction
