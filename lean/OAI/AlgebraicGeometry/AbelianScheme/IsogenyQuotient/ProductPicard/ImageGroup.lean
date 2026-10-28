import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageOrigin
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FppfSheafRestriction
import OAI.AlgebraicGeometry.FormalGeometry.Completion.FppfPairLift

/-! # Image Group -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageGroup.Construction

noncomputable section

/-! The abelian Picard image embedding preserves multiplication on
all test schemes. The equality is detected after simultaneous fppf lifts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

universe u
variable {S : Scheme.{u}} {B C : Over S} [GrpObj B] [GrpObj C]
  (R : Picard.PoincareBundle.Line.Bundles.LineBundle (B ⊗ B).left)
  (βv : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber R (Picard.PoincareBundle.Vertical.ProductParameters.inputLeft B B))
    (Picard.PoincareBundle.Line.Fibers.fiber R (Picard.PoincareBundle.Vertical.ProductParameters.inputRight B B))
    (Picard.PoincareBundle.Line.Fibers.fiber R (Picard.PoincareBundle.Vertical.ProductParameters.outputPoint B B)))
  (hβv : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βv))
  (βh : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber R (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft B B))
    (Picard.PoincareBundle.Line.Fibers.fiber R (Picard.PoincareBundle.Product.ParameterSchemes.inputRight B B))
    (Picard.PoincareBundle.Line.Fibers.fiber R (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint B B)))
  (hβh : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βh))
  (q : B ⟶ C) [IsMonHom q]
  (i : uliftYoneda.{u + 1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (hfac : uliftYoneda.map q ≫ i = SheafMap.Construction.productNativePicardSheafMap R βv hβv)

omit [GrpObj C] in
theorem picardImage_value_natural {T U : Over S} (a : U ⟶ T) (x : T ⟶ C) :
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.map a.op (i.app (op T) (ULift.up x)) =
      i.app (op U) (ULift.up (a ≫ x)) :=
  (congrArg (fun t : (uliftYoneda.{u + 1}.obj C).obj (op T) ⟶
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op U) => t (ULift.up x)) (i.naturality a.op)).symm

variable [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]

include βh hβh hfac in
set_option backward.isDefEq.respectTransparency false in
theorem productPicardImage_mul {T : Over S} (x y : T ⟶ C) :
    i.app (op T) (ULift.up (x * y)) = i.app (op T) (ULift.up x) * i.app (op T) (ULift.up y) := by
  obtain ⟨U, p, a, b, hpflat, hpsurj, hpfp, ha, hb⟩ := FormalGeometry.Completion.FppfPairLift.Construction.fppf_lift_pair q x y
  have : Flat p.left := hpflat
  have : Surjective p.left := hpsurj
  have : LocallyOfFinitePresentation p.left := hpfp
  apply FppfSheafRestriction.Construction.fppfSheaf_restriction_injective p (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B)
  have hm (z w : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T)) :
      (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.map p.op (z * w) =
        (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.map p.op z * (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.map p.op w := by
    have h := (Picard.Homomorphisms.GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom (Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupPresheaf B) p.op).map_mul z w
    simp only [Picard.Homomorphisms.GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom_apply] at h
    exact h
  have hv (z : U ⟶ B) : i.app (op U) (ULift.up (z ≫ q)) = SheafMap.Construction.productNativePicardSectionHom R βv hβv βh hβh U z :=
    congrArg (fun t : uliftYoneda.{u + 1}.obj B ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj =>
      t.app (op U) (ULift.up z)) hfac
  rw [hm, picardImage_value_natural, picardImage_value_natural, picardImage_value_natural,
    MonObj.comp_mul, ha, hb, ← MonObj.mul_comp, hv, hv, hv, map_mul]

def productPicardImageSectionHom (T : Over S) :
    (T ⟶ C) →* (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T) where
  toFun x := i.app (op T) (ULift.up x)
  map_one' := (ImageOrigin.Construction.productPicardImage_origin R βv hβv βh hβh q i hfac T).trans
    (Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.trivialHomogeneousPicardClass_eq_one B T)
  map_mul' := productPicardImage_mul R βv hβv βh hβh q i hfac

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageGroup.Construction
