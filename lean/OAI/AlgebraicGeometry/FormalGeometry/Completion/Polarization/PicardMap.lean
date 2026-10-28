import OAI.AlgebraicGeometry.FormalGeometry.Completion.Polarization.Family
import OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativePicard

/-! # Picard Map -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Polarization.PicardMap

noncomputable section

/-! The geometric polarization family gives an actual natural map into
the relative Picard sheaf. Its fibers are translation invariant there. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

def polarizationRelativeSection (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A) : AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections A T :=
  (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T) (Family.Construction.polarizationFamilyClass A L a).toMul

theorem polarizationRelativeSection_natural (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    {T U : Over (Spec (CommRingCat.of K))} (j : U ⟶ T) (a : T ⟶ A) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj.map j.op (polarizationRelativeSection A L a) =
      polarizationRelativeSection A L (j ≫ a) := by
  unfold polarizationRelativeSection
  rw [AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality]
  apply congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op U))
  exact congrArg Additive.toMul (Family.Construction.polarizationFamilyClass_pullback A L j a)

def polarizationPicardMap (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) :
    uliftYoneda.{u + 1}.obj A ⟶ (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj where
  app T := TypeCat.ofHom (fun a => polarizationRelativeSection A L a.down)
  naturality {T U} j := by
    apply ConcreteCategory.ext_apply
    intro a
    exact (polarizationRelativeSection_natural A L j.unop a.down).symm

theorem polarizationRelativeSection_one (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (T : Over (Spec (CommRingCat.of K))) :
    polarizationRelativeSection A L (1 : T ⟶ A) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T := by
  unfold polarizationRelativeSection
  rw [Family.Construction.polarizationFamilyClass_one]
  rfl

theorem polarizationRelativeSection_translation (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    {T : Over (Spec (CommRingCat.of K))} (x a : T ⟶ A) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Family.Construction.polarizationTestTranslation A a).left (Family.Construction.polarizationFamilyClass A L x).toMul) =
        polarizationRelativeSection A L x := by
  have ht := congrArg Additive.toMul (Family.Construction.polarizationFamilyClass_translated A L x a)
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Family.Construction.polarizationTestTranslation A a).left (Family.Construction.polarizationFamilyClass A L x).toMul =
    RelativePicard.Construction.RelativePicardBaseTwist.baseTwist A
      (SchemePointPicardPairing.Construction.schemePointPicardPairing A L T (Additive.ofMul x) (Additive.ofMul a)).toMul
      (Family.Construction.polarizationFamilyClass A L x).toMul at ht
  rw [ht]
  exact RelativePicard.Construction.RelativePicardBaseTwist.toRelativePicard_baseTwist_class A _ _

theorem polarizationFamilyClass_relative_homogeneous (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    {T U : Over (Spec (CommRingCat.of K))} (j : U ⟶ T) (x : T ⟶ A) (a : U ⟶ A) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op U)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Family.Construction.polarizationTestTranslation A a).left
        ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map j.op (Family.Construction.polarizationFamilyClass A L x).toMul)) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op U)
        ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map j.op (Family.Construction.polarizationFamilyClass A L x).toMul) := by
  have hn := congrArg Additive.toMul (Family.Construction.polarizationFamilyClass_pullback A L j x)
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map j.op (Family.Construction.polarizationFamilyClass A L x).toMul =
    (Family.Construction.polarizationFamilyClass A L (j ≫ x)).toMul at hn
  rw [hn]
  exact polarizationRelativeSection_translation A L (j ≫ x) a

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Polarization.PicardMap
