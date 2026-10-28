import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.SourceMap
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UnbundledPicardPullbackHom
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupMaps

/-! # Picard Image Source Group -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardImageSourceGroup.Construction

noncomputable section

/-! The represented source map preserves the canonical Picard group
law over every base whenever the image map preserves tensor products.
No comparison with a separately supplied dual group law is used. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B C : Over S} [GrpObj A] [GrpObj B] [GrpObj C]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : A ⟶ B) [IsMonHom f]
  (i : uliftYoneda.{u + 1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (F : ∀ T : Over S, (T ⟶ C) →* (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T))
  (hF : ∀ (T : Over S) (x : T ⟶ C), F T x = i.app (op T) (ULift.up x))

def canonicalPicardImageSourcePointHom (T : Over S) :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    (T ⟶ C) →* (T ⟶ D.abelian) :=
  letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroupHomEquiv D T).symm.toMonoidHom.comp
    ((UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom f T).comp (F T))

include hF in
set_option backward.isDefEq.respectTransparency false in
theorem canonicalPicardImageSourcePointHom_apply (T : Over S) (x : T ⟶ C) :
    canonicalPicardImageSourcePointHom D f F T x = x ≫ PicardImage.SourceMap.Construction.picardImageSourceMap D f i := by
  apply D.representable.homEquiv.injective
  change D.representable.homEquiv
    (D.representable.homEquiv.symm (UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom f T (F T x))) = _
  rw [Equiv.apply_symm_apply, PicardImage.SourceMap.Construction.picardImageSourceMap_value, hF, UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom_apply]

include hF in
theorem canonicalPicardImageSourceMap_isMonHom :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    IsMonHom (PicardImage.SourceMap.Construction.picardImageSourceMap D f i) := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  apply GroupMaps.Construction.isMonHom_of_pointwise
  · intro T
    rw [← canonicalPicardImageSourcePointHom_apply D f i F hF]
    exact (canonicalPicardImageSourcePointHom D f F T).map_one
  · intro T x y
    rw [← canonicalPicardImageSourcePointHom_apply D f i F hF,
      ← canonicalPicardImageSourcePointHom_apply D f i F hF,
      ← canonicalPicardImageSourcePointHom_apply D f i F hF]
    exact (canonicalPicardImageSourcePointHom D f F T).map_mul x y

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardImageSourceGroup.Construction
