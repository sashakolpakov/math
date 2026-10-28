import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.DualData
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.PoincarePullbackLine
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardPullback
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ParameterKernel
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Covers
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Noetherian

/-! # Picard Dual -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PicardDual.Construction

noncomputable section

/-! The Cartier quotient representing the whole Picard sheaf carries
an actual normalized universal Poincare line over a Noetherian base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] ParameterKernel.Construction.abelianIsogeny_locallyOfFinitePresentation

variable {S : Scheme.{0}} {g : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (v : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A)
  (Q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian Q)
  (i : uliftYoneda.{1}.obj Q.scheme ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B.scheme).obj)
  (hfac : uliftYoneda.map q.hom ≫ i = Canonical.PicardPullback.Construction.canonicalPicardPullbackSheafMap D v.hom)

abbrev canonicalRelativePoincarePullbackLine :=
  Relative.PoincarePullbackLine.Construction.relativePoincarePullbackLine (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled (Canonical.DualData.Construction.canonicalDualAbelianData D)) v.hom

include hfac in
set_option backward.isDefEq.respectTransparency false in
theorem canonicalRelativePoincarePullbackLine_value (T : Over S)
    (a : T ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme) :
    (canonicalRelativePoincarePullbackLine D v).relativeValue a =
      (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B.scheme).hom.app (op T)
        (i.app (op T) (ULift.up (a ≫ q.hom))) := by
  rw [Relative.PoincarePullbackLine.Construction.relativePoincarePullbackLine_value]
  have hf := congrArg (fun t : uliftYoneda.{1}.obj (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme ⟶
      (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B.scheme).obj => t.app (op T) (ULift.up a)) hfac
  change i.app (op T) (ULift.up (a ≫ q.hom)) = Canonical.PicardPullback.Construction.canonicalPicardPullbackHom D v.hom T a at hf
  rw [hf]
  change _ = (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B.scheme).hom.app (op T)
    (UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom v.hom T ((Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).representable.homEquiv a))
  rw [UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom_apply]
  rfl

include hfac in
theorem canonicalRelativePoincarePullbackLine_eq_on_quotient {T : Over S}
    (a b : T ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme) (h : a ≫ q.hom = b ≫ q.hom) :
    (canonicalRelativePoincarePullbackLine D v).relativeValue a =
      (canonicalRelativePoincarePullbackLine D v).relativeValue b := by
  rw [canonicalRelativePoincarePullbackLine_value D v Q q i hfac,
    canonicalRelativePoincarePullbackLine_value D v Q q i hfac, h]

variable [IsLocallyNoetherian S] [IsIso i]
  (h1 : ∀ T : Over S, i.app (op T) (ULift.up (1 : T ⟶ Q.scheme)) = 1)

local instance : IsLocallyNoetherian (Q.scheme ⊗ B.scheme).left :=
  Picard.PoincareBundle.Product.Noetherian.product_noetherian Q.scheme B.scheme

local instance : IsAffineHom (q.hom ⊗ₘ 𝟙 B.scheme).left := by
  have : IsAffineHom (Over.Hom.left (𝟙 B.scheme)) := inferInstanceAs (IsAffineHom (𝟙 B.scheme.left))
  exact Picard.PoincareBundle.Product.Covers.tensorAffine q.hom (𝟙 B.scheme)

local instance : Flat (q.hom ⊗ₘ 𝟙 B.scheme).left := by
  have : Flat (Over.Hom.left (𝟙 B.scheme)) := inferInstanceAs (Flat (𝟙 B.scheme.left))
  exact Picard.PoincareBundle.Product.Covers.tensorFlat q.hom (𝟙 B.scheme)

local instance : Surjective (q.hom ⊗ₘ 𝟙 B.scheme).left := by
  have : Surjective (Over.Hom.left (𝟙 B.scheme)) := inferInstanceAs (Surjective (𝟙 B.scheme.left))
  exact Picard.PoincareBundle.Product.Covers.tensorSurjective q.hom (𝟙 B.scheme)

local instance : LocallyOfFinitePresentation (q.hom ⊗ₘ 𝟙 B.scheme).left := by
  have : LocallyOfFinitePresentation (Over.Hom.left (𝟙 B.scheme)) :=
    inferInstanceAs (LocallyOfFinitePresentation (𝟙 B.scheme.left))
  exact Picard.PoincareBundle.Product.Covers.property_tensor (@LocallyOfFinitePresentation) q.hom (𝟙 B.scheme)
    inferInstance inferInstance

set_option backward.isDefEq.respectTransparency false in
def noetherianPicardQuotientDualData : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B :=
  ((canonicalRelativePoincarePullbackLine D v).relativePicardQuotientDualData q.hom
    (fun {_T} _ a b h => canonicalRelativePoincarePullbackLine_eq_on_quotient D v Q q i hfac a b h)
    (Relative.PoincarePullbackLine.Construction.relativePoincarePullbackLine_homogeneous (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled (Canonical.DualData.Construction.canonicalDualAbelianData D)) v.hom)
    (Relative.PoincarePullbackLine.Construction.relativePoincarePullbackLine_secondAxis_class (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled (Canonical.DualData.Construction.canonicalDualAbelianData D)) v.hom)
    i (canonicalRelativePoincarePullbackLine_value D v Q q i hfac)
    (fun T => (h1 T).trans (Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.trivialHomogeneousPicardClass_eq_one B.scheme T).symm)).toBundled B Q.smoothDimension

theorem noetherianPicardQuotientDualData_value (T : Over S) (x : T ⟶ Q.scheme) :
    (noetherianPicardQuotientDualData D v Q q i hfac h1).representable.homEquiv x =
      i.app (op T) (ULift.up x) := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PicardDual.Construction
