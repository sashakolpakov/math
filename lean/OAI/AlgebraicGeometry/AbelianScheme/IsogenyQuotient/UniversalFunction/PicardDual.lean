import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PicardDual
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.DualData

/-! # Picard Dual -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.PicardDual.Construction

noncomputable section

/-! The actual Cartier quotient representing the whole Picard sheaf
carries its normalized universal Poincare line whenever the source
family has universal global functions, with no Noetherian restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] ParameterKernel.Construction.abelianIsogeny_locallyOfFinitePresentation

variable {S : Scheme.{0}} {g : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (v : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A)
  (Q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian Q)
  (i : uliftYoneda.{1}.obj Q.scheme ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B.scheme).obj)
  (hfac : uliftYoneda.map q.hom ≫ i = Canonical.PicardPullback.Construction.canonicalPicardPullbackSheafMap D v.hom)

variable (hB : GlobalFunctions.Construction.HasUniversalGlobalFunctions B.scheme) [IsIso i]
  (h1 : ∀ T : Over S, i.app (op T) (ULift.up (1 : T ⟶ Q.scheme)) = 1)

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
def universalFunctionPicardQuotientDualData : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B :=
  ((Noetherian.PicardDual.Construction.canonicalRelativePoincarePullbackLine D v).universalPicardQuotientDualData hB q.hom
    (fun {_T} a b h => Noetherian.PicardDual.Construction.canonicalRelativePoincarePullbackLine_eq_on_quotient D v Q q i hfac a b h)
    (Relative.PoincarePullbackLine.Construction.relativePoincarePullbackLine_homogeneous (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled (Canonical.DualData.Construction.canonicalDualAbelianData D)) v.hom)
    (Relative.PoincarePullbackLine.Construction.relativePoincarePullbackLine_secondAxis_class (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled (Canonical.DualData.Construction.canonicalDualAbelianData D)) v.hom)
    i (Noetherian.PicardDual.Construction.canonicalRelativePoincarePullbackLine_value D v Q q i hfac)
    (fun T => (h1 T).trans (Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.trivialHomogeneousPicardClass_eq_one B.scheme T).symm)).toBundled B Q.smoothDimension

theorem universalFunctionPicardQuotientDualData_value (T : Over S) (x : T ⟶ Q.scheme) :
    (universalFunctionPicardQuotientDualData D v Q q i hfac hB h1).representable.homEquiv x =
      i.app (op T) (ULift.up x) := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.PicardDual.Construction
