import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.CharacterPullback
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.DualData

/-! # Picard Pullback -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardPullback.Construction

noncomputable section

/-! Pullback of actual homogeneous line bundles defines a natural group
map from the canonical original Picard dual, and kills the actual Cartier subgroup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {X : Over S} [GrpObj X] (f : X ⟶ A.scheme) [IsMonHom f]

local instance canonicalPicardPullbackGroup : GrpObj (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).abelian :=
  Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D)

def canonicalPicardPullbackHom (T : Over S) :
    (T ⟶ (DualData.Construction.canonicalDualAbelianData D).abelian.scheme) →*
      (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X).obj.obj (op T) :=
  (UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom f T).comp
    (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroupHomEquiv (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) T).toMonoidHom

set_option backward.isDefEq.respectTransparency false in
theorem canonicalPicardPullbackHom_natural {T U : Over S} (a : U ⟶ T)
    (x : T ⟶ (DualData.Construction.canonicalDualAbelianData D).abelian.scheme) :
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X).obj.map a.op (canonicalPicardPullbackHom D f T x) =
      canonicalPicardPullbackHom D f U (a ≫ x) := by
  change (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X).obj.map a.op
    (UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom f T ((Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).representable.homEquiv x)) =
      UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom f U ((Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).representable.homEquiv (a ≫ x))
  rw [(Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).representable.homEquiv_comp,
    UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom_apply, UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom_apply]
  exact ((Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback X A.scheme f).hom.naturality_apply a.op
    ((Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).representable.homEquiv x)).symm

def canonicalPicardPullbackSheafMap :
    uliftYoneda.{u + 1}.obj (DualData.Construction.canonicalDualAbelianData D).abelian.scheme ⟶
      (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X).obj where
  app T := TypeCat.ofHom (fun x => canonicalPicardPullbackHom D f T.unop x.down)
  naturality {T U} a := by
    apply ConcreteCategory.ext_apply
    intro x
    exact (canonicalPicardPullbackHom_natural D f a.unop x.down).symm

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))

theorem canonicalPicardPullbackHom_cartier (T : Over S) (x : T ⟶ C.dual.X) :
    canonicalPicardPullbackHom D f T (x ≫ DualData.Construction.canonicalCartierPicardInclusion D f C) = 1 := by
  change UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom f T
    ((Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).representable.homEquiv
      (x ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) C)) = 1
  rw [CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicard_apply]
  change UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom f T
    ((Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).representable.homEquiv
      ((Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).representable.homEquiv.symm
        (CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T (C.sectionEquiv T x)))) = 1
  rw [Equiv.apply_symm_apply]
  exact Parameter.CharacterPullback.Construction.parameterCharacterPicardHom_pullback_one f T (C.sectionEquiv T x)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardPullback.Construction
