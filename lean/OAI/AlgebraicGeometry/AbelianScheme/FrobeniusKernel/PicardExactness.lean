import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardSheafLimit
import Mathlib.CategoryTheory.Limits.Types.Equalizers

/-! # Picard Exactness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardExactness.Construction

noncomputable section

/-! On every parameter scheme, the kernel of Picard pullback consists
uniquely of the actual character lines of the isogeny kernel. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

section Trivial

variable {S : Scheme.{u}} (A B : Over S) [GrpObj A] [GrpObj B]

def trivialPicardPullbackSheaf : Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B ⟶ Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A where
  hom := {
    app T := TypeCat.ofHom fun _ => Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.trivialHomogeneousPicardClass A T.unop
    naturality := by
      intro T U t
      apply ConcreteCategory.hom_ext
      intro _
      have hn := (toSheafify (Scheme.fppfTopology.over S)
        (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A)).naturality_apply t (1 : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A).obj T)
      exact (congrArg ((toSheafify (Scheme.fppfTopology.over S)
        (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A)).app U)
        ((Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupPresheaf A).map t).hom.map_one).symm.trans hn }

theorem sheafifiedTrivialPicardPullback :
    (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
      (PicardLimit.Construction.trivialPicardPullbackPresheaf (A := A) (B := B)) = trivialPicardPullbackSheaf A B := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).property
  exact (toSheafify_naturality (Scheme.fppfTopology.over S)
    (PicardLimit.Construction.trivialPicardPullbackPresheaf (A := A) (B := B))).symm

end Trivial

variable {k : Type u} [Field k]
variable {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
variable (f : A ⟶ B) [IsMonHom f]
variable [IsFinite f.left] [Flat f.left] [Surjective f.left]
  [LocallyOfFinitePresentation f.left]

theorem picardPullback_kernel_character_unique (Q : Over (Spec (.of k)))
    (c : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (.op Q))
    (hc : (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom.app (.op Q) c =
      Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.trivialHomogeneousPicardClass A Q) :
    ∃! χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q),
      CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f Q χ = c := by
  let E := sheafToPresheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1)) ⋙
    (evaluation (Over (Spec (.of k)))ᵒᵖ (Type (u + 1))).obj (.op Q)
  have hL := isLimitForkMapOfIsLimit E (PicardSheafLimit.Construction.characterPicardKernel_condition f)
    (PicardSheafLimit.Construction.characterPicardKernel_isLimit f)
  apply Types.unique_of_type_equalizer _ _ hL c
  change (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom.app (.op Q) c =
    ((presheafToSheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1))).map
      (PicardLimit.Construction.trivialPicardPullbackPresheaf (A := A) (B := B))).hom.app (.op Q) c
  rw [sheafifiedTrivialPicardPullback]
  exact hc

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardExactness.Construction
