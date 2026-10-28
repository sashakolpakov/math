import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Picard
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-! # Picard Limit -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardLimit.Construction

noncomputable section

/-! The raw family Picard kernel is the actual presheaf equalizer of
pullback and the trivial class, with its universal property proved. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
variable (f : A ⟶ B) [IsMonHom f]

def trivialPicardPullbackPresheaf : Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B ⟶ Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A where
  app _ := TypeCat.ofHom fun _ => 1
  naturality {T U} t := by
    apply ConcreteCategory.hom_ext
    intro _
    exact ((Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupPresheaf A).map t).hom.map_one.symm

theorem rawPicardKernel_condition :
    Picard.Construction.rawPicardKernelInclusion f ≫ Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullbackPresheaf A B f =
      Picard.Construction.rawPicardKernelInclusion f ≫ trivialPicardPullbackPresheaf (A := A) (B := B) := by
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.hom_ext
  intro c
  exact c.property

def rawPicardKernelFork : Fork (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullbackPresheaf A B f)
    (trivialPicardPullbackPresheaf (A := A) (B := B)) :=
  Fork.ofι (Picard.Construction.rawPicardKernelInclusion f) (rawPicardKernel_condition f)

def rawPicardKernelLift (s : Fork (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullbackPresheaf A B f)
    (trivialPicardPullbackPresheaf (A := A) (B := B))) : s.pt ⟶ Picard.Construction.rawPicardKernel f where
  app T := TypeCat.ofHom fun c => ⟨s.ι.app T c,
    ConcreteCategory.congr_hom (NatTrans.congr_app s.condition T) c⟩
  naturality {T U} t := by
    apply ConcreteCategory.hom_ext
    intro c
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (s.ι.naturality t) c

def rawPicardKernel_isLimit : IsLimit (rawPicardKernelFork f) :=
  Fork.IsLimit.ofExistsUnique fun s => ⟨rawPicardKernelLift f s, rfl, by
    intro m hm
    apply NatTrans.ext
    funext T
    apply ConcreteCategory.hom_ext
    intro c
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hm T) c⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardLimit.Construction
