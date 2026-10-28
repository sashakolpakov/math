import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FamilyPicardCharacters
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CoverDenseSurjectivity

/-! # Picard -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Picard

noncomputable section

/-! The actual kernel-character map is locally bijective onto the raw
homogeneous Picard pullback kernel on the full fppf site. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace Construction

universe u

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
variable (f : A ⟶ B) [IsMonHom f]

def rawPicardKernel : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := {c : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B).obj T //
    (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullbackPresheaf A B f).app T c = 1}
  map t := TypeCat.ofHom fun c => ⟨(Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B).map t c.val, by
    have hn := (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullbackPresheaf A B f).naturality_apply t c.val
    exact hn.trans ((congrArg ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A).map t) c.property).trans
      ((Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupPresheaf A).map t).hom.map_one)⟩
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro c
    apply Subtype.ext
    exact (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B).map_id_apply T c.val
  map_comp t v := by
    apply ConcreteCategory.hom_ext
    intro c
    apply Subtype.ext
    exact (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B).map_comp_apply t v c.val

def rawPicardKernelInclusion : rawPicardKernel f ⟶ Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B where
  app _T := TypeCat.ofHom Subtype.val
  naturality {_T _U} _t := rfl

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [LocallyOfFinitePresentation f.left]

def characterToRawPicardKernel : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj ⟶ rawPicardKernel f where
  app T := TypeCat.ofHom fun χ => ⟨CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f T.unop χ,
    CharacterPicard.Construction.parameterCharacterHomogeneousClass_pullback f T.unop χ⟩
  naturality {T U} t := by
    apply ConcreteCategory.hom_ext
    intro χ
    apply Subtype.ext
    exact (CartierDuality.ParameterLineNaturality.Construction.KernelCharacters.parameterCharacterHomogeneousClass_natural f t.unop χ).symm

theorem characterToRawPicardKernel_inclusion :
    characterToRawPicardKernel f ≫ rawPicardKernelInclusion f = CartierDuality.PicardMonomorphism.Construction.KernelCharacters.parameterCharacterRawMap f := rfl

variable {k : Type u} [Field k]
variable {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
variable (f : A ⟶ B) [IsMonHom f]
variable [IsFinite f.left] [Flat f.left] [Surjective f.left]
  [LocallyOfFinitePresentation f.left]

theorem characterToRawPicardKernel_injective (Q : Over (Spec (.of k))) :
    Function.Injective ((characterToRawPicardKernel f).app (.op Q)) := by
  intro χ ψ h
  exact CartierDuality.PicardMonomorphism.Construction.KernelCharacters.parameterCharacterHomogeneousClass_injective f Q (congrArg Subtype.val h)

theorem characterToRawPicardKernel_surjective_affine (Q : Over (Spec (.of k))) [IsAffine Q.left] :
    Function.Surjective ((characterToRawPicardKernel f).app (.op Q)) := by
  intro c
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Q ◁ f).left c.val.val = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (Q ⊗ A).left :=
    congrArg Subtype.val c.property
  obtain ⟨χ, hχ⟩ := FamilyPicardCharacters.Construction.familyLine_kernel_character_exists f Q c.val.val hc
  refine ⟨χ, Subtype.ext (Subtype.ext ?_)⟩
  exact (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass_val f Q χ).trans hχ.symm

theorem characterToRawPicardKernel_locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of k)))
      (characterToRawPicardKernel f) := by
  have : (algSpec (.of k)).IsCoverDense (Scheme.fppfTopology.over (Spec (.of k))) :=
    CartierDuality.SheafDescent.Construction.e56AlgSpecCoverDense (.of k)
  apply CoverDenseSurjectivity.Construction.locallySurjective_of_surjective_coverDense
    (Scheme.fppfTopology.over (Spec (.of k))) (algSpec (.of k)) (characterToRawPicardKernel f)
  intro R
  have : IsAffine ((algSpec (.of k)).obj R).left := by
    change IsAffine (Spec _)
    infer_instance
  exact characterToRawPicardKernel_surjective_affine f ((algSpec (.of k)).obj R)

theorem characterToRawPicardKernel_locallyInjective :
    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over (Spec (.of k)))
      (characterToRawPicardKernel f) :=
  Presheaf.isLocallyInjective_of_injective (Scheme.fppfTopology.over (Spec (.of k)))
    (characterToRawPicardKernel f) (fun T => characterToRawPicardKernel_injective f T.unop)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Picard
