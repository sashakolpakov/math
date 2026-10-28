import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.SourceKernelCharacter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RepresentedKernelCharacterGroup
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageGroup

/-! # Source Kernel Cartier Embedding -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.SourceKernelCartierEmbedding.Construction

noncomputable section

/-! The finite source-map kernel embeds as an actual group scheme in
the Cartier dual of the original quotient kernel, with exact Picard recovery. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {B : Over (Spec (.of k))} [GrpObj B] [IsCommMonObj B]
  [IsProper B.hom] [Smooth B.hom] [GeometricallyIntegral B.hom]
  [IsLocallyNoetherian B.left]
  (D : FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine B B)
  (βv : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.inputLeft B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.inputRight B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.outputPoint B B)))
  (hβv : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βv))
  (βh : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.inputRight B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint B B)))
  (hβh : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βh))

variable {C : Over (Spec (.of k))} (q : B ⟶ C)
  (i : uliftYoneda.{u + 1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (hfac : uliftYoneda.map q ≫ i = ProductPicard.SheafMap.Construction.productNativePicardSheafMap (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv)

variable [IsAffineHom (q ⊗ₘ 𝟙 B).left] [Flat (q ⊗ₘ 𝟙 B).left]
  [Surjective (q ⊗ₘ 𝟙 B).left] [IsLocallyNoetherian (C ⊗ B).left]
  [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]

variable
  {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (DA : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
local notation "Q" => OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac

variable [GrpObj C] [IsMonHom q] [Mono i]
  [IsMonHom (PicardImage.SourceMap.Construction.picardImageSourceMap DA f i)]
  [IsFinite (PicardImage.SourceMap.Construction.picardImageSourceMap DA f i).left]
  [Flat (PicardImage.SourceMap.Construction.picardImageSourceMap DA f i).left]
  [LocallyOfFinitePresentation (PicardImage.SourceMap.Construction.picardImageSourceMap DA f i).left]
  (Y : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation _ (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))

include D βv hβv βh hβh q hfac in
set_option backward.isDefEq.respectTransparency false in
theorem picardImageSourceKernel_exists_cartier_embedding :
    ∃ c : Picard.Homomorphisms.Kernel.Construction.kernelScheme (PicardImage.SourceMap.Construction.picardImageSourceMap DA f i) ⟶ Y.dual.X,
      Mono c ∧ IsMonHom c ∧
      ∀ (T : Over (Spec (.of k))) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme (PicardImage.SourceMap.Construction.picardImageSourceMap DA f i)),
        CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T (Y.sectionEquiv T (x ≫ c)) =
          i.app (op T) (ULift.up (x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion (PicardImage.SourceMap.Construction.picardImageSourceMap DA f i))) := by
  let sourceMap := PicardImage.SourceMap.Construction.picardImageSourceMap DA f i
  let kernelSpace := Picard.Homomorphisms.Kernel.Construction.kernelScheme sourceMap
  let inclusion := Picard.Homomorphisms.Kernel.Construction.kernelInclusion sourceMap
  have : IsFinite kernelSpace.hom := (Picard.Homomorphisms.Kernel.Construction.kernelScheme_finiteLocallyFree sourceMap
    ⟨inferInstance, inferInstance, inferInstance⟩).1
  have : IsAffine kernelSpace.left := isAffine_of_isAffineHom kernelSpace.hom
  have : IsLocallyNoetherian kernelSpace.left := LocallyOfFiniteType.isLocallyNoetherian kernelSpace.hom
  let j := uliftYoneda.map inclusion ≫ i
  obtain ⟨χ, hχ⟩ := PicardImage.SourceKernelCharacter.Construction.picardImageSourceKernel_exists_character D βv hβv βh hβh q i hfac DA f inclusion
    (Picard.Homomorphisms.KernelGroup.Construction.kernelInclusion_comp sourceMap)
  have hχ' : CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f kernelSpace χ =
      j.app (op kernelSpace) (ULift.up (𝟙 kernelSpace)) := by
    change _ = i.app (op kernelSpace) (ULift.up ((𝟙 kernelSpace) ≫ inclusion))
    rw [Category.id_comp]
    exact hχ
  let c := RepresentedKernelCharacterMap.Construction.representedKernelCharacterMap f Y χ
  have hc : Mono c := RepresentedKernelCharacterMap.Construction.representedKernelCharacterMap_mono f Y j χ hχ'
  let H (T : Over (Spec (.of k))) :=
    (ProductPicard.ImageGroup.Construction.productPicardImageSectionHom (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv βh hβh q i hfac T).comp
      { toFun := fun x : T ⟶ kernelSpace => x ≫ inclusion
        map_one' := MonObj.one_comp inclusion
        map_mul' := fun x y => MonObj.mul_comp x y inclusion }
  have hH (T : Over (Spec (.of k))) (x : T ⟶ kernelSpace) : H T x = j.app (op T) (ULift.up x) := rfl
  have hg : IsMonHom c := RepresentedKernelCharacterGroup.Construction.representedKernelCharacterMap_isMonHom f Y j χ hχ' H hH
    (CartierDuality.PicardMonomorphism.Construction.KernelCharacters.parameterCharacterPicardHom_injective f)
  exact ⟨c, hc, hg, fun T x => RepresentedKernelCharacterMap.Construction.representedKernelCharacterMap_value f Y j χ hχ' x⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.SourceKernelCartierEmbedding.Construction
