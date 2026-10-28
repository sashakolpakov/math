import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.SourceKernelCartierEmbedding
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CoprimeKernelCartierIso
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.GroupEmbeddingIso
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.KernelCartierComparison

/-! # Source Kernel Cartier Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.SourceKernelCartierIso.Construction

noncomputable section

/-! Full torsion self-annihilation makes the actual character embedding
an isomorphism, retaining its exact Picard recovery on every test scheme. -/

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

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup Picard.PoincareBundle.Kernel.Scheme.kernelGroup_commutative

variable [IsCommMonObj C] [IsFinite q.left]
  (φ : A ⟶ DA.abelian) [IsMonHom φ]
  (n d : ℕ) (hnd : n.Coprime d)
  (hsource : f ≫ q ≫ PicardImage.SourceMap.Construction.picardImageSourceMap DA f i = φ ^ n)
  (hφ : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A), x ≫ φ = 1 → x ^ d = 1)
  (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)
  (eK : Picard.PoincareBundle.Kernel.Scheme.kernelObject φ ≅ Picard.PoincareBundle.Kernel.Scheme.kernelObject q) [IsMonHom eK.hom]
  (heK : eK.hom ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion q = Picard.PoincareBundle.Kernel.Scheme.kernelInclusion φ ≫ f)
  (b : Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A n) (B := Torsion.Groups.Construction.nativeTorsionScheme A n)
    (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X))
  (hb : b.toSheafPairing.IsPerfect)
  (hlag :
    let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f)
    b.relativeAnnihilator F = F)

include D βv hβv βh hβh q hfac hnd hsource hφ hf eK heK b hb hlag in
set_option backward.isDefEq.respectTransparency false in
theorem picardImageSourceKernel_exists_cartier_iso :
    ∃ c : Picard.Homomorphisms.Kernel.Construction.kernelScheme (PicardImage.SourceMap.Construction.picardImageSourceMap DA f i) ⟶ Y.dual.X,
      IsIso c ∧ IsMonHom c ∧
      ∀ (T : Over (Spec (.of k))) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme (PicardImage.SourceMap.Construction.picardImageSourceMap DA f i)),
        CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T (Y.sectionEquiv T (x ≫ c)) =
          i.app (op T) (ULift.up (x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion (PicardImage.SourceMap.Construction.picardImageSourceMap DA f i))) := by
  obtain ⟨c, hcmono, hcgroup, hcvalue⟩ :=
    SourceKernelCartierEmbedding.Construction.picardImageSourceKernel_exists_cartier_embedding D βv hβv βh hβh q i hfac DA f Y
  have : Mono c := hcmono
  have : IsMonHom c := hcgroup
  have : IsCommMonObj Y.dual.X := Y.commutative
  have : IsFinite Y.dual.X.hom := Y.finite
  have : Flat Y.dual.X.hom := Y.flat
  let sourceMap := PicardImage.SourceMap.Construction.picardImageSourceMap DA f i
  have hK := Picard.Homomorphisms.Kernel.Construction.kernelScheme_finiteLocallyFree sourceMap
    ⟨inferInstance, inferInstance, inferInstance⟩
  have : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme sourceMap).hom := hK.1
  have : Flat (Picard.Homomorphisms.Kernel.Construction.kernelScheme sourceMap).hom := hK.2.1
  have hN := Intrinsic.KernelCartierComparison.Construction.categoricalKernel_finiteLocallyFree sourceMap
  have : IsFinite (Picard.PoincareBundle.Kernel.Scheme.kernelObject sourceMap).hom := hN.1
  have : Flat (Picard.PoincareBundle.Kernel.Scheme.kernelObject sourceMap).hom := hN.2.1
  have : LocallyOfFinitePresentation (Picard.PoincareBundle.Kernel.Scheme.kernelObject sourceMap).hom := hN.2.2
  obtain ⟨es⟩ := CoprimeKernelCartierIso.Construction.coprimeKernel_cartierSheafIso f q sourceMap φ n d hnd hsource hφ hf eK heK b hb hlag
  let en := Intrinsic.KernelCartierComparison.Construction.nativeKernelCartierIso f sourceMap Y es
  let s : Spec (.of k) := ⟨⊥, Ideal.isPrime_bot⟩
  let cG : Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme sourceMap) ⟶ Y.dual := Grp.homMk c
  have : Mono cG.hom.hom := hcmono
  have : IsIso cG := Finite.GroupEmbeddingIso.Construction.finiteGroup_mono_isIso_of_nonempty_iso _ _ cG ⟨en⟩ s
  have : IsIso c := (Grp.forget _).map_isIso cG
  exact ⟨c, inferInstance, hcgroup, hcvalue⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.SourceKernelCartierIso.Construction
