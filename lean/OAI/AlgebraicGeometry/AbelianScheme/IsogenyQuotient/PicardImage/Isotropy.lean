import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.CoprimeKernelIso
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.SourceKernelCartierIso
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.SheafIso
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.DualData

/-! # Isotropy -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.Isotropy.Construction

noncomputable section

/-! Full source self-annihilation and the perfect native torsion pairing
construct the quotient dual, including its universal normalized line. -/

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

variable [GrpObj C] [IsMonHom q]

variable [Mono i]
  {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (DA : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
local notation "Q" => OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac

variable [IsCommMonObj C]
  [IsMonHom (SourceMap.Construction.picardImageSourceMap DA f i)]
  [IsFinite (SourceMap.Construction.picardImageSourceMap DA f i).left]
  [Flat (SourceMap.Construction.picardImageSourceMap DA f i).left]
  [LocallyOfFinitePresentation (SourceMap.Construction.picardImageSourceMap DA f i).left]

variable [Surjective (SourceMap.Construction.picardImageSourceMap DA f i).left]
  [IsFinite q.left] [IsProper C.hom] [Smooth C.hom] [GeometricallyConnected C.hom]
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable (φ : A ⟶ DA.abelian) [IsMonHom φ]
  (n d : ℕ) (hnd : n.Coprime d)
  (hsource : f ≫ q ≫ SourceMap.Construction.picardImageSourceMap DA f i = φ ^ n)
  (hk : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A), x ≫ φ = 1 → x ^ d = 1)
  (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)
  (P : Picard.PoincareBundle.Line.Bundles.LineBundle (DA.abelian ⊗ A).left)
  (Dh : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst DA.abelian A) (snd DA.abelian A) P)
  (Dv : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (snd DA.abelian A) (fst DA.abelian A) P)
  (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf ≅
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf)
  (hv : Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondMultiplication (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)) (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh) σ =
    Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv)
  (hp : Picard.PoincareBundle.Biextension.Compatibility.Interchange P Dh Dv)
  (hh : Picard.PoincareBundle.Symmetric.TransverseFrames.returnedFirst (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)) (Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv) σ =
    Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh)
  (e : (D.bundle.pullback (f ⊗ₘ f).left).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf)
  (hlag : Picard.PoincareBundle.NaturalPairingOrthogonal.SelfAnnihilating (Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap f n hf)
    (Picard.PoincareBundle.TorsionPairing.Poincare.torsionPairing φ P Dh Dv n σ hv hp hh))

variable (b : Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A n) (B := Torsion.Groups.Construction.nativeTorsionScheme A n)
    (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X))
  (hb : b.toSheafPairing.IsPerfect)
  (hnative :
    let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f)
    b.relativeAnnihilator F = F)

include D βv hβv βh hβh hfac hnd hsource hk hf hv hp hh e hlag b hb hnative in
set_option backward.isDefEq.respectTransparency false in
theorem picardImage_isIso_of_full_isotropy : IsIso i := by
  obtain ⟨eK, heKmon, heK⟩ := CoprimeKernelIso.Construction.picardImage_exists_coprime_kernelIso D βv hβv βh hβh q i hfac DA f
    φ n d hnd hsource hk hf P Dh Dv σ hv hp hh e hlag
  have : IsMonHom eK.hom := heKmon
  have hK := Picard.Homomorphisms.Kernel.Construction.kernelScheme_finiteLocallyFree f ⟨inferInstance, inferInstance, inferInstance⟩
  have : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom := hK.1
  have : Flat (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom := hK.2.1
  have : LocallyOfFinitePresentation (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom := hK.2.2
  let Y := CartierDuality.GroupRepresentatives.Construction.Schemes.characterGroupRepresentationOfRepresentable _ (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))
    (CartierDuality.PolarizedTorsion.Construction.characterSheaf_finiteLocallyFree _ (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
  obtain ⟨c, hciso, _hcmon, hc⟩ := Picard.SourceKernelCartierIso.Construction.picardImageSourceKernel_exists_cartier_iso
    D βv hβv βh hβh q i hfac DA f Y φ n d hnd hsource hk hf eK heK b hb hnative
  have : IsIso c := hciso
  exact SheafIso.Construction.picardImage_isIso_of_character_iso DA f Y i
    (ProductPicard.ImageGroup.Construction.productPicardImageSectionHom (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv βh hβh q i hfac)
    (fun _T _x => rfl) (Picard.Homomorphisms.Kernel.Construction.kernelInclusion (SourceMap.Construction.picardImageSourceMap DA f i)) c hc

include D βv hβv βh hβh hfac hnd hsource hk hf hv hp hh e hlag b hb hnative in
set_option backward.isDefEq.respectTransparency false in
def picardImageDualDataOfFullIsotropy : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B := by
  have : IsIso i := picardImage_isIso_of_full_isotropy D βv hβv βh hβh q i hfac DA f
    φ n d hnd hsource hk hf P Dh Dv σ hv hp hh e hlag b hb hnative
  exact DualData.Construction.picardImageDualData D βv hβv βh hβh q i hfac

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.Isotropy.Construction
