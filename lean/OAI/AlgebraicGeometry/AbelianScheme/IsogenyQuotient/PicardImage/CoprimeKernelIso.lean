import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.SourceComplement
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.FamilyRecovery
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.Biextension
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.CoprimeKernelIso

/-! # Coprime Kernel Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.CoprimeKernelIso.Construction

noncomputable section

/-! Full source isotropy and actual image-line recovery identify the
source polarization kernel with the Picard image isogeny kernel. -/

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

include D βv hβv βh hβh hfac hnd hsource hk hf hv hp hh e hlag in
set_option backward.isDefEq.respectTransparency false in
theorem picardImage_exists_coprime_kernelIso :
    ∃ e : Picard.PoincareBundle.Kernel.Scheme.kernelObject φ ≅ Picard.PoincareBundle.Kernel.Scheme.kernelObject q, IsMonHom e.hom ∧
      e.hom ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion q = Picard.PoincareBundle.Kernel.Scheme.kernelInclusion φ ≫ f := by
  have hnf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1 := by
    intro T x
    apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)).mp
    rw [MonObj.pow_comp, MonObj.one_comp]
    apply hf T (x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)
    rw [Category.assoc, Picard.Homomorphisms.KernelGroup.Construction.kernelInclusion_comp, MonObj.comp_one]
  obtain ⟨v, _hvmon, hdual⟩ := SourceComplement.Construction.exists_picardImageSource_complement D βv hβv βh hβh q i hfac DA f n hnf
  let eQ := FamilyRecovery.Construction.picardImageFamilySourcePullbackIso D βv hβv βh hβh q i hfac f ≪≫ e
  let eK := Picard.PoincareBundle.Poincare.CoprimeKernelIso.kernelIso φ f q (SourceMap.Construction.picardImageSourceMap DA f i) n d hnd
    hsource v hdual hk hf P Dh Dv σ hv hp hh
    (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac))
    (Multiplications.Construction.picardImageHorizontalMultiplication D βv hβv βh hβh q i hfac)
    (Multiplications.Construction.picardImageVerticalMultiplication D βv hβv βh hβh q i hfac)
    (Biextension.Construction.picardImageMultiplications_interchange D βv hβv βh hβh q i hfac) eQ hlag
  exact ⟨eK, inferInstance,
    Picard.PoincareBundle.CoprimeKernelEmbedding.map_inclusion φ f q (SourceMap.Construction.picardImageSourceMap DA f i) n d hnd hsource v hdual hk⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.CoprimeKernelIso.Construction
