import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsotropicPicardImage
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.Isotropy

/-! # Isotropic Picard Dual -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.IsotropicPicardDual.Construction

noncomputable section

/-! The actual descended Poincare line represents the whole quotient
Picard sheaf under the full perfect self-annihilating torsion pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility

universe u
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {k : Type u} [Field k] {A B : Over (Spec (.of k))}
  [GrpObj A] [IsCommMonObj A] [GrpObj B]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (DA : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A)
  (φ : A ⟶ DA.abelian) [IsMonHom φ] (P : Picard.PoincareBundle.Line.Bundles.LineBundle (DA.abelian ⊗ A).left)
  (Dh : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst DA.abelian A) (snd DA.abelian A) P) (Dv : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (snd DA.abelian A) (fst DA.abelian A) P) (n : ℕ)
  (e : (Scheme.Modules.pullback (β_ A A).hom.left).obj (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf ≅
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf)
  (hv : Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondMultiplication (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)) (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh) e =
    Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv)
  (hi : Picard.PoincareBundle.Biextension.Compatibility.Interchange P Dh Dv)
  (hh : Picard.PoincareBundle.Symmetric.TransverseFrames.returnedFirst (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)) (Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv) e =
    Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh)
  (f : A ⟶ B) [IsMonHom f]
  (hker : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)
  (hlag :
    let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A n) (MorphismKernel.Construction.nativeMorphismKernel f)
    (Poincare.LineDescent.Construction.poincareNativeTorsionPairing φ P Dh Dv n e hv hi hh).relativeAnnihilator F = F)
  [IsFinite f.left] [Flat f.left] [Surjective f.left]
  [IsLocallyNoetherian (B ⊗ B).left] [IsLocallyNoetherian B.left]

variable [IsAlgClosed k] [IsCommMonObj B] [IsProper B.hom] [Smooth B.hom]
  [GeometricallyIntegral B.hom]
  [IsLocallyNoetherian (B ⊗ (B ⊗ B)).left] [IsLocallyNoetherian ((B ⊗ B) ⊗ B).left]

variable {C : Over (Spec (.of k))} [GrpObj C] [IsCommMonObj C]
  [IsProper C.hom] [Smooth C.hom] [GeometricallyConnected C.hom]
  (q : B ⟶ C) [IsMonHom q] [IsFinite q.left] [Flat q.left] [Surjective q.left]
  [LocallyOfFinitePresentation q.left]
  (i : uliftYoneda.{u + 1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj) [Mono i]
  (hfac : uliftYoneda.map q ≫ i = IsotropicPicardSheaf.Construction.nativeIsotropicQuotientPicardSheafMap φ P Dh Dv n e hv hi hh f hker hlag)
  [IsAffineHom (q ⊗ₘ 𝟙 B).left] [Flat (q ⊗ₘ 𝟙 B).left]
  [Surjective (q ⊗ₘ 𝟙 B).left] [IsLocallyNoetherian (C ⊗ B).left]
  [LocallyOfFinitePresentation f.left]
  [IsMonHom (PicardImage.SourceMap.Construction.picardImageSourceMap DA f i)]
  [IsFinite (PicardImage.SourceMap.Construction.picardImageSourceMap DA f i).left] [Flat (PicardImage.SourceMap.Construction.picardImageSourceMap DA f i).left]
  [Surjective (PicardImage.SourceMap.Construction.picardImageSourceMap DA f i).left]
  [LocallyOfFinitePresentation (PicardImage.SourceMap.Construction.picardImageSourceMap DA f i).left]
  (d : ℕ) (hnd : n.Coprime d)
  (hsource : f ≫ q ≫ PicardImage.SourceMap.Construction.picardImageSourceMap DA f i = φ ^ n)
  (hk : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A), x ≫ φ = 1 → x ^ d = 1)
  (hb : (Poincare.LineDescent.Construction.poincareNativeTorsionPairing φ P Dh Dv n e hv hi hh).toSheafPairing.IsPerfect)

include hfac hnd hsource hk hb in
set_option backward.isDefEq.respectTransparency false in
theorem nativeIsotropicPicardImage_isIso : IsIso i := by
  let R := IsotropicRigidification.Construction.nativeIsotropicQuotientRigidifiedLine φ P Dh Dv n e hv hi hh f hker hlag
  let hkf := Picard.PoincareBundle.Poincare.TorsionKernelFrame.multiple_annihilates_kernel f φ n hker
  let hz := Picard.PoincareBundle.TorsionPairing.Poincare.kernel_isotropic φ P Dh Dv n e hv hi hh f hker
    (Poincare.LineDescent.Construction.poincareNativeKernel_selfAnnihilating φ P Dh Dv n e hv hi hh f hker hlag)
  let βv := Picard.PoincareBundle.CanonicalPoincare.VerticalProduct.product (φ ^ n) P Dh Dv hi f hkf e hv hh hz
  let βh := Picard.PoincareBundle.CanonicalPoincare.Product.product (φ ^ n) P Dh Dv hi f hkf e hv hh hz
  have hβv : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βv) :=
    Picard.PoincareBundle.CanonicalPoincare.VerticalProduct.product_isIso (φ ^ n) P Dh Dv hi f hkf e hv hh hz
  have hβh : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βh) :=
    Picard.PoincareBundle.CanonicalPoincare.Product.product_isIso (φ ^ n) P Dh Dv hi f hkf e hv hh hz
  exact PicardImage.Isotropy.Construction.picardImage_isIso_of_full_isotropy R βv hβv βh hβh q i hfac DA f φ n d hnd hsource hk hker
    P Dh Dv e hv hi hh (Poincare.LineDescent.Construction.nativeIsotropicQuotientLine_pullbackIso φ P Dh Dv n e hv hi hh f hker hlag)
    (Poincare.LineDescent.Construction.poincareNativeKernel_selfAnnihilating φ P Dh Dv n e hv hi hh f hker hlag)
    (Poincare.LineDescent.Construction.poincareNativeTorsionPairing φ P Dh Dv n e hv hi hh) hb hlag

include hfac hnd hsource hk hb in
set_option backward.isDefEq.respectTransparency false in
def nativeIsotropicPicardImageDualData : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B := by
  have : IsIso i := nativeIsotropicPicardImage_isIso DA φ P Dh Dv n e hv hi hh f hker hlag q i hfac d hnd hsource hk hb
  let R := IsotropicRigidification.Construction.nativeIsotropicQuotientRigidifiedLine φ P Dh Dv n e hv hi hh f hker hlag
  let hkf := Picard.PoincareBundle.Poincare.TorsionKernelFrame.multiple_annihilates_kernel f φ n hker
  let hz := Picard.PoincareBundle.TorsionPairing.Poincare.kernel_isotropic φ P Dh Dv n e hv hi hh f hker
    (Poincare.LineDescent.Construction.poincareNativeKernel_selfAnnihilating φ P Dh Dv n e hv hi hh f hker hlag)
  let βv := Picard.PoincareBundle.CanonicalPoincare.VerticalProduct.product (φ ^ n) P Dh Dv hi f hkf e hv hh hz
  let βh := Picard.PoincareBundle.CanonicalPoincare.Product.product (φ ^ n) P Dh Dv hi f hkf e hv hh hz
  have hβv : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βv) :=
    Picard.PoincareBundle.CanonicalPoincare.VerticalProduct.product_isIso (φ ^ n) P Dh Dv hi f hkf e hv hh hz
  have hβh : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βh) :=
    Picard.PoincareBundle.CanonicalPoincare.Product.product_isIso (φ ^ n) P Dh Dv hi f hkf e hv hh hz
  exact PicardImage.DualData.Construction.picardImageDualData R βv hβv βh hβh q i hfac

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.IsotropicPicardDual.Construction
