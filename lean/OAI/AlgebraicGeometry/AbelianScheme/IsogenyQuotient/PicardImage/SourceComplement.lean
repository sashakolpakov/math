import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.SourceKernelTorsion
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.KernelTorsionTests
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupKernelPowerDescent

/-! # Source Complement -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.SourceComplement.Construction

noncomputable section

/-! The source-map kernel exponent holds on every scheme-valued test.
Actual effective descent then constructs the complementary group map. -/

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

include D βv hβv βh hβh q hfac

omit [IsMonHom (SourceMap.Construction.picardImageSourceMap DA f i)] in
set_option backward.isDefEq.respectTransparency false in
theorem picardImageSourceKernel_torsion
    (n : ℕ) (hn : ∀ (U : Over (Spec (.of k))) (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), z ^ n = 1)
    (T : Over (Spec (.of k))) (x : T ⟶ C) (hx : x ≫ SourceMap.Construction.picardImageSourceMap DA f i = 1) :
    x ^ n = 1 := by
  apply Finite.KernelTorsionTests.Construction.finiteKernel_torsion_of_affine_noetherian_tests (SourceMap.Construction.picardImageSourceMap DA f i) n _ T x hx
  intro U _ _ z hz
  exact SourceKernelTorsion.Construction.picardImageSourceKernel_affine_torsion D βv hβv βh hβh q i hfac DA f z hz n hn

variable [Surjective (SourceMap.Construction.picardImageSourceMap DA f i).left]

set_option backward.isDefEq.respectTransparency false in
theorem exists_picardImageSource_complement
    (n : ℕ) (hn : ∀ (U : Over (Spec (.of k))) (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), z ^ n = 1) :
    ∃ v : DA.abelian ⟶ C, IsMonHom v ∧ SourceMap.Construction.picardImageSourceMap DA f i ≫ v = (𝟙 C) ^ n := by
  have : EffectiveEpi (SourceMap.Construction.picardImageSourceMap DA f i ⊗ₘ SourceMap.Construction.picardImageSourceMap DA f i) :=
    Picard.Homomorphisms.GroupDescent.Construction.effectiveEpi_tensor_over_of_fpqc (SourceMap.Construction.picardImageSourceMap DA f i) (SourceMap.Construction.picardImageSourceMap DA f i)
  exact GroupKernelPowerDescent.Construction.exists_groupKernel_power_complement (SourceMap.Construction.picardImageSourceMap DA f i) n
    (picardImageSourceKernel_torsion D βv hβv βh hβh q i hfac DA f n hn)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.SourceComplement.Construction
