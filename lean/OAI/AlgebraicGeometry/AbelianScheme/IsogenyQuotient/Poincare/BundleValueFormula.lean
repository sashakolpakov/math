import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.KernelFrameRatio
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BundleSecondFrameComparison

/-! # Bundle Value Formula -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BundleValueFormula.Construction

noncomputable section

/-! The actual PoincareBundle pairing equals a ratio of original Poincare unit
frames, with the second frame carried by the same family symmetry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (φ : A.scheme ⟶ D.abelian.scheme) [IsMonHom φ]
  (σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf)
  {B : Over (Spec (.of k))} [GrpObj B] (f : A.scheme ⟶ B) [IsMonHom f]
  (hf : Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f ≫ φ = 1)
  (hv : Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondMultiplication (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ)
      (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication φ (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D)) σ =
    Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical φ (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D))

theorem e45PoincareValue_frameRatio {T : Over (Spec (.of k))}
    (z w : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f) (x y : T ⟶ A.scheme)
    (hz : z ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f = x) (hw : w ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f = y)
    (hx : x ≫ φ = 1) (hy : y ≫ φ = 1) :
    Picard.PoincareBundle.Canonical.KernelPairing.value φ (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
      (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D) f hf σ hv z w =
    Picard.PoincareBundle.Line.FrameUnits.frameRatio (AxisFrames.Construction.poincareHorizontalUnitFrame D (lift (x ≫ φ) y) ((lift_fst _ _).trans hx))
      (AxisFrames.Construction.poincareHorizontalUnitFrame D (lift (y ≫ φ) x) ((lift_fst _ _).trans hy) ≪≫
        SymmetryFibers.Construction.poincareSymmetryFiber D φ σ x y) := by
  let L := Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ
  let Dh := Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication φ (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D)
  let F := Picard.PoincareBundle.Pulled.KernelFrames.Poincare.kernelFrames φ (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) f hf
  let a := lift x y
  let hz' := hz.trans (lift_fst x y).symm
  let hw' := hw.trans (lift_snd x y).symm
  let c := Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) a (φ ⊗ₘ 𝟙 A.scheme) (lift (x ≫ φ) y)
    (SymmetryFibers.Construction.poincareSymmetryTarget_point D φ x y)
  have h0 := Canonical.KernelFrameRatio.Construction.canonicalKernelPairing_frameRatio_at φ (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
    (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D) f hf σ hv z w a hz' hw'
  have h1 := BundleKernelFrameComparison.Construction.poincareKernelFrame_comparison_at D φ f hf z a hz' (lift (x ≫ φ) y)
    (SymmetryFibers.Construction.poincareSymmetryTarget_point D φ x y) ((lift_fst _ _).trans hx)
  have h2 := BundleSecondFrameComparison.Construction.poincareSecondKernelFrame_comparison D φ σ f hf w x y hw ((lift_fst _ _).trans hy)
  exact h0.trans ((Picard.PoincareBundle.FrameRatioPullback.frameRatio_postcomp (F.frame z a hz')
    ((Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondFrames L Dh σ f F).frame w a hw') c).symm.trans (congrArg₂ Picard.PoincareBundle.Line.FrameUnits.frameRatio h1 h2))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BundleValueFormula.Construction
