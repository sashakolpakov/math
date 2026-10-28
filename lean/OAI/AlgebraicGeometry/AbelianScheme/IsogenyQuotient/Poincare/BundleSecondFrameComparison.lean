import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BundleKernelFrameComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BundleSecondFrameFormula
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.SymmetryFrameFormula
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FrameSymmetryTransport

/-! # Bundle Second Frame Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BundleSecondFrameComparison.Construction

noncomputable section

/-! PoincareBundle's second kernel frame is the original horizontal Poincare
frame transported by the actual polarization-family symmetry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (φ : A.scheme ⟶ D.abelian.scheme) [IsMonHom φ]
  (σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf)
  {B : Over (Spec (.of k))} [GrpObj B] (f : A.scheme ⟶ B) [IsMonHom f]
  (hf : Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f ≫ φ = 1)

set_option backward.isDefEq.respectTransparency false in
theorem poincareSecondKernelFrame_comparison {T : Over (Spec (.of k))}
    (z : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f) (x y : T ⟶ A.scheme) (hz : z ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f = y)
    (hu : lift (y ≫ φ) x ≫ fst D.abelian.scheme A.scheme = 1) :
    (Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondFrames (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ)
      (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication φ (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D)) σ f
      (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.kernelFrames φ (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) f hf)).frame
      z (lift x y) (hz.trans (lift_snd _ _).symm) ≪≫
        Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift x y) (φ ⊗ₘ 𝟙 A.scheme) (lift (x ≫ φ) y)
          (SymmetryFibers.Construction.poincareSymmetryTarget_point D φ x y) =
      AxisFrames.Construction.poincareHorizontalUnitFrame D (lift (y ≫ φ) x) hu ≪≫ SymmetryFibers.Construction.poincareSymmetryFiber D φ σ x y := by
  let P := Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D
  let L := Picard.PoincareBundle.FirstBiextensionFactor.familyLine P φ
  let Dh := Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication φ P (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D)
  let F := Picard.PoincareBundle.Pulled.KernelFrames.Poincare.kernelFrames φ P (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) f hf
  have hs : lift x y ≫ (β_ A.scheme A.scheme).hom = lift y x := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [Category.assoc, braiding_hom_fst, braiding_hom_snd, lift_fst, lift_snd]
  have hF := BundleKernelFrameComparison.Construction.poincareKernelFrame_comparison_at D φ f hf z (lift y x)
    (hz.trans (lift_fst _ _).symm) (lift (y ≫ φ) x) (SymmetryFibers.Construction.poincareSymmetryTarget_point D φ y x) hu
  have hS := BundleSecondFrameFormula.Construction.secondKernelFrame_formula L Dh σ f F z (lift x y) (lift y x)
    (hz.trans (lift_snd _ _).symm) (hz.trans (lift_fst _ _).symm) hs
  change (Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondFrames L Dh σ f F).frame z (lift x y) _ =
    (F.frame z (lift y x) _ ≪≫
      (Picard.PoincareBundle.GlobalPullbackFrame.comparison (β_ A.scheme A.scheme).hom L (lift x y) (lift y x) hs).symm) ≪≫
        (Scheme.Modules.pullback (lift x y).left).mapIso σ at hS
  rw [← FiberProductOrigin.Construction.fiberPullbackIso_eq_comparison] at hS
  let a := Picard.PoincareBundle.Line.Fibers.fiberPullbackIso P (lift y x) (φ ⊗ₘ 𝟙 A.scheme) (lift (y ≫ φ) x) (SymmetryFibers.Construction.poincareSymmetryTarget_point D φ y x)
  let b := Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L (lift x y) (β_ A.scheme A.scheme).hom (lift y x) hs
  let c := Picard.PoincareBundle.Line.Fibers.fiberPullbackIso P (lift x y) (φ ⊗ₘ 𝟙 A.scheme) (lift (x ≫ φ) y) (SymmetryFibers.Construction.poincareSymmetryTarget_point D φ x y)
  exact (congrArg (fun v => v ≪≫ c) hS).trans
    ((FrameSymmetryTransport.Construction.frame_symmetry_transport (F.frame z (lift y x) (hz.trans (lift_fst _ _).symm)) a b
      ((Scheme.Modules.pullback (lift x y).left).mapIso σ) c (AxisFrames.Construction.poincareHorizontalUnitFrame D _ hu) hF).trans
      (congrArg (fun v => AxisFrames.Construction.poincareHorizontalUnitFrame D (lift (y ≫ φ) x) hu ≪≫ v)
        (SymmetryFrameFormula.Construction.poincareSymmetryFiber_formula D φ σ x y hs).symm))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BundleSecondFrameComparison.Construction
