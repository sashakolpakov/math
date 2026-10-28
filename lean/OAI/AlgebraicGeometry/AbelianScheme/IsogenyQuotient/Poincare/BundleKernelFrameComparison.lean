import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PulledMultiplicationUnits
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberProductOrigin
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.FrameReferenceUnit

/-! # Bundle Kernel Frame Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BundleKernelFrameComparison.Construction

noncomputable section

/-! PoincareBundle's actual first kernel frame is the original horizontal Poincare
unit frame, through the canonical comparison of the family-line fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (φ : A.scheme ⟶ D.abelian.scheme) [IsMonHom φ]
  {B : Over (Spec (.of k))} [GrpObj B] (f : A.scheme ⟶ B) [IsMonHom f]
  (hf : Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f ≫ φ = 1)

include hf in
omit [IsAlgClosed k] [IsMonHom φ] [IsMonHom f] in
theorem poincareKernelFrame_image_neutral {T : Over (Spec (.of k))}
    (z : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f) (a : T ⟶ A.scheme ⊗ A.scheme)
    (ha : z ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f = a ≫ fst A.scheme A.scheme) :
    (a ≫ (φ ⊗ₘ 𝟙 A.scheme)) ≫ fst D.abelian.scheme A.scheme = 1 := by
  rw [Category.assoc, tensorHom_fst, ← Category.assoc, ← ha, Category.assoc, hf, MonObj.comp_one]

set_option backward.isDefEq.respectTransparency false in
theorem poincareKernelFrame_comparison {T : Over (Spec (.of k))}
    (z : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f) (a : T ⟶ A.scheme ⊗ A.scheme)
    (ha : z ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f = a ≫ fst A.scheme A.scheme) :
    (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.kernelFrames φ (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) f hf).frame z a ha ≪≫
      Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) a (φ ⊗ₘ 𝟙 A.scheme) (a ≫ (φ ⊗ₘ 𝟙 A.scheme)) rfl =
      AxisFrames.Construction.poincareHorizontalUnitFrame D (a ≫ (φ ⊗ₘ 𝟙 A.scheme)) (poincareKernelFrame_image_neutral D φ f hf z a ha) :=
  Kernel.FrameReferenceUnit.Construction.kernelFrame_to_originalUnit φ (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D)
    f hf z a ha (poincareKernelFrame_image_neutral D φ f hf z a ha)

theorem poincareKernelFrame_comparison_at {T : Over (Spec (.of k))}
    (z : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f) (a : T ⟶ A.scheme ⊗ A.scheme)
    (ha : z ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f = a ≫ fst A.scheme A.scheme)
    (r : T ⟶ D.abelian.scheme ⊗ A.scheme) (hr : a ≫ (φ ⊗ₘ 𝟙 A.scheme) = r)
    (hu : r ≫ fst D.abelian.scheme A.scheme = 1) :
    (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.kernelFrames φ (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) f hf).frame z a ha ≪≫
      Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) a (φ ⊗ₘ 𝟙 A.scheme) r hr =
      AxisFrames.Construction.poincareHorizontalUnitFrame D r hu := by
  cases hr
  exact poincareKernelFrame_comparison D φ f hf z a ha

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BundleKernelFrameComparison.Construction
