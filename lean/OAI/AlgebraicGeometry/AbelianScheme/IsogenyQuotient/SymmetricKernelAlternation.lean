import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SymmetricFrameDiagonal
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BundleIntrinsicKernelPairing

/-! # Symmetric Kernel Alternation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SymmetricKernelAlternation.Construction

noncomputable section

/-!
The actual PoincareBundle pairing of a kernel with itself is alternating when the
source-line symmetry has its derived diagonal normalization. Equality
of the two genuine frames gives value one on every diagonal test point,
including infinitesimal points.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.KernelRectangle
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames

universe u

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (L : Picard.PoincareBundle.Line.Bundles.LineBundle (A ⊗ A).left)
  (D : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst A A) (snd A A) L)
  (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj L.sheaf ≅ L.sheaf)
  (f : A ⟶ B) [IsMonHom f] (F : Picard.PoincareBundle.FiberwiseMultiplication.KernelFrames (fst A A) (snd A A) L f D)
  (hdiag : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A).left).mapIso σ =
    Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A A).hom L (DiagonalLineSymmetry.Construction.groupDiagonal A) (DiagonalLineSymmetry.Construction.groupDiagonal A)
      (DiagonalLineSymmetry.Construction.groupDiagonal_swap A))

include hdiag

theorem symmetricKernelPairing_diagonal {T : Over S} (k : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f) :
    Picard.PoincareBundle.ConcreteKernelPairing.Concrete.value f f L D (Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondMultiplication L D σ) F (Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondFrames L D σ f F) k k = 1 := by
  let c := Picard.PoincareBundle.Biextension.KernelRectangle.crossPoint f f k k
  have hc : (k ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f) ≫ DiagonalLineSymmetry.Construction.groupDiagonal A = c := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [DiagonalLineSymmetry.Construction.groupDiagonal, c, Picard.PoincareBundle.Biextension.KernelRectangle.crossPoint]
  have hfixed : c ≫ (β_ A A).hom = c := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [c, Picard.PoincareBundle.Biextension.KernelRectangle.crossPoint]
  have hσ := SymmetricFrameDiagonal.Construction.fixedLineSymmetry_at_point (β_ A A).hom (DiagonalLineSymmetry.Construction.groupDiagonal A) (DiagonalLineSymmetry.Construction.groupDiagonal_swap A)
    L σ hdiag (k ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f) c hc hfixed
  have hframe := SymmetricFrameDiagonal.Construction.secondKernelFrame_eq_at_fixed_point L D σ f F k c
    (Picard.PoincareBundle.Biextension.KernelRectangle.crossPoint_fst f f k k).symm (Picard.PoincareBundle.Biextension.KernelRectangle.crossPoint_snd f f k k).symm hfixed hσ
  exact (Picard.PoincareBundle.Line.FrameUnits.frameRatio_eq_one_iff _ _).mpr hframe.symm

theorem symmetricNativeKernelPairing_alternating
    (ht : Picard.PoincareBundle.Biextension.Compatibility.TransverseFrames L D (Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondMultiplication L D σ)
      f f F (Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondFrames L D σ f F)) (T : Over S) (k : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f) :
    (Poincare.BundleIntrinsicKernelPairing.Construction.e45NativeKernelPairing f f L D (Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondMultiplication L D σ) F (Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondFrames L D σ f F) ht).pairValue k k = 1 := by
  apply CartierDuality.UnitValueDetection.Construction.Schemes.multiplicativeGroupUnitHom_injective T
  rw [Poincare.BundleIntrinsicKernelPairing.Construction.e45NativeKernelPairing_value, map_one]
  exact symmetricKernelPairing_diagonal L D σ f F hdiag k

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SymmetricKernelAlternation.Construction
