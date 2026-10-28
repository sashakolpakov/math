import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.KernelTrivialization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

/-! # Torsion Kernel Frame -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TorsionKernelFrame

noncomputable section

/-!
# Kernel containment constructs the normalized Poincare kernel frame in every characteristic
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.KernelTrivialization

variable {S : Scheme.{u}} {A B Z X : Over S} [GrpObj A] [GrpObj B] [GrpObj Z]
  (f : A ⟶ B) [IsMonHom f] (φ : A ⟶ Z) [IsMonHom φ] (n : ℕ)
  (hker : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)

include hker in
/-- Testing the actual represented kernel gives scheme-theoretic annihilation by the multiple. -/
theorem multiple_annihilates_kernel : Kernel.Scheme.kernelInclusion f ≫ φ ^ n = 1 := by
  rw [MonObj.comp_pow, ← MonObj.pow_comp,
    hker (Kernel.Scheme.kernelObject f) (Kernel.Scheme.kernelInclusion f) (Kernel.Scheme.kernelInclusion_comp f), MonObj.one_comp]

variable (P : Line.Bundles.LineBundle (Z ⊗ X).left)
  (normalized : (Scheme.Modules.pullback (KernelTrivialization.zeroSection (Z := Z) (X := X)).left).obj P.sheaf ≅
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left)

/-- The actual frame on the scheme kernel product follows from torsion containment and Poincare normalization. -/
def kernelFrame : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Kernel.Scheme.kernelObject f ⊗ X).left ≅
    (Scheme.Modules.pullback (Kernel.Scheme.kernelInclusion f ⊗ₘ 𝟙 X).left).obj (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf :=
  KernelTrivialization.kernelFrame (Kernel.Scheme.kernelInclusion f) (φ ^ n)
    (multiple_annihilates_kernel f φ n hker) P normalized

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TorsionKernelFrame
