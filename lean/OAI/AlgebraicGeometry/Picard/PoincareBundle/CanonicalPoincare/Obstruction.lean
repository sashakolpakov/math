import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TorsionKernelFrame
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.KernelTrivialization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrames

/-! # Obstruction -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.Obstruction

noncomputable section

/-!
# The canonical kernel obstruction constructed from Poincare normalization and symmetry

Both frames and their scheme-valued unit ratio are constructed here. No kernel-frame splitting or
isotropy conclusion is assumed. Identifying this normalization with the torsion Weil pairing and
proving compatibility with the biextension products remain separate mathematical steps.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.KernelTrivialization

variable {S : Scheme.{u}} {A B Z : Over S} [GrpObj A] [GrpObj B] [GrpObj Z]
  (f : A ⟶ B) [IsMonHom f] (φ : A ⟶ Z) [IsMonHom φ] (n : ℕ)
  (hker : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)
  (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (normalized : (Scheme.Modules.pullback (Poincare.KernelTrivialization.zeroSection (Z := Z) (X := A)).left).obj P.sheaf ≅
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)
  (symmetry : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf ≅
    (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf)

/-- The first frame comes directly from torsion containment and the normalized Poincare zero fiber. -/
def firstFrame : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Kernel.Scheme.kernelObject f ⊗ A).left ≅
    (Scheme.Modules.pullback (Kernel.Scheme.kernelInclusion f ⊗ₘ 𝟙 A).left).obj (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf :=
  Poincare.TorsionKernelFrame.kernelFrame f φ n hker P normalized

/-- Symmetry constructs the second actual normalized kernel frame. -/
def secondFrame : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (A ⊗ Kernel.Scheme.kernelObject f).left ≅
    (Scheme.Modules.pullback (𝟙 A ⊗ₘ Kernel.Scheme.kernelInclusion f).left).obj (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf :=
  Symmetric.KernelTrivialization.secondFrame (Kernel.Scheme.kernelInclusion f) (FirstBiextensionFactor.familyLine P (φ ^ n))
    (firstFrame f φ n hker P normalized) symmetry

/-- The canonical obstruction is an actual invertible function on every test-scheme kernel pair. -/
def value {T : Over S} (k l : T ⟶ Kernel.Scheme.kernelObject f) : Γ(T.left, ⊤)ˣ :=
  Kernel.IntersectionFrames.obstruction (Kernel.Scheme.kernelInclusion f) (Kernel.Scheme.kernelInclusion f) (FirstBiextensionFactor.familyLine P (φ ^ n))
    (firstFrame f φ n hker P normalized) (secondFrame f φ n hker P normalized symmetry) k l

/-- The constructed Poincare obstruction is natural also for nonreduced test schemes. -/
theorem value_naturality {T T' : Over S} (a : T' ⟶ T) (k l : T ⟶ Kernel.Scheme.kernelObject f) :
    value f φ n hker P normalized symmetry (a ≫ k) (a ≫ l) =
      Units.map a.left.appTop.hom (value f φ n hker P normalized symmetry k l) :=
  Kernel.IntersectionFrames.obstruction_naturality (Kernel.Scheme.kernelInclusion f) (Kernel.Scheme.kernelInclusion f)
    (FirstBiextensionFactor.familyLine P (φ ^ n)) (firstFrame f φ n hker P normalized)
    (secondFrame f φ n hker P normalized symmetry) a k l

/-- Triviality of the canonical obstruction is equality of the two constructed intersection frames. -/
theorem trivial_iff :
    (∀ (T : Over S) (k l : T ⟶ Kernel.Scheme.kernelObject f), value f φ n hker P normalized symmetry k l = 1) ↔
    Kernel.IntersectionFrames.horizontalFrame (Kernel.Scheme.kernelInclusion f) (Kernel.Scheme.kernelInclusion f)
      (FirstBiextensionFactor.familyLine P (φ ^ n)) (firstFrame f φ n hker P normalized) =
    Kernel.IntersectionFrames.verticalFrame (Kernel.Scheme.kernelInclusion f) (Kernel.Scheme.kernelInclusion f)
      (FirstBiextensionFactor.familyLine P (φ ^ n)) (secondFrame f φ n hker P normalized symmetry) :=
  Kernel.IntersectionFrames.obstruction_trivial_iff (Kernel.Scheme.kernelInclusion f) (Kernel.Scheme.kernelInclusion f)
    (FirstBiextensionFactor.familyLine P (φ ^ n)) (firstFrame f φ n hker P normalized)
    (secondFrame f φ n hker P normalized symmetry)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.Obstruction
