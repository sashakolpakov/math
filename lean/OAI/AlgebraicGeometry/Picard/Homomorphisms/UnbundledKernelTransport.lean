import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledGeometricKernel
import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelTransport

/-! # Unbundled Kernel Transport -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledKernelTransport.Construction.UnbundledPicard

noncomputable section

/-! Transport geometric Poincare classes to the actual target scheme
through the product's unit isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
variable (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (E : UnbundledDualData.Construction.UnbundledPicard.DualData B) (f : A ⟶ B) [IsMonHom f]

def geometricDualKernelNativeLineEmbedding :
    {x : Over.mk (𝟙 (Spec (.of k))) ⟶ E.abelian // x ≫ UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D E f = 1} ↪
    {q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass B.left //
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left} :=
  (UnbundledGeometricKernel.Construction.UnbundledPicard.geometricDualKernelLineEmbedding D E f).trans
    (KernelTransport.Construction.pullbackKernelClassEmbedding ((𝟙_ (Over (Spec (.of k)))) ◁ f).left f.left
      (λ_ A).inv.left ((Over.forget (Spec (.of k))).mapIso (λ_ B).symm)
      (congrArg Over.Hom.left (leftUnitor_inv_naturality f)))

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledKernelTransport.Construction.UnbundledPicard
