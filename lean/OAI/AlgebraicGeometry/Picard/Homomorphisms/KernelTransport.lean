import OAI.AlgebraicGeometry.Picard.Homomorphisms.GeometricKernel

/-! # Kernel Transport -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelTransport.Construction

noncomputable section

/-! Remove the unit factor from geometric Poincare line bundles by the
actual scheme isomorphism, preserving the kernel of pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

def pullbackKernelClassEmbedding {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (s : X' ⟶ X) (t : Y' ≅ Y)
    (w : f' ≫ t.hom = s ≫ f) :
    {q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass Y // AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass X} ↪
    {q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass Y' // AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f' q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass X'} where
  toFun q := ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass t.hom q.val, by
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, w, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp,
      q.property, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial]⟩
  inj' q r h := Subtype.ext ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackIso t).injective (congrArg Subtype.val h))

variable {k : Type u} [Field k] [IsAlgClosed k] {g h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
variable {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (E : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
variable (f : A.scheme ⟶ B.scheme) [IsMonHom f]

def geometricDualKernelNativeLineEmbedding :
    {x : Over.mk (𝟙 (Spec (.of k))) ⟶ E.abelian.scheme //
      x ≫ DualPullback.Construction.dualPicardPullback D E f = 1} ↪
    {q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass B.scheme.left //
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.scheme.left} :=
  (GeometricKernel.Construction.geometricDualKernelLineEmbedding D E f).trans
    (pullbackKernelClassEmbedding ((𝟙_ (Over (Spec (.of k)))) ◁ f).left f.left
      (λ_ A.scheme).inv.left ((Over.forget (Spec (.of k))).mapIso (λ_ B.scheme).symm)
      (congrArg Over.Hom.left (leftUnitor_inv_naturality f)))

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelTransport.Construction
