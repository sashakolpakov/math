import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SymmetricFrameDiagonal

/-! # Bundle Second Frame Formula -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BundleSecondFrameFormula.Construction

noncomputable section

/-! The actual second kernel frame is the first frame at the exchanged
point, followed by its canonical fiber comparison and line symmetry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames

universe u

set_option backward.isDefEq.respectTransparency false in
theorem secondKernelFrame_formula {S : Scheme.{u}} {A B T : Over S} [GrpObj A] [GrpObj B]
    (L : Picard.PoincareBundle.Line.Bundles.LineBundle (A ⊗ A).left)
    (D : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst A A) (snd A A) L)
    (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj L.sheaf ≅ L.sheaf)
    (f : A ⟶ B) [IsMonHom f] (F : Picard.PoincareBundle.FiberwiseMultiplication.KernelFrames (fst A A) (snd A A) L f D)
    (z : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f) (a b : T ⟶ A ⊗ A)
    (ha : z ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f = a ≫ snd A A)
    (hb : z ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f = b ≫ fst A A)
    (hs : a ≫ (β_ A A).hom = b) :
    (Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondFrames L D σ f F).frame z a ha =
      (F.frame z b hb ≪≫ (Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A A).hom L a b hs).symm) ≪≫
        (Scheme.Modules.pullback a.left).mapIso σ := by
  cases hs
  change Picard.PoincareBundle.Line.FiberIsomorphisms.transportFrame (L.pullback (β_ A A).hom.left) L σ a
    ((Picard.PoincareBundle.Symmetric.MultiplicativeFrames.exchangedFrames L D f F).frame z a ha) = _
  rw [Picard.PoincareBundle.Symmetric.MultiplicativeFrames.exchangedFrames, SymmetricFrameDiagonal.Construction.kernelFrames_congrCoordinates_frame]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BundleSecondFrameFormula.Construction
