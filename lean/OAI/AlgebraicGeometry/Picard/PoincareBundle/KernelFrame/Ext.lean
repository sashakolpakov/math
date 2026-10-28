import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

/-! # Ext -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Ext

noncomputable section

/-! Complete multiplicative kernel-frame data are determined by their actual frame isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

variable {S : Scheme.{u}} {E A B X : Over S} [GrpObj A] [GrpObj B]
  {p : E ⟶ A} {r : E ⟶ X} {L : Line.Bundles.LineBundle E.left}
  {f : A ⟶ B} [IsMonHom f] {D : FiberwiseMultiplication.Multiplication p r L}

/-- Equality on all actual test-scheme frames determines the complete frame system. -/
theorem ext (K J : FiberwiseMultiplication.KernelFrames p r L f D)
    (h : ∀ (T : Over S) (k : T ⟶ Kernel.Scheme.kernelObject f) (a : T ⟶ E)
      (ha : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ p), K.frame k a ha = J.frame k a ha) : K = J := by
  cases K
  cases J
  congr 1
  funext T k a ha
  exact h T k a ha

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Ext
