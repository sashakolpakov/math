import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilAmpleLineDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingPullback

/-! # Weil Ample Product Line -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilAmpleProductLine

noncomputable section

/-! The ample quotient line constructs a product line recovering the required Poincare multiple under the actual product quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

attribute [local instance] Kernel.Scheme.kernelGroup
attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] [IsAlgClosed k] {a : ℕ}
  {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {δ : Fin a → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (n : ℕ) (hn : 0 < n)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
  (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)
  (hlag : WeilData.SelfAnnihilating D pol.isogeny n hn
    (Kernel.ContainmentMap.torsionMap f.hom n hf))

include hlag

/-- The constructed difference line recovers the original Poincare multiple as an actual sheaf isomorphism. -/
theorem exists_ample_line_recovery :
    ∃ N : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.scheme.left,
      N.IsAmple ∧ Nonempty ((N.pullback η[B.scheme].left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of k))) ∧
      Nonempty ((Scheme.Modules.pullback (f.hom ⊗ₘ f.hom).left).obj
        (InducingClass.Bundle.line B.scheme N).sheaf ≅
          (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (pol.isogeny.hom ^ n)).sheaf) := by
  obtain ⟨N, hN, o, ⟨e⟩⟩ := WeilAmpleLineDescent.exists_ample_inducing_pullback D pol n hn f hf hlag
  exact ⟨N, hN, o, ⟨InducingPullback.Bundle.recoveryIso f.hom N
    (D.poincare.pullback ((pol.isogeny.hom ^ n) ⊗ₘ 𝟙 A.scheme).left) e⟩⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilAmpleProductLine
