import OAI.NumberTheory.PadicHodge.GeometricComparison.LargeFlasque
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.IndexEquivalence

/-! # Small Cover -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCover.SmallCoverFlasqueCech

noncomputable section

/-! Flasque Cech exactness for the original small covers and large coefficients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u v
variable (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{max u v} X)
  {ι : Type} (U : ι → Opens X)

theorem exactAt_succ [TopCat.Sheaf.IsFlasque F] (hU : iSup U = ⊤) (n : ℕ) :
    ((cechComplexFunctor U).obj F.obj).ExactAt (n + 1) := by
  let e : ULift.{max u v} ι ≃ ι := Equiv.ulift
  have hV : iSup (U ∘ e) = ⊤ := e.iSup_comp.trans hU
  exact (LargeFlasque.LargeFlasqueCech.exactAt_succ X F (U ∘ e) hV n).of_iso
    (Cech.IndexEquivalence.CechIndexEquivalence.complexIso e U F.obj)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCover.SmallCoverFlasqueCech
