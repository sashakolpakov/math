import OAI.ArithmeticGeometry.Descent.CMVariety.CanonicalDualComparisons
import OAI.ArithmeticGeometry.Descent.CMVariety.ConcreteFiberLevelRigidity

/-! # Group Level Comparisons -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.GroupLevelComparisons.Abelian.FamilyPoints

noncomputable section

/-! Literal group/level/endomorphism fiber rigidity supplies an actual
comparison preserving the canonical dual and its Poincare class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem unpolarized_comparison_of_actual_fiber_iso
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N r : ℕ} {δ : Fin g → ℕ}
    (F : ModuliObjects.Abelian.EnhancedAbelianData g δ N r S.left) (s₀ s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (h : ConcreteFiberLevelRigidity.Abelian.FamilyPoints.ActualEquivariantLevelFiberIso F.polarized.abelian F.polarized.level
      F.endomorphism s₀ s) :
    Nonempty (UnpolarizedComparisons.Abelian.UnpolarizedEnhancedIso (F.pullback s₀.left) (F.pullback s.left)) := by
  obtain ⟨e, he, hi, hl⟩ := h
  exact ⟨@CanonicalDualComparisons.Abelian.unpolarizedEnhancedIsoOfGroupLevel g N r δ
    (F.pullback s₀.left) (F.pullback s.left) e he hi hl⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.GroupLevelComparisons.Abelian.FamilyPoints
