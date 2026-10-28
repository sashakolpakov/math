import OAI.AlgebraicGeometry.FormalGeometry.Completion.SchemeImageDominance

/-! # Dominant Closed Factorization -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.DominantClosedFactorization.Construction

noncomputable section

/-! Factorization through a closed subscheme is detected after a
scheme-theoretically dominant pullback. This retains nilpotent structure. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

theorem factorThroughClosed_of_dominant {X Y Z W : Scheme.{u}}
    (p : X ⟶ Y) [IsSchemeTheoreticallyDominant p]
    (f : Y ⟶ Z) (i : W ⟶ Z) [IsClosedImmersion i]
    (g : X ⟶ W) (hg : p ≫ f = g ≫ i) : ∃ h : Y ⟶ W, h ≫ i = f := by
  have hk : (p ≫ f).ker = f.ker := by
    rw [Scheme.Hom.ker_comp, p.ker_eq_bot, Scheme.IdealSheafData.map_bot]
  have hi : i.ker ≤ f.ker := by
    rw [← hk, hg]
    exact Scheme.Hom.le_ker_comp g i
  exact ⟨IsClosedImmersion.lift i f hi, IsClosedImmersion.lift_fac i f hi⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.DominantClosedFactorization.Construction
