import OAI.AlgebraicGeometry.Resolution.Blowups.Global.LogarithmicLe
import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.BoundaryHistoryExtension

/-! # Unit History Extension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Adding an absent boundary component to the selected history leaves the native logarithmic ideal unchanged. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.logarithmicIdeal_extend_unit_history
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β γ : Type} {D : β → X.IdealSheafData}
    (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (e : γ ↪ β) (j : β) (hj : ∀ s, j ≠ e s)
    (hunit : D j = ⊤) (J : X.IdealSheafData) (n : ℕ) :
    (A.reindex (Finite.BoundaryHistoryExtension.Construction.extendSelectedBoundaryHistory e j hj)).logarithmicIdeal J n =
      (A.reindex e).logarithmicIdeal J n := by
  let : IsLocallyNoetherian X := A.locallyNoetherian
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ A.openCover
  intro i
  change A.indices at i
  change ((A.reindex (Finite.BoundaryHistoryExtension.Construction.extendSelectedBoundaryHistory e j hj)).logarithmicIdeal J n).comap (A.map i) =
    ((A.reindex e).logarithmicIdeal J n).comap (A.map i)
  rw [A.reindex_logarithmicIdeal_restrict, A.reindex_logarithmicIdeal_restrict]
  have hs : Ideal.span {A.equations i j} = ⊤ := by
    apply (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp
    rw [DifferentialUnitGluing.Construction.affineQuotientKernel_top, ← A.component, hunit, Scheme.IdealSheafData.comap_top]
  rw [Finite.BoundaryHistoryExtension.Construction.iteratedRelativeLogarithmicDifferentialIdeal_extend_unit_history
    (A.equations i) e j hj (Ideal.span_singleton_eq_top.mp hs)]

end

end OAI.AlgebraicGeometry.Resolution.Blowups
