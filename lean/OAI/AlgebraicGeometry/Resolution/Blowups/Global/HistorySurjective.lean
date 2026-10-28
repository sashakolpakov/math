import OAI.AlgebraicGeometry.Resolution.Blowups.Global.LogarithmicLe
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicBoundary

/-! # History Surjective -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A selected history containing every boundary label gives the full logarithmic ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.logarithmicIdeal_surjective_reindex
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β γ : Type} {D : β → X.IdealSheafData}
    (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (e : γ ↪ β) (he : Function.Surjective e)
    (J : X.IdealSheafData) (n : ℕ) :
    (A.reindex e).logarithmicIdeal J n = A.logarithmicIdeal J n := by
  let : IsLocallyNoetherian X := A.locallyNoetherian
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ A.openCover
  intro i
  change A.indices at i
  change ((A.reindex e).logarithmicIdeal J n).comap (A.map i) =
    (A.logarithmicIdeal J n).comap (A.map i)
  rw [A.reindex_logarithmicIdeal_restrict, A.logarithmicIdeal_restrict,
    Relative.LogarithmicBoundary.Construction.iteratedRelativeLogarithmicDifferentialIdeal_surjective_reindex ℂ (A.equations i) e he]

end

end OAI.AlgebraicGeometry.Resolution.Blowups
