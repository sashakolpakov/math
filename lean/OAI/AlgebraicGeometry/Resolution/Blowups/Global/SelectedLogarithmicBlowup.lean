import OAI.AlgebraicGeometry.Resolution.Blowups.Global.LogarithmicBlowupBound
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.LogarithmicLe
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.Labels

/-! # Selected Logarithmic Blowup -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Actual global blowups retain the logarithmic bound for selected old labels and the new exceptional label. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.logarithmicIdeal_eq_of_boundary_eq
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β : Type} {D E : β → X.IdealSheafData}
    (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (B : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f E)
    (hDE : D = E) (J : X.IdealSheafData) (n : ℕ) : A.logarithmicIdeal J n = B.logarithmicIdeal J n := by
  subst E
  exact A.logarithmicIdeal_eq_atlas B J n

theorem Global.SelectedLogarithmicBlowup.Construction.globalBlowup_preserves_selected_logarithmic_order_bound
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} (I J : X.IdealSheafData) (hI : I ≠ ⊥)
    {β γ : Type} [Fintype γ] (D : β → X.IdealSheafData) (e : γ ↪ β)
    (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) (B : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D)
    (B' : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D))
    (m : ℕ) (hp : J ≤ I ^ m) (hbound : (B.reindex e).logarithmicIdeal J m = ⊤) :
    (B'.reindex (Function.Embedding.optionMap e)).logarithmicIdeal
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m) m = ⊤ := by
  let E := fun l => D (e l)
  let A' : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I E := A.pullbackLabels (fun l => some (e l))
    (by intro i j s hi hj; exact e.injective ((Option.some.inj hi).trans (Option.some.inj hj).symm))
    E (fun _ => rfl)
  have he : (fun l => CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D (Function.Embedding.optionMap e l)) =
      CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI E := by
    funext l
    cases l <;> rfl
  let C : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI E) :=
    he ▸ B'.reindex (Function.Embedding.optionMap e)
  have hc := Global.LogarithmicBlowupBound.Construction.globalBlowup_preserves_logarithmic_order_bound I J hI E A' (B.reindex e) C m hp hbound
  have hC := (B'.reindex (Function.Embedding.optionMap e)).logarithmicIdeal_eq_of_boundary_eq C he
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m) m
  exact hC.trans hc

end

end OAI.AlgebraicGeometry.Resolution.Blowups
