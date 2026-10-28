import OAI.AlgebraicGeometry.Resolution.Blowups.ReducedCenterPointedDescent
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterComponents

/-! # Permissible Center Tangent Descent -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.PermissibleCenterTangentDescent.Construction

noncomputable section

/-! Smooth permissible center ideals are uniquely determined by pointed tangent comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem permissible_centers_eq_of_pointed_tangent_comparisons
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J I K : X.IdealSheafData) (n : ℕ)
    [Smooth (I.subschemeι ≫ f)] [Smooth (K.subschemeι ≫ f)]
    (hI : J ≤ I ^ (n + 1)) (hK : J ≤ K ^ (n + 1))
    (h : ∀ x : X, x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support →
      ∃ (V : Scheme) (a b : V ⟶ X) (y : V), a y = x ∧
        IdealSheaf.CongruentMaps.Construction.IdealSheafCongruent a b (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n) ∧ I.comap a = K.comap b) : I = K := by
  let : IsReduced I.subscheme := Blowups.Smooth.CenterComponents.Construction.smooth_complex_scheme_isReduced (I.subschemeι ≫ f)
  let : IsReduced K.subscheme := Blowups.Smooth.CenterComponents.Construction.smooth_complex_scheme_isReduced (K.subschemeι ≫ f)
  exact ReducedCenterPointedDescent.Construction.idealSheaf_eq_of_reduced_tangent_comparisons (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n) I K
    (Global.OrderLocusPreservation.Construction.global_tangent_le_permissible_center f J I n hI) (Global.OrderLocusPreservation.Construction.global_tangent_le_permissible_center f J K n hK) h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.PermissibleCenterTangentDescent.Construction
