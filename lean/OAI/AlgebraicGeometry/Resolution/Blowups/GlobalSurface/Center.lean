import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalSurface.TangentGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalSurface.Tangent
import OAI.AlgebraicGeometry.Resolution.Blowups.MinimalCoefficientBound

/-! # Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The actual native surface coefficient center at a fixed common differential level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (ℓ : ℕ)
    (hb : ∀ i, (A.choice i).HasBound (ℓ + 1))
    (hdim : ∀ i, ringKrullDim (A.rings i) ≤ 2) (hlevel : (n + 1).factorial ≤ ℓ + 1)

def GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceCenter : X.IdealSheafData :=
  (GlobalSurface.TangentGluing.Construction.existsUnique_global_surface_tangent_center ℂ f A.rings A.map A.ground A.cover J A.ideals A.ideal_eq
    n ℓ (fun i => (A.choice i).toSurfaceTangentChoice ℓ (hb i)) hdim hlevel).choose

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceCenter_restrict (i : A.indices) :
    (A.surfaceCenter ℓ hb hdim hlevel).comap (A.map i) =
      Affine.QuotientKernel.Construction.affineQuotientKernel ((A.choice i).toSurfaceTangentChoice ℓ (hb i)).center :=
  (GlobalSurface.TangentGluing.Construction.existsUnique_global_surface_tangent_center ℂ f A.rings A.map A.ground A.cover J A.ideals A.ideal_eq
    n ℓ (fun i => (A.choice i).toSurfaceTangentChoice ℓ (hb i)) hdim hlevel).choose_spec.1 i

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceCenter_isPermissible : J ≤ (A.surfaceCenter ℓ hb hdim hlevel) ^ (n + 1) :=
  A.surfaceCenter_permissible ℓ _ _ (A.surfaceCenter_restrict ℓ hb hdim hlevel) hdim hlevel

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceCenter_isSmooth : Smooth ((A.surfaceCenter ℓ hb hdim hlevel).subschemeι ≫ f) :=
  A.surfaceCenter_smooth ℓ _ _ (A.surfaceCenter_restrict ℓ hb hdim hlevel) hdim hlevel

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceCenter_nonzero [Nonempty X] : A.surfaceCenter ℓ hb hdim hlevel ≠ ⊥ :=
  A.surfaceCenter_ne_bot ℓ _ _ (A.surfaceCenter_restrict ℓ hb hdim hlevel)

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceCenter_eq_top_iff : A.surfaceCenter ℓ hb hdim hlevel = ⊤ ↔
    ∀ i, (A.choice i).HasBound ℓ := by
  constructor
  · intro ht i
    apply ((A.choice i).tangentChoice_center_eq_top_iff (hb i)).mp
    apply (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp
    have he := A.surfaceCenter_restrict ℓ hb hdim hlevel i
    rw [ht, Scheme.IdealSheafData.comap_top] at he
    exact he.symm.trans DifferentialUnitGluing.Construction.affineQuotientKernel_top.symm
  · intro h
    apply Finite.OpenIdealSheafUniqueness.Construction.idealSheaf_eq_of_open_affine_restrictions (fun i => Spec (A.rings i)) A.map A.cover
    intro i
    rw [A.surfaceCenter_restrict ℓ hb hdim hlevel i,
      ((A.choice i).tangentChoice_center_eq_top_iff (hb i)).mpr (h i),
      DifferentialUnitGluing.Construction.affineQuotientKernel_top, Scheme.IdealSheafData.comap_top]

end

end OAI.AlgebraicGeometry.Resolution.Blowups
