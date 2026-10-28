import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.Nonvanishing

/-! # Module Restriction Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleRestrictionIs.Construction.ModuleRestriction

noncomputable section

/-! Detecting a module-sheaf map on sections inside an open where it is invertible. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem isIso_app {X : Scheme.{u}} {M N : X.Modules} (a : M ⟶ N)
    (U V : X.Opens) (hV : V ≤ U) [IsIso ((Scheme.Modules.pullback U.ι).map a)] :
    IsIso (a.app V) := by
  have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map a) :=
    (AbelianModuli.HilbertConstruction.Power.Nonvanishing.isIso_restrict_map_iff U.ι a).mpr inferInstance
  have he : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hV]
  rw [← he]
  exact inferInstanceAs (IsIso (((Scheme.Modules.restrictFunctor U.ι).map a).app (U.ι ⁻¹ᵁ V)))

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleRestrictionIs.Construction.ModuleRestriction
