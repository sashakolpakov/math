import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow.AmplePushforwardAcyclicity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.FinitenessProperty
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow.AmplePowerSectionsFinite
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsPushforward

/-! # Ample Pushforward Cohomology Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow

noncomputable section

/-! A sufficiently high ample power on the Chow modification has a direct image with finite genuine cohomology in every degree. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem Modification.ChowModification.Model.amplePowerPushforward_sections_finite
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} (D : Modification.ChowModification.Model f) (n : ℕ) :
    Module.Finite R ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap f)).obj
      ((Scheme.Modules.pushforward D.projection).obj (D.ampleLineBundle.tensorPower n).sheaf)) := by
  have h : Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (D.projection ≫ f)).obj
    (D.ampleLineBundle.tensorPower n).sheaf) := D.amplePowerSections_finite n
  exact @Module.Finite.equiv R _ _ _ _ _ _ _ h
    (Coefficient.GlobalSectionsPushforward.schemeGlobalSectionsPushforwardIso D.projection f (D.ampleLineBundle.tensorPower n).sheaf).symm

theorem Modification.ChowModification.Model.amplePowerPushforward_eventually_finite_cohomology
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} [IsProper f] (D : Modification.ChowModification.Model f) :
    ∃ B : ℕ, ∀ n : ℕ, B ≤ n →
      CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite (Coefficient.ModulePresheaf.schemeCoefficientMap f)
        ((Scheme.Modules.pushforward D.projection).obj (D.ampleLineBundle.tensorPower n).sheaf) := by
  obtain ⟨B, hB⟩ := D.amplePowerPushforward_eventually_acyclic
  exact ⟨B, fun n hn ↦ CoefficientCohomology.FinitenessProperty.ZariskiCohomology.coefficientCohomologyFinite_of_sections_and_vanishing
    _ _ (D.amplePowerPushforward_sections_finite n) (hB n hn)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow
