import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow.AmplePushforwardCohomologyFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow.LineImageFiniteType

/-! # Integral Good Cohomology Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IntegralGoodCohomologySheaf

noncomputable section

/-! Every proper integral scheme over a Noetherian affine spectrum has an actual coherent sheaf, generically a line bundle on a specified nonempty affine open, with finite genuine cohomology and no positive cohomology. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem properIntegral_exists_coherent_generic_line_finite_cohomology
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of R)) [IsProper f] :
    ∃ G : X.Modules, G.IsQuasicoherent ∧ G.IsFiniteType ∧
      CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite (Coefficient.ModulePresheaf.schemeCoefficientMap f) G ∧
      (∀ q : ℕ, Subsingleton (Zariski.Cohomology.ZariskiCohomology.H G (q + 1))) ∧
      ∃ U : X.Opens, Nonempty U ∧ IsAffineOpen U ∧
        ∃ L : Line.Bundles.LineBundle U.toScheme, Nonempty (G.restrict U.ι ≅ L.sheaf) := by
  let D := Chow.Modification.ChowModification.build f
  obtain ⟨B, hB⟩ := D.amplePowerPushforward_eventually_acyclic
  let L := D.ampleLineBundle.tensorPower B
  let G := (Scheme.Modules.pushforward D.projection).obj L.sheaf
  have hG : ∀ q : ℕ, Subsingleton (Zariski.Cohomology.ZariskiCohomology.H G (q + 1)) := hB B le_rfl
  refine ⟨G, D.lineBundlePushforward_quasicoherent L, D.lineBundlePushforward_finiteType L,
    CoefficientCohomology.FinitenessProperty.ZariskiCohomology.coefficientCohomologyFinite_of_sections_and_vanishing _ G
      (D.amplePowerPushforward_sections_finite B) hG, hG, ?_⟩
  exact ⟨D.cover.common, D.cover.common_nonempty, D.cover.common_affine,
    D.pushforwardLineOnCommon L, ⟨D.pushforward_restrictCommon_iso L⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IntegralGoodCohomologySheaf
