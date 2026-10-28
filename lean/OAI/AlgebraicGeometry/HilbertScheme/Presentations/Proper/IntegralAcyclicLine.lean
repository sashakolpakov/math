import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.ChowAcyclicSheaves
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ChowGenericLine

/-! # Integral Acyclic Line -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.IntegralAcyclicLine

noncomputable section

/-! A proper integral scheme over a noetherian affine base has a
constructed coherent sheaf which is generically a line bundle and has
finite cohomology. In fact its positive cohomology groups vanish. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Cohomology

universe u

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.ChowGenericLine

theorem baseCohomologyFinite_of_sections_and_vanishing
    {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    (hΓ : Module.Finite Γ(S, ⊤) ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor f).obj M))
    (hH : ∀ q : ℕ, 0 < q → Subsingleton (SheafCohomology.AffineH.Projective.H M q)) :
    PELModuli.IntegralModel.CohomologyExactFiniteness.BaseCohomologyFinite f M := by
  intro n
  cases n with
  | zero =>
      let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M 0
      let := SheafCohomology.Projective.BaseZeroSections.baseGlobalSectionsModule f M
      have : Module.Finite Γ(S, ⊤) Γ(M, ⊤) := hΓ
      exact Module.Finite.equiv (SheafCohomology.Projective.BaseZeroSections.baseHZeroLinearEquivGlobalSections f M).symm
  | succ n =>
      let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M (n + 1)
      have : Subsingleton (SheafCohomology.AffineH.Projective.H M (n + 1)) := hH (n + 1) (Nat.zero_lt_succ n)
      infer_instance

theorem properIntegral_exists_coherent_generic_line_finite_cohomology
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of R)) [IsProper f] :
    ∃ G : X.Modules, G.IsQuasicoherent ∧ G.IsFiniteType ∧ PELModuli.IntegralModel.CohomologyExactFiniteness.BaseCohomologyFinite f G ∧
      (∀ q : ℕ, 0 < q → Subsingleton (SheafCohomology.AffineH.Projective.H G q)) ∧
      ∃ U : X.Opens, Nonempty U ∧ IsAffineOpen U ∧
        ∃ L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle U.toScheme, Nonempty (G.restrict U.ι ≅ L.sheaf) := by
  let D := Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.build f
  obtain ⟨b, hb⟩ := ChowAcyclicSheaves.Cohomology.chowHighPowerPushforward_eventually_acyclic D
  let L := (PELModuli.IntegralModel.ChowAmpleLine.chowAmpleLine D).tensorPower (b + 1)
  let G := (Scheme.Modules.pushforward D.projection).obj L.sheaf
  have hG : ∀ q : ℕ, 0 < q → Subsingleton (SheafCohomology.AffineH.Projective.H G q) := hb (b + 1) (Nat.le_succ b)
  refine ⟨G, PELModuli.IntegralModel.ChowLinePushforward.chowLinePushforward_quasicoherent D L, PELModuli.IntegralModel.ChowLinePushforward.chowLinePushforward_finiteType D L,
    baseCohomologyFinite_of_sections_and_vanishing f G
      (ChowAcyclicSheaves.Cohomology.chowLinePushforward_globalSections_finite D L) hG, hG, ?_⟩
  exact ⟨D.cover.common, D.cover.common_nonempty, D.cover.common_affine,
    PELModuli.IntegralModel.ChowGenericLine.chowPushforwardLineOnCommon D L, ⟨PELModuli.IntegralModel.ChowGenericLine.chowPushforward_restrictCommon_iso D L⟩⟩

end Cohomology

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.IntegralAcyclicLine
