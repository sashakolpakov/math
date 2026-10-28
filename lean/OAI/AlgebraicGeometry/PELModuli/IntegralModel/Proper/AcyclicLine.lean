import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ChowAcyclicSheaves
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ChowGenericLine

/-! # Acyclic Line -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.AcyclicLine

noncomputable section

/-! A proper integral scheme over a noetherian affine base has a
constructed coherent sheaf which is generically a line bundle and has
finite cohomology. In fact its positive cohomology groups vanish. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem baseCohomologyFinite_of_sections_and_vanishing
    {X S : Scheme.{0}} (f : X ⟶ S) (M : X.Modules)
    (hΓ : Module.Finite Γ(S, ⊤) ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor f).obj M))
    (hH : ∀ q : ℕ, 0 < q → Subsingleton (SheafCohomology.AffineH.Projective.H M q)) :
    CohomologyExactFiniteness.BaseCohomologyFinite f M := by
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
    {R : Type} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of R)) [IsProper f] :
    ∃ G : X.Modules, G.IsQuasicoherent ∧ G.IsFiniteType ∧ CohomologyExactFiniteness.BaseCohomologyFinite f G ∧
      (∀ q : ℕ, 0 < q → Subsingleton (SheafCohomology.AffineH.Projective.H G q)) ∧
      ∃ U : X.Opens, Nonempty U ∧ IsAffineOpen U ∧
        ∃ L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle U.toScheme, Nonempty (G.restrict U.ι ≅ L.sheaf) := by
  let D := Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.build f
  obtain ⟨b, hb⟩ := ChowAcyclicSheaves.chowHighPowerPushforward_eventually_acyclic D
  let L := (ChowAmpleLine.chowAmpleLine D).tensorPower (b + 1)
  let G := (Scheme.Modules.pushforward D.projection).obj L.sheaf
  have hG : ∀ q : ℕ, 0 < q → Subsingleton (SheafCohomology.AffineH.Projective.H G q) := hb (b + 1) (Nat.le_succ b)
  refine ⟨G, ChowLinePushforward.chowLinePushforward_quasicoherent D L, ChowLinePushforward.chowLinePushforward_finiteType D L,
    baseCohomologyFinite_of_sections_and_vanishing f G
      (ChowAcyclicSheaves.chowLinePushforward_globalSections_finite D L) hG, hG, ?_⟩
  exact ⟨D.cover.common, D.cover.common_nonempty, D.cover.common_affine,
    ChowGenericLine.chowPushforwardLineOnCommon D L, ⟨ChowGenericLine.chowPushforward_restrictCommon_iso D L⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.AcyclicLine
