import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ChowLinePushforward
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.FiniteCoverAmpleVanishing
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AcyclicPushforwardComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CohomologyExactFiniteness

/-! # Chow Acyclic Sheaves -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.ChowAcyclicSheaves

noncomputable section

/-! Coherent sheaves with finite cohomology on an arbitrary proper
integral scheme, constructed as high-power direct images from Chow's
projective modification. No normality hypothesis is required. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Cohomology

universe u

theorem chowHighPowerPushforward_eventually_acyclic
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} [IsProper f]
    (D : Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.Model f) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      ∀ q : ℕ, 0 < q → Subsingleton (SheafCohomology.AffineH.Projective.H
        ((Scheme.Modules.pushforward D.projection).obj ((PELModuli.IntegralModel.ChowAmpleLine.chowAmpleLine D).tensorPower n).sheaf) q) := by
  have : IsProper D.projection := D.proper
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherianRing Γ(Spec (.of R), ⊤) := isNoetherianRing_of_ringEquiv R
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  let U (i : ULift.{u} (Fin D.cover.n)) : X.Opens := D.cover.opens i.down
  have hUa (i : ULift.{u} (Fin D.cover.n)) : IsAffineOpen (U i) := D.cover.affine i.down
  have hU : IsOpenCover U := by
    apply IsOpenCover.mk
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := D.cover.covers x
    exact Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  obtain ⟨a, ha⟩ := FiniteCoverAmpleVanishing.Cohomology.finiteCover_relativelyAmple_eventually_acyclic D.projection
    (PELModuli.IntegralModel.ChowAmpleLine.chowAmpleLine D) (PELModuli.IntegralModel.ChowAmpleLine.chowAmpleLine_relative_to_target D) U hUa
  obtain ⟨b, hb⟩ := AmpleLineVanishing.Cohomology.ample_lineBundle_eventually_vanishing (D.projection ≫ f)
    (PELModuli.IntegralModel.ChowAmpleLine.chowAmpleLine D) (PELModuli.IntegralModel.ChowAmpleLine.chowAmpleLine_isAmple D)
  refine ⟨max a b, fun n hn q hq => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  let L := (PELModuli.IntegralModel.ChowAmpleLine.chowAmpleLine D).tensorPower n
  have : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  have : Subsingleton (SheafCohomology.AffineH.Projective.H L.sheaf (k + 1)) := hb n ((le_max_right a b).trans hn) (k + 1) hq
  exact (PELModuli.IntegralModel.AcyclicPushforwardComparison.pushforwardCohomologyAcyclicCoverEquiv D.projection L.sheaf
    U hU hUa (ha n ((le_max_left a b).trans hn)) k).injective.subsingleton

theorem chowLinePushforward_globalSections_finite
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} [IsProper f]
    (D : Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.Model f) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle D.scheme) :
    Module.Finite Γ(Spec (.of R), ⊤)
      ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor f).obj ((Scheme.Modules.pushforward D.projection).obj L.sheaf)) := by
  have : IsNoetherianRing Γ(Spec (.of R), ⊤) := isNoetherianRing_of_ringEquiv R
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  have : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  have : L.sheaf.IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation L
  have : L.sheaf.IsFiniteType := by
    obtain ⟨p, hp⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.sheaf
    refine { exists_localGeneratorsData := ⟨p.localGeneratorsData, ?_⟩ }
    constructor
    intro i
    exact (hp.isFinite_presentation i).isFiniteType_generators
  have : Module.Finite Γ(Spec (.of R), ⊤)
      ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (D.projection ≫ f)).obj L.sheaf) :=
    PELModuli.IntegralModel.Projective.SectionFiniteness.projectivePresentation_globalSections_finite (Over.mk (D.projection ≫ f))
      D.projectivePresentation L.sheaf
  exact Module.Finite.equiv
    (ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardSections.Construction.baseGlobalSectionsPushforwardEquiv D.projection f L.sheaf).symm

end Cohomology

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.ChowAcyclicSheaves
