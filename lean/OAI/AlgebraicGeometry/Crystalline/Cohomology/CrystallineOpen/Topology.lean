import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Principal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Topology
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # Topology -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Topology.CrystallineOpenTopology

noncomputable section

/-!
# Continuity and cocontinuity of native crystalline open restriction

The inclusion is downward closed and preserves the actual principal PD
opens. The principal-open characterization proves both covering laws for
the original generated crystalline topologies.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u w

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {X Y : Over (Spec (CommRingCat.of k))} (j : X ⟶ Y) [IsOpenImmersion j.left]

local notation "Inclusion" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Embedding.CrystallineOpenEmbedding.functor p k j

instance full : (Inclusion).Full := (Embedding.CrystallineOpenEmbedding.fullyFaithful p k j).full

instance faithful : (Inclusion).Faithful := (Embedding.CrystallineOpenEmbedding.fullyFaithful p k j).faithful

def downwardsClosed {P : Site.Object p k X} {Q : Site.Object p k Y}
    (f : Q ⟶ (Inclusion).obj P) : Σ P', (Inclusion).obj P' ≅ Q :=
  ⟨OpenLift.CrystallineOpenLift.object p k j Q (OpenLift.CrystallineOpenLift.range_of_map p k j Q P f),
    OpenLift.CrystallineOpenLift.iso p k j Q (OpenLift.CrystallineOpenLift.range_of_map p k j Q P f)⟩

theorem compatiblePreserving :
    CompatiblePreserving.{w} (Site.topology p k Y) Inclusion :=
  compatiblePreservingOfDownwardsClosed (Site.topology p k Y) Inclusion (downwardsClosed p k j)

theorem coverPreserving :
    CoverPreserving (Site.topology p k X) (Site.topology p k Y) Inclusion where
  cover_preserve {Q S} hS := by
    apply (CrystallinePrincipal.Topology.CrystallinePrincipalTopology.covering_iff p k Y _).mpr
    intro x
    obtain ⟨s, hs, hmem⟩ := (CrystallinePrincipal.Topology.CrystallinePrincipalTopology.covering_iff p k X S).mp hS x
    apply CrystallinePrincipal.Topology.CrystallinePrincipalTopology.of_open p k Y (S.functorPushforward Inclusion)
      ((Inclusion).map (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s))
      (Sieve.image_mem_functorPushforward Inclusion S hmem) x
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away s) s).symm ▸ hs

instance continuous :
    (Inclusion).IsContinuous (Site.topology p k X) (Site.topology p k Y) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreserving p k j) (coverPreserving p k j)

instance cocontinuous :
    (Inclusion).IsCocontinuous (Site.topology p k X) (Site.topology p k Y) where
  cover_lift {Q S} hS := by
    apply (CrystallinePrincipal.Topology.CrystallinePrincipalTopology.covering_iff p k X _).mpr
    intro x
    obtain ⟨s, hs, hmem⟩ := (CrystallinePrincipal.Topology.CrystallinePrincipalTopology.covering_iff p k Y S).mp hS x
    refine ⟨s, hs, ?_⟩
    change S ((Inclusion).map (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s))
    exact (Principal.CrystallineOpenPrincipal.projection p k j Q s) ▸
      S.downward_closed hmem (Principal.CrystallineOpenPrincipal.map p k j Q s)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Topology.CrystallineOpenTopology
