import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.CoverRefinement

/-! # Topology -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Topology.CrystallinePrincipalTopology

noncomputable section

/-!
# The principal-open basis of the actual crystalline topology

A native sieve covers exactly when every ambient point lies in an actual
principal open whose projection belongs to the sieve. Pullback stability
uses the native principal pullbacks; transitivity uses actual PD refinements
of composite open immersions. This identifies the existing generated
crystalline topology, rather than replacing it with a different topology.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

local notation "A" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.ambient p k X

def LocallyPrincipal {Q : Site.Object p k X} (S : Sieve Q) : Prop :=
  ∀ x : PrimeSpectrum Q.thickening.ring, ∃ s : Q.thickening.ring,
    x ∈ PrimeSpectrum.basicOpen s ∧ S (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s)

theorem of_open {P Q : Site.Object p k X} (S : Sieve Q) (f : P ⟶ Q)
    [IsOpenImmersion ((A).map f)] (hf : S f) (x : PrimeSpectrum Q.thickening.ring)
    (hx : x ∈ Set.range (PrimeSpectrum.comap f.ambientMap.toRingHom)) :
    ∃ s : Q.thickening.ring, x ∈ PrimeSpectrum.basicOpen s ∧
      S (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s) := by
  obtain ⟨_, ⟨s, rfl⟩, hxs, hs⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx
      (Scheme.Hom.isOpenEmbedding ((A).map f)).isOpen_range
  refine ⟨s, hxs, ?_⟩
  exact (OpenRefinement.CrystallinePrincipalOpenRefinement.lift_factor p k X f s hs) ▸
    S.downward_closed hf (OpenRefinement.CrystallinePrincipalOpenRefinement.lift p k X f s hs)

def topology : GrothendieckTopology (Site.Object p k X) where
  sieves _ := {S | LocallyPrincipal p k X S}
  top_mem' Q := fun x => ⟨1, by simp, trivial⟩
  pullback_stable' := by
    intro Q P S f hS x
    obtain ⟨s, hs, hSs⟩ := hS (PrimeSpectrum.comap f.ambientMap.toRingHom x)
    refine ⟨f.ambientMap s, hs, ?_⟩
    change S (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X P (f.ambientMap s) ≫ f)
    exact (Pullbacks.CrystallinePrincipalPullbacks.condition p k X f s) ▸
      S.downward_closed hSs (Pullbacks.CrystallinePrincipalPullbacks.map p k X f s)
  transitive' := by
    intro Q S hS R hR x
    obtain ⟨s, hs, hSs⟩ := hS x
    have hx : x ∈ Set.range (PrimeSpectrum.comap (algebraMap Q.thickening.ring (Localization.Away s))) :=
      (PrimeSpectrum.localization_away_comap_range (Localization.Away s) s).symm ▸ hs
    obtain ⟨y, hy⟩ := hx
    obtain ⟨t, ht, hRt⟩ := hR hSs y
    let P := CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q s
    have hy' : y ∈ Set.range (PrimeSpectrum.comap (algebraMap P.thickening.ring (Localization.Away t))) :=
      (PrimeSpectrum.localization_away_comap_range (Localization.Away t) t).symm ▸ ht
    obtain ⟨z, hz⟩ := hy'
    let f := CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X P t ≫ CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s
    have : IsOpenImmersion ((A).map f) := by
      change IsOpenImmersion ((A).map (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X P t ≫
        CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s))
      rw [(A).map_comp]
      infer_instance
    apply of_open p k X R f hRt x
    refine ⟨z, ?_⟩
    change PrimeSpectrum.comap (algebraMap Q.thickening.ring (Localization.Away s))
      (PrimeSpectrum.comap (algebraMap P.thickening.ring (Localization.Away t)) z) = x
    exact (congrArg (PrimeSpectrum.comap (algebraMap Q.thickening.ring (Localization.Away s))) hz).trans hy

theorem native_le : Site.topology p k X ≤ topology p k X := by
  apply Precoverage.toGrothendieck_le_iff_le_toPrecoverage.mpr
  intro Q R hR
  exact CoverRefinement.CrystallinePrincipalCoverRefinement.exists_at p k X Q R hR

theorem le_native : topology p k X ≤ Site.topology p k X := by
  intro Q S hS
  choose s hs hmem using hS
  have hspan : Ideal.span (Set.range s) = ⊤ := by
    apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
    apply top_le_iff.mp
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hs x⟩
  apply (Site.topology p k X).superset_covering _
    (Covers.CrystallinePrincipalCovers.covering_mem p k X Q (PrimeSpectrum Q.thickening.ring) s hspan)
  apply (Sieve.generate_le_iff _ _).mpr
  intro P f hf
  obtain ⟨i⟩ := hf
  exact hmem i

theorem eq_native : topology p k X = Site.topology p k X :=
  le_antisymm (le_native p k X) (native_le p k X)

theorem covering_iff {Q : Site.Object p k X} (S : Sieve Q) :
    S ∈ Site.topology p k X Q ↔ LocallyPrincipal p k X S := by
  rw [← eq_native]
  rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Topology.CrystallinePrincipalTopology
