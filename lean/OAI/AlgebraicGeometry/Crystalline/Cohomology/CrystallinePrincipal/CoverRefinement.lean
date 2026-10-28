import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.OpenRefinement
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Covers

/-! # Cover Refinement -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.CoverRefinement.CrystallinePrincipalCoverRefinement

noncomputable section

/-!
# Principal refinements of every native crystalline covering family

The Zariski basis of the actual ambient affine scheme, together with
native PD factorizations, refines every generating crystalline cover
by actual principal-open objects whose coefficients generate the unit ideal.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q : Site.Object p k X)

local notation "A" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.ambient p k X

theorem exists_at (R : Presieve Q)
    (hR : R.map A ∈ Scheme.precoverage IsOpenImmersion ((A).obj Q))
    (x : PrimeSpectrum Q.thickening.ring) :
    ∃ s : Q.thickening.ring, x ∈ PrimeSpectrum.basicOpen s ∧
      Sieve.generate R (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s) := by
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  rw [Presieve.map_ofArrows, Scheme.ofArrows_mem_precoverage_iff] at hR
  obtain ⟨i, hi⟩ := hR.1 x
  have : IsOpenImmersion ((A).map (f i)) := hR.2 i
  obtain ⟨_, ⟨s, rfl⟩, hxs, hs⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hi
      (Scheme.Hom.isOpenEmbedding ((A).map (f i))).isOpen_range
  refine ⟨s, hxs, ?_⟩
  have hg := (Sieve.generate (Presieve.ofArrows Y f)).downward_closed
    (Sieve.le_generate _ _ _ (Presieve.ofArrows.mk i))
    (OpenRefinement.CrystallinePrincipalOpenRefinement.lift p k X (f i) s hs)
  exact (OpenRefinement.CrystallinePrincipalOpenRefinement.lift_factor p k X (f i) s hs) ▸ hg

theorem exists_refinement (R : Presieve Q)
    (hR : R.map A ∈ Scheme.precoverage IsOpenImmersion ((A).obj Q)) :
    ∃ s : PrimeSpectrum Q.thickening.ring → Q.thickening.ring,
      Ideal.span (Set.range s) = ⊤ ∧
      Covers.CrystallinePrincipalCovers.presieve p k X Q (PrimeSpectrum Q.thickening.ring) s ≤ Sieve.generate R := by
  choose s hs hsmem using exists_at p k X Q R hR
  refine ⟨s, ?_, ?_⟩
  · apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
    apply top_le_iff.mp
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hs x⟩
  · intro P f hf
    obtain ⟨i⟩ := hf
    exact hsmem i

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.CoverRefinement.CrystallinePrincipalCoverRefinement
