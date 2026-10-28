import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Opens

/-! # Covers -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Covers.CrystallinePrincipalCovers

noncomputable section

/-!
# Principal-open covers in the actual crystalline topology

A family of ambient coefficients generating the unit ideal gives a cover
by the constructed principal-open crystalline objects. Its covering sieve
belongs to the existing native crystalline topology.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q : Site.Object p k X)
  (ι : Type u) (s : ι → Q.thickening.ring)

def presieve : Presieve Q :=
  Presieve.ofArrows (fun i => Opens.CrystallinePrincipalOpens.object p k X Q (s i))
    (fun i => Opens.CrystallinePrincipalOpens.projection p k X Q (s i))

theorem exists_basicOpen (hs : Ideal.span (Set.range s) = ⊤) (x : PrimeSpectrum Q.thickening.ring) :
    ∃ i, s i ∉ x.asIdeal := by
  classical
  by_contra h
  push Not at h
  have hI : Ideal.span (Set.range s) ≤ x.asIdeal := Ideal.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    exact h i)
  rw [hs] at hI
  exact x.isPrime.ne_top (top_le_iff.mp hI)

/-- Actual principal-open crystalline objects cover in the native topology. -/
theorem covering_mem (hs : Ideal.span (Set.range s) = ⊤) :
    Sieve.generate (presieve p k X Q ι s) ∈ Site.topology p k X Q := by
  apply Site.covering_mem
  rw [presieve, Presieve.map_ofArrows, Scheme.ofArrows_mem_precoverage_iff]
  constructor
  · intro x
    obtain ⟨i, hi⟩ := exists_basicOpen p k X Q ι s hs x
    refine ⟨i, ?_⟩
    change x ∈ Set.range (PrimeSpectrum.comap
      (algebraMap Q.thickening.ring (Localization.Away (s i))))
    have hxi : (x : PrimeSpectrum Q.thickening.ring) ∈
        (PrimeSpectrum.basicOpen (s i) : Set (PrimeSpectrum Q.thickening.ring)) := hi
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away (s i)) (s i)).symm ▸ hxi
  · intro i
    exact Opens.CrystallinePrincipalOpens.ambient_openImmersion p k X Q (s i)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Covers.CrystallinePrincipalCovers
