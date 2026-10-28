import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Topology
import Mathlib.CategoryTheory.Sites.CoverPreserving

/-! # Residual Cover -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ResidualCover.CrystallineResidualCover

noncomputable section

/-!
# Crystalline covers cover the actual residual open subscheme

The residual-open functor remembers the original immersion into the
special fibre. Every crystalline covering sieve covers this open in
the ordinary Zariski topology, as witnessed by actual principal objects.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

def functor : Site.Object p k X ⥤ X.left.Opens where
  obj Q := Q.immersion.opensRange
  map {P Q} f := homOfLE (by
    rintro x ⟨z, rfl⟩
    refine ⟨(Spec.map (CommRingCat.ofHom f.reducedMap.toRingHom)) z, ?_⟩
    exact congrArg (fun g : Spec P.residueRing ⟶ X.left => g z) f.over_X)

theorem exists_at {Q : Site.Object p k X} (S : Sieve Q)
    (hS : S ∈ Site.topology p k X Q) (x : X.left) (hx : x ∈ Q.immersion.opensRange) :
    ∃ (P : Site.Object p k X) (f : P ⟶ Q), S f ∧ x ∈ P.immersion.opensRange := by
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨s, hs, hmem⟩ := (CrystallinePrincipal.Topology.CrystallinePrincipalTopology.covering_iff p k X S).mp hS
    (PrimeSpectrum.comap Q.thickening.reduction z)
  have hz : z ∈ PrimeSpectrum.basicOpen (Q.thickening.reduction s) := hs
  have hl : z ∈ Set.range (PrimeSpectrum.comap (algebraMap Q.residueRing
      (Localization.Away (Q.thickening.reduction s)))) :=
    (PrimeSpectrum.localization_away_comap_range
      (Localization.Away (Q.thickening.reduction s)) (Q.thickening.reduction s)).symm ▸ hz
  obtain ⟨w, hw⟩ := hl
  refine ⟨CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q s,
    CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s, hmem, w, ?_⟩
  exact congrArg Q.immersion hw

theorem coverPreserving : CoverPreserving (Site.topology p k X)
    (Opens.grothendieckTopology X.left) (functor p k X) where
  cover_preserve {Q S} hS := by
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    obtain ⟨P, f, hf, hxP⟩ := exists_at p k X S hS x hx
    exact ⟨(functor p k X).obj P, (functor p k X).map f,
      Sieve.image_mem_functorPushforward (functor p k X) S hf, hxP⟩

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ResidualCover.CrystallineResidualCover
