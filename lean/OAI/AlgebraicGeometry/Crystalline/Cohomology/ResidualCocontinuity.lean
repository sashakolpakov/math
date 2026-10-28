import OAI.AlgebraicGeometry.Crystalline.Cohomology.ResidualCover
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.ThickeningTopology
import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # Residual Cocontinuity -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ResidualCocontinuity.CrystallineResidualCocontinuity

noncomputable section

/-!
# Lifting Zariski covers to native crystalline covers

A residual principal-open function lifts along the actual surjective
reduction. Its ambient principal open is a native crystalline object.
These objects refine every Zariski covering sieve of the residual open.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

theorem refinement (Q : Site.Object p k X) (U : X.left.Opens)
    (z : PrimeSpectrum Q.residueRing) (hz : Q.immersion z ∈ U) :
    ∃ s : Q.thickening.ring,
      PrimeSpectrum.comap Q.thickening.reduction z ∈ PrimeSpectrum.basicOpen s ∧
      (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q s).immersion.opensRange ≤ U := by
  obtain ⟨_, ⟨r, rfl⟩, hzr, hr⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hz
      (U.isOpen.preimage Q.immersion.continuous)
  obtain ⟨s, hs⟩ := Q.thickening.reduction_surjective r
  have hr' : (PrimeSpectrum.basicOpen (Q.thickening.reduction s) : Set (PrimeSpectrum Q.residueRing)) ⊆
      Q.immersion ⁻¹' (U : Set X.left) := hs.symm ▸ hr
  refine ⟨s, ?_, ?_⟩
  · change z ∈ PrimeSpectrum.basicOpen (Q.thickening.reduction s)
    rw [hs]
    exact hzr
  · rintro y ⟨w, rfl⟩
    change PrimeSpectrum (Localization.Away (Q.thickening.reduction s)) at w
    change Q.immersion (PrimeSpectrum.comap (algebraMap Q.residueRing
      (Localization.Away (Q.thickening.reduction s))) w) ∈ U
    exact hr' ((PrimeSpectrum.localization_away_comap_range
      (Localization.Away (Q.thickening.reduction s)) (Q.thickening.reduction s)).subset ⟨w, rfl⟩)

instance cocontinuous : (ResidualCover.CrystallineResidualCover.functor p k X).IsCocontinuous
    (Site.topology p k X) (Opens.grothendieckTopology X.left) where
  cover_lift {Q S} hS := by
    apply (CrystallinePrincipal.Topology.CrystallinePrincipalTopology.covering_iff p k X _).mpr
    intro x
    obtain ⟨z, rfl⟩ :=
      (PD.ThickeningTopology.PDThickeningTopology.reduction_isHomeomorph p k Q.residueRing Q.thickening).surjective x
    obtain ⟨U, f, hf, hz⟩ := (Opens.mem_grothendieckTopology X.left).mp hS
      (Q.immersion z) ⟨z, rfl⟩
    obtain ⟨s, hs, hU⟩ := refinement p k X Q U z hz
    refine ⟨s, hs, ?_⟩
    change S ((ResidualCover.CrystallineResidualCover.functor p k X).map
      (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s))
    have h := S.downward_closed hf (homOfLE hU)
    exact (Subsingleton.elim (homOfLE hU ≫ f)
      ((ResidualCover.CrystallineResidualCover.functor p k X).map
        (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s))) ▸ h

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ResidualCocontinuity.CrystallineResidualCocontinuity
