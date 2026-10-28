import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Topology
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.CoverLifting

/-! # Cocontinuity -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Cocontinuity.CrystallineFrameCocontinuity

noncomputable section

/-!
# Full cover lifting for the native crystalline frame functor

The principal-open characterization of the actual crystalline topology
extends the constructed principal-cover lifts to every covering sieve
of the framed site. No cover-lifting hypothesis is supplied.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.forget p k B σ a
local notation "G" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.frame p k B σ a
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Functor.CrystallineFrameFunctor.functor p k B σ a
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Topology.FramedCrystallineTopology.native p k B σ a

theorem framed_refinement (Q : FramedCrystalline.Category.FramedCrystallineCategory.Object p k B σ a)
    (S : Sieve Q) (hS : S ∈ K Q) :
    ∃ t : PrimeSpectrum Q.base.thickening.ring → Q.base.thickening.ring,
      Ideal.span (Set.range t) = ⊤ ∧
      ∀ i, S (FramedCrystalline.CrystallineRestriction.FramedCrystallineRestriction.principalProjection p k B σ a Q (t i)) := by
  have hlocal := (CrystallinePrincipal.Topology.CrystallinePrincipalTopology.covering_iff p k X (S.functorPushforward U)).mp hS
  choose t ht hmem using hlocal
  refine ⟨t, ?_, ?_⟩
  · apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
    apply top_le_iff.mp
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, ht x⟩
  · intro i
    have h : (S.functorPushforward U).functorPullback U
        (FramedCrystalline.CrystallineRestriction.FramedCrystallineRestriction.principalProjection p k B σ a Q (t i)) := hmem i
    exact (FramedCrystalline.Sieves.FramedCrystallineSieves.functorPullback_pushforward p k B σ a Q S) ▸ h

instance cocontinuous : (G).IsCocontinuous J K where
  cover_lift {Q S} hS := by
    obtain ⟨t, ht, hmem⟩ := framed_refinement p k B σ a ((G).obj Q) S hS
    apply (J).superset_covering _
      (CoverLifting.CrystallineFrameCoverLifting.lifted_covering_mem p k B σ a Q _ t ht)
    apply (Sieve.generate_le_iff _ _).mpr
    intro P f hf
    obtain ⟨i⟩ := hf
    change S ((G).map (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q
      (CoverLifting.CrystallineFrameCoverLifting.coefficient p k B σ a Q (t i))))
    exact (FramedCrystalline.CoverLifting.FramedCrystallineCoverLifting.factor_projection p k B σ a Q (t i)) ▸
      S.downward_closed (hmem i) (FramedCrystalline.CoverLifting.FramedCrystallineCoverLifting.factor p k B σ a Q (t i))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Cocontinuity.CrystallineFrameCocontinuity
