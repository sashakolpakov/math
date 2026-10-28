import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Sieves
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Adjunction
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Covers
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.InducedTopology

/-! # Topology -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Topology.FramedCrystallineTopology

noncomputable section

/-!
# The topology of the crystalline site with lifted frame coordinates

A sieve covers precisely when its underlying native sieve covers. The
proved sieve identities establish the topology axioms. The topology is
also identified with the standard induced topology along the forgetful
functor. Both the forgetful functor and its native frame right adjoint
are continuous, giving an adjunction on sheaves.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Sieves.FramedCrystallineSieves

universe u v w

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.forget p k B σ a
local notation "G" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.frame p k B σ a

def topology (J : GrothendieckTopology (Site.Object p k X)) :
    GrothendieckTopology (FramedCrystalline.Category.FramedCrystallineCategory.Object p k B σ a) where
  sieves Q := {S | S.functorPushforward U ∈ J Q.base}
  top_mem' Q := by
    change (⊤ : Sieve Q).functorPushforward U ∈ J Q.base
    rw [Sieve.functorPushforward_top]
    exact J.top_mem _
  pullback_stable' := by
    intro Q P S f hS
    change (S.pullback f).functorPushforward U ∈ J P.base
    rw [Sieves.FramedCrystallineSieves.pushforward_pullback]
    exact J.pullback_stable _ hS
  transitive' := by
    intro Q S hS R hR
    apply J.transitive hS
    rintro P f ⟨Y, g, h, hg, he⟩
    have hr := hR hg
    change (R.pullback g).functorPushforward U ∈ J Y.base at hr
    rw [Sieves.FramedCrystallineSieves.pushforward_pullback] at hr
    have hh := J.pullback_stable h hr
    rw [← Sieve.pullback_comp, ← he] at hh
    exact hh

theorem coverPreserving (J : GrothendieckTopology (Site.Object p k X)) :
    CoverPreserving (topology p k B σ a J) J U := ⟨fun h => h⟩

instance continuous (J : GrothendieckTopology (Site.Object p k X)) :
    (U).IsContinuous (topology p k B σ a J) J :=
  Functor.isContinuous_of_coverPreserving
    (CrystallineRestriction.FramedCrystallineRestriction.compatiblePreserving p k B σ a J)
    (coverPreserving p k B σ a J)

instance cocontinuous (J : GrothendieckTopology (Site.Object p k X)) :
    (U).IsCocontinuous (topology p k B σ a J) J where
  cover_lift {Q S} hS := by
    change (S.functorPullback U).functorPushforward U ∈ J Q.base
    exact (Sieves.FramedCrystallineSieves.pushforward_functorPullback p k B σ a Q S).symm ▸ hS

theorem eq_inducedTopology (J : GrothendieckTopology (Site.Object p k X)) :
    topology p k B σ a J = (U).inducedTopology J := by
  apply le_antisymm
  · exact Functor.le_inducedTopology_iff.mpr inferInstance
  · intro Q S hS
    exact (CoverPreserving.of_isContinuous U ((U).inducedTopology J) J).cover_preserve hS

instance frame_continuous (J : GrothendieckTopology (Site.Object p k X)) :
    (G).IsContinuous J (topology p k B σ a J) :=
  (CrystallineFrame.Adjunction.CrystallineFrameAdjunction.adjunction p k B σ a).isContinuous_of_isCocontinuous _ _

def sheafAdjunction (A : Type v) [Category.{w} A]
    (J : GrothendieckTopology (Site.Object p k X)) :
    (U).sheafPushforwardContinuous A (topology p k B σ a J) J ⊣
      (G).sheafPushforwardContinuous A J (topology p k B σ a J) :=
  (CrystallineFrame.Adjunction.CrystallineFrameAdjunction.adjunction p k B σ a).sheafPushforwardContinuous _ _

/-- The framed site retains the actual native crystalline covering sieves. -/
abbrev native : GrothendieckTopology (FramedCrystalline.Category.FramedCrystallineCategory.Object p k B σ a) :=
  topology p k B σ a (Site.topology p k X)

theorem principal_cover (Q : FramedCrystalline.Category.FramedCrystallineCategory.Object p k B σ a)
    (ι : Type u) (s : ι → Q.base.thickening.ring) (hs : Ideal.span (Set.range s) = ⊤) :
    Sieve.ofArrows (fun i => CrystallineRestriction.FramedCrystallineRestriction.principal p k B σ a Q (s i))
      (fun i => CrystallineRestriction.FramedCrystallineRestriction.principalProjection p k B σ a Q (s i)) ∈
        native p k B σ a Q := by
  change (Sieve.ofArrows _ _).functorPushforward U ∈ Site.topology p k X Q.base
  rw [Sieve.functorPushforward_ofArrows]
  exact CrystallinePrincipal.Covers.CrystallinePrincipalCovers.covering_mem p k X Q.base ι s hs

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Topology.FramedCrystallineTopology
