import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Topology
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.CoverLifting

/-! # Cover Lifting -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.CoverLifting.FramedCrystallineCoverLifting

noncomputable section

/-!
# Principal-cover lifting for the functor into the framed site

The native cover-lifting factors preserve total polynomial coordinates.
Consequently the inverse-image sieve of every unit-ideal principal cover
of a framed extension is a covering sieve in the original crystalline site.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)
  (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B))

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "G" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.frame p k B σ a
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Functor.CrystallineFrameFunctor.functor p k B σ a

def factor (t : ((F).obj Q).thickening.ring) :
    (G).obj (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q (CrystallineFrame.CoverLifting.CrystallineFrameCoverLifting.coefficient p k B σ a Q t)) ⟶
      CrystallineRestriction.FramedCrystallineRestriction.principal p k B σ a ((G).obj Q) t where
  hom := CrystallineFrame.CoverLifting.CrystallineFrameCoverLifting.factor p k B σ a Q t
  coordinate_comm i := by
    have he := congrArg (fun f => f.ambientMap (CrystallineFrame.Map.CrystallineFrameMap.coordinate a Q i))
      (CrystallineFrame.CoverLifting.CrystallineFrameCoverLifting.factor_projection p k B σ a Q t)
    exact he.trans (CrystallineFrame.Map.CrystallineFrameMap.coordinate_naturality a
      (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q (CrystallineFrame.CoverLifting.CrystallineFrameCoverLifting.coefficient p k B σ a Q t)) i)

theorem factor_projection (t : ((F).obj Q).thickening.ring) :
    factor p k B σ a Q t ≫ CrystallineRestriction.FramedCrystallineRestriction.principalProjection p k B σ a ((G).obj Q) t =
      (G).map (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q (CrystallineFrame.CoverLifting.CrystallineFrameCoverLifting.coefficient p k B σ a Q t)) :=
  Category.FramedCrystallineCategory.hom_ext p k B σ a
    (CrystallineFrame.CoverLifting.CrystallineFrameCoverLifting.factor_projection p k B σ a Q t)

theorem pullback_covering_mem (ι : Type u) (t : ι → ((F).obj Q).thickening.ring)
    (ht : Ideal.span (Set.range t) = ⊤) :
    (Sieve.ofArrows (fun i => CrystallineRestriction.FramedCrystallineRestriction.principal p k B σ a ((G).obj Q) (t i))
      (fun i => CrystallineRestriction.FramedCrystallineRestriction.principalProjection p k B σ a ((G).obj Q) (t i))).functorPullback G ∈
        Site.topology p k X Q := by
  apply (Site.topology p k X).superset_covering _
    (CrystallineFrame.CoverLifting.CrystallineFrameCoverLifting.lifted_covering_mem p k B σ a Q ι t ht)
  apply (Sieve.generate_le_iff _ _).mpr
  unfold CrystallinePrincipal.Covers.CrystallinePrincipalCovers.presieve
  intro P f hf
  obtain ⟨i⟩ := hf
  change (Sieve.ofArrows _ _) ((G).map (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q
    (CrystallineFrame.CoverLifting.CrystallineFrameCoverLifting.coefficient p k B σ a Q (t i))))
  rw [← factor_projection]
  exact (Sieve.ofArrows
    (fun j => CrystallineRestriction.FramedCrystallineRestriction.principal p k B σ a ((G).obj Q) (t j))
    (fun j => CrystallineRestriction.FramedCrystallineRestriction.principalProjection p k B σ a ((G).obj Q) (t j))).downward_closed
      (Sieve.ofArrows_mk _ _ i) (factor p k B σ a Q (t i))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.CoverLifting.FramedCrystallineCoverLifting
