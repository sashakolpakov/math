import OAI.RepresentationTheory.Theta.Geometric.Geometry
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting

/-! # Domain Topology -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The original negative-line domain is contractible. Its topology
therefore gives uniqueness and existence of covering lifts from one
specified source-fiber point. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.domain_zero_mem (hg : D.pel.HasIntegralModelGeometry) : (0 : LinearTheta.BallCoordinates) ∈ D.domain := by
  have h := hg.reference_admissible
  rcases h with ⟨_, _, _, hn, _⟩
  change Complex.normSq 0 + Complex.normSq 0 < -(D.pel.reference.μ D.pel.reference.b).re
  simpa only [Complex.normSq_zero, zero_add] using neg_pos.mpr hn

def Data.ActiveHeckeThetaData.domainOrigin (hg : D.pel.HasIntegralModelGeometry) : D.domain := ⟨0, D.domain_zero_mem hg⟩

theorem Data.ActiveHeckeThetaData.domain_contractible (hg : D.pel.HasIntegralModelGeometry) : ContractibleSpace D.domain :=
  (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ball_starConvex (D.pel.reference.μ D.pel.reference.b)).contractibleSpace
    ⟨0, D.domain_zero_mem hg⟩

theorem Data.ActiveHeckeThetaData.domain_simplyConnected (hg : D.pel.HasIntegralModelGeometry) : SimplyConnectedSpace D.domain := by
  let : ContractibleSpace D.domain := D.domain_contractible hg
  infer_instance

theorem Data.ActiveHeckeThetaData.domain_locallyPathConnected : LocallyPathConnectedSpace D.domain := by
  exact D.domain.isOpen.locallyPathConnectedSpace

end

end OAI.RepresentationTheory.Theta.Geometric
