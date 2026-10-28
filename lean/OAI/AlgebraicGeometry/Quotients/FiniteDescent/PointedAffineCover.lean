import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineCover
import Mathlib.Order.ULift

/-! # Pointed Affine Cover -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PointedAffineCover.Construction.PointedFiniteAffineCover

noncomputable section

/-! A finite ordered affine cover with a chosen member containing a
rational point, indexed in the universe of the schemes. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}

structure Data (s : Spec (.of K) ⟶ X) where
  I : Type u
  fintype : Fintype I
  linearOrder : LinearOrder I
  opens : I → X.Opens
  affine : ∀ i, IsAffineOpen (opens i)
  covers : iSup opens = ⊤
  distinguished : I
  point_in : ⊤ ≤ s ⁻¹ᵁ opens distinguished

def ofIntegral [IsIntegral X] [CompactSpace X] (s : Spec (.of K) ⟶ X) : Data s := by
  classical
  let D := AffineCover.Construction.FiniteAffineCover.ofIntegral X
  let i := Classical.choose (D.covers (s (IsLocalRing.closedPoint K)))
  have hi := Classical.choose_spec (D.covers (s (IsLocalRing.closedPoint K)))
  refine ⟨ULift.{u} (Fin D.n), inferInstance, inferInstance, (fun j => D.opens j.down),
    (fun j => D.affine j.down), ?_, ⟨i⟩, ?_⟩
  · apply top_unique
    intro x _
    obtain ⟨j, hj⟩ := D.covers x
    exact Opens.mem_iSup.mpr ⟨⟨j⟩, hj⟩
  · intro z _
    have hz : z = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    exact hz ▸ hi

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PointedAffineCover.Construction.PointedFiniteAffineCover
