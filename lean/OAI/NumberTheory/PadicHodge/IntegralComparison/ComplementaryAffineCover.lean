import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.SetTheory.Cardinal.Order

/-! # Complementary Affine Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ComplementaryAffineCover

noncomputable section

/-! An actual affine cover adapted to one affine neighborhood and its
open complement. Its distinguished member is the original neighborhood. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u
variable {X : Scheme.{u}} (O : X.Opens)

def Index : Type u := { V : X.affineOpens // V.val ≤ O }

instance indexLinearOrder : LinearOrder (Index O) :=
  IsWellOrder.linearOrder WellOrderingRel

def opens (i : Index O) : X.Opens := i.val.val

theorem affine (i : Index O) : IsAffineOpen (opens O i) := i.val.property

theorem le (i : Index O) : opens O i ≤ O := i.property

theorem covers : (⨆ i, opens O i) = O := by
  apply le_antisymm (iSup_le (le O))
  intro x hx
  obtain ⟨V, hV, hxV, hVO⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  exact Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVO⟩, hxV⟩

variable (U : X.Opens)

def cover : WithBot (Index O) → X.Opens :=
  RelativeCech.Intersections.cover U (opens O)

theorem cover_bot : cover O U ⊥ = U := rfl

theorem cover_coe (i : Index O) : cover O U (i : WithBot (Index O)) = opens O i := rfl

theorem cover_affine (hU : IsAffineOpen U) (i : WithBot (Index O)) :
    IsAffineOpen (cover O U i) := by
  cases i with
  | bot => exact hU
  | coe i => exact affine O i

theorem cover_top (h : U ⊔ O = ⊤) : (⨆ i, cover O U i) = ⊤ := by
  apply top_unique
  intro x _
  have hx : x ∈ U ⊔ O := by rw [h]; trivial
  rcases hx with hx | hx
  · exact Opens.mem_iSup.mpr ⟨⊥, hx⟩
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, opens O i by rw [covers]; exact hx)
    exact Opens.mem_iSup.mpr ⟨(i : WithBot (Index O)), hi⟩

theorem intersection_covers : (⨆ i, U ⊓ opens O i) = U ⊓ O := by
  rw [← inf_iSup_eq, covers]

theorem intersection_affine [X.IsSeparated] (hU : IsAffineOpen U) (i : Index O) :
    IsAffineOpen (U ⊓ opens O i) := hU.inf (affine O i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ComplementaryAffineCover
