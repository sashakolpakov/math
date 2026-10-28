import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.SectionCechIndices
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Cech Intersections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CechIntersections

noncomputable section

/-! The actual categorical intersection opens used by the Čech complex are affine. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

theorem opensProduct_eq_iInf {X : Scheme.{u}} {κ : Type v} (V : κ → X.Opens) :
    (∏ᶜ V) = ⨅ k, V k :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit _) (Preorder.isLimitIInf V)).to_eq

theorem affine_cechIntersection {X : Scheme.{u}} [X.IsSeparated] {ι : Type u}
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    IsAffineOpen (∏ᶜ fun k : Fin (n + 1) ↦ U (i k)) := by
  rw [opensProduct_eq_iInf (fun k : Fin (n + 1) ↦ U (i k))]
  exact IsAffineOpen.iInf (fun k ↦ hU (i k))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CechIntersections
