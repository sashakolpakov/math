import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.StalkDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Euler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TotalTorCoefficient

/-! # Tor Cutoff -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.TorCutoff

noncomputable section

/-! The extra ambient family dimension does not change the endpoint
Tor Euler coefficient: all Tor above the endpoint smooth dimension vanishes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))
  (m : ℕ) [hf : SmoothOfRelativeDimension m f]

include hf

theorem euler_succ (x : X) (M N : ModuleCat (X.presheaf.stalk x)) :
    Tor.Euler.euler (X.presheaf.stalk x) M N (m + 1) =
      Tor.Euler.euler (X.presheaf.stalk x) M N m := by
  have h := StalkDimension.stalk_tor_length_zero f m x M N (m + 1) (Nat.lt_succ_self m)
  simp only [Tor.Euler.euler, Finset.sum_range_succ (n := m + 1),
    ExactLength.rationalLength, h, ENat.toNat_zero, Nat.cast_zero, mul_zero, add_zero]

theorem coefficient_succ (A B : IrreducibleCloseds X) (x : X) :
    TotalTorCoefficient.coefficient X A B x (m + 1) =
      TotalTorCoefficient.coefficient X A B x m := by
  unfold TotalTorCoefficient.coefficient
  split_ifs with h
  · exact euler_succ f m x (CycleClass.Thom.IntersectionGeometry.localSupportModule X A x h.1) (CycleClass.Thom.IntersectionGeometry.localSupportModule X B x h.2)
  · rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.TorCutoff
