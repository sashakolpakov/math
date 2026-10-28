import OAI.RepresentationTheory.Theta.Geometric.Local.ClosedPointScalars
import OAI.RepresentationTheory.Theta.Geometric.SpecLocalRings

/-! # Spec Closed Point -/

namespace OAI.RepresentationTheory.Theta.Geometric.SpecClosedPoint

noncomputable section

/-! The closed point used for affine Picard equations is the ordinary
closed point when the affine scheme is the spectrum of a local ring. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u
variable (R : Type u) [CommRing R] [IsLocalRing R]
local instance : IsLocalRing Γ(Spec (.of R), ⊤) := SpecLocalRings.specGlobal_isLocalRing R

theorem affineLocalClosedPoint_spec :
    Local.AxisCechChart.affineLocalClosedPoint (Spec (.of R)) = IsLocalRing.closedPoint R := by
  apply (IsLocalRing.specializes_closedPoint (Local.AxisCechChart.affineLocalClosedPoint (Spec (.of R)))).antisymm ?_ |>.eq
  rw [specializes_iff_forall_open]
  intro U hU hx
  have htop := (Local.AxisCechChart.affineLocalClosedPoint_mem_iff (Spec (.of R)) ⟨U, hU⟩).mp hx
  change IsLocalRing.closedPoint R ∈ (⟨U, hU⟩ : (Spec (.of R)).Opens)
  rw [htop]
  trivial

end

end OAI.RepresentationTheory.Theta.Geometric.SpecClosedPoint
