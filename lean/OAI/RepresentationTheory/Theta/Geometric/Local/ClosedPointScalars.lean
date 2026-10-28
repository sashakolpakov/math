import OAI.RepresentationTheory.Theta.Geometric.Local.AxisCechChart
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FieldPoint
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Closed Point Scalars -/

namespace OAI.RepresentationTheory.Theta.Geometric.Local.ClosedPointScalars

noncomputable section

/-! A field-valued point over the closed point of an affine local scheme
induces a local map on actual global functions. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u
variable (S : Scheme.{u}) [IsAffine S] [IsLocalRing Γ(S, ⊤)]

theorem affineLocalClosedPoint_toSpecΓ :
    S.toSpecΓ (AxisCechChart.affineLocalClosedPoint S) = IsLocalRing.closedPoint Γ(S, ⊤) :=
  congrArg (fun f : Spec Γ(S, ⊤) ⟶ Spec Γ(S, ⊤) => f (IsLocalRing.closedPoint Γ(S, ⊤)))
    S.isoSpec.inv_hom_id

theorem fieldPoint_isLocalHom_of_closedPoint {K : Type u} [Field K]
    (g : Spec (.of K) ⟶ S) (hg : g (IsLocalRing.closedPoint K) = AxisCechChart.affineLocalClosedPoint S) :
    IsLocalHom g.appTop.hom := by
  let : Field Γ(Spec (.of K), ⊤) := AlgebraicGeometry.Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField K
  have hk := AlgebraicGeometry.Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.kernel g (IsLocalRing.closedPoint K)
  rw [hg, affineLocalClosedPoint_toSpecΓ] at hk
  refine ⟨fun a ha => ?_⟩
  by_contra hn
  have hm : a ∈ (IsLocalRing.closedPoint Γ(S, ⊤)).asIdeal := hn
  have hz : a ∈ RingHom.ker g.appTop.hom := hk ▸ hm
  exact ha.ne_zero hz

theorem affineLocalResidue_isLocalHom :
    IsLocalHom (S.fromSpecResidueField (AxisCechChart.affineLocalClosedPoint S)).appTop.hom :=
  fieldPoint_isLocalHom_of_closedPoint S _ (S.fromSpecResidueField_apply _ _)

end

end OAI.RepresentationTheory.Theta.Geometric.Local.ClosedPointScalars
