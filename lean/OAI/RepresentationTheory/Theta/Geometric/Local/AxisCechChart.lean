import OAI.RepresentationTheory.Theta.Geometric.CechAxisFunctional
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Axis Cech Chart -/

namespace OAI.RepresentationTheory.Theta.Geometric.Local.AxisCechChart

noncomputable section

/-! An affine local base has a Cech chart containing its entire axis:
choose a chart at the closed point, then use generalization. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u
variable (S : Scheme.{u}) [IsAffine S] [IsLocalRing Γ(S, ⊤)]

def affineLocalClosedPoint : S := S.isoSpec.inv (IsLocalRing.closedPoint Γ(S, ⊤))

theorem affineLocalClosedPoint_mem_iff (U : S.Opens) :
    affineLocalClosedPoint S ∈ U ↔ U = ⊤ := by
  constructor
  · intro h
    have hp : S.isoSpec.inv ⁻¹ᵁ U = ⊤ :=
      (IsLocalRing.closedPoint_mem_iff _).mp h
    apply top_unique
    intro x _
    have hx : S.isoSpec.inv (S.isoSpec.hom x) ∈ U := by
      change S.isoSpec.hom x ∈ S.isoSpec.inv ⁻¹ᵁ U
      rw [hp]
      trivial
    have he : S.isoSpec.inv (S.isoSpec.hom x) = x :=
      congrArg (fun f : S ⟶ S => f x) S.isoSpec.hom_inv_id
    exact he ▸ hx
  · rintro rfl
    trivial

variable {S} {X : Scheme.{u}} (s : S ⟶ X)

include s in
theorem exists_axis_cech_chart {I : Type u} [LinearOrder I] (U : I → X.Opens)
    (hU : iSup U = ⊤) :
    ∃ i : I, (⊤ : S.Opens) ≤ s ⁻¹ᵁ OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0
      (OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i) := by
  have hx : s (affineLocalClosedPoint S) ∈ iSup U := by
    rw [hU]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have ht : s ⁻¹ᵁ U i = ⊤ := (affineLocalClosedPoint_mem_iff S _).mp hi
  refine ⟨i, ?_⟩
  rw [OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single_open, ht]

end

end OAI.RepresentationTheory.Theta.Geometric.Local.AxisCechChart
