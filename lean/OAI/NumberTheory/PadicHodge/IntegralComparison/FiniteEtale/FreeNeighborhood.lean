import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRhamTraceRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FreeCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Free.TensorTransport

/-! # Free Neighborhood -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FreeNeighborhood

noncomputable section

/-! Finite étale scheme maps have actual affine neighborhoods on which
their algebra of sections is free. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRhamTraceRestriction

universe u

variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left]

def IsFreeOn (U : Y.left.Opens) : Prop :=
  letI := AffineOpen.DeRhamTrace.sectionAlgebra R X Y f U
  Module.Free (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U)

theorem exists_subopen (U : Y.left.Opens) (hU : IsAffineOpen U)
    (x : Y.left) (hx : x ∈ U) :
    ∃ V : Y.left.Opens, x ∈ V ∧ V ≤ U ∧ IsAffineOpen V ∧ IsFreeOn R X Y f V := by
  let : Fact (IsAffineOpen U) := ⟨hU⟩
  let sectionAlg : Algebra (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) :=
    AffineOpen.DeRhamTrace.sectionAlgebra R X Y f U
  let : Algebra.Etale (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) := AffineOpen.DeRhamTrace.sectionEtale R X Y f U hU
  let : Module.Finite (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) := f.left.finite_app U hU
  have hxrange : x ∈ Set.range hU.fromSpec := by rwa [hU.range_fromSpec]
  obtain ⟨p, hp⟩ := hxrange
  obtain ⟨r, hr, hfree⟩ := @FreeCover.exists_at_prime
    (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) inferInstance inferInstance sectionAlg
      inferInstance inferInstance p
  let V := Y.left.basicOpen r
  have hVU : V ≤ U := Y.left.basicOpen_le r
  have hV : IsAffineOpen V := hU.basicOpen r
  have hxV : x ∈ V := by
    rw [← hp]
    change p ∈ hU.fromSpec ⁻¹ᵁ Y.left.basicOpen r
    exact (hU.fromSpec_preimage_basicOpen (r : Γ(Y.left, U))).symm ▸ hr
  refine ⟨V, hxV, hVU, hV, ?_⟩
  let : Fact (IsAffineOpen V) := ⟨hV⟩
  let : Fact (V ≤ U) := ⟨hVU⟩
  let := AffineOpen.DeRhamTrace.sectionAlgebra R X Y f V
  let := AffineOpen.DeRhamTraceRestriction.targetAlgebra R Y U V
  let := AffineOpen.DeRhamTraceRestriction.sourceAlgebra R X Y f U V
  let := AffineOpen.DeRhamTraceRestriction.diagonalAlgebra R X Y f U V
  let := AffineOpen.DeRhamTraceRestriction.firstDiagonalTower R X Y f U V
  let := AffineOpen.DeRhamTraceRestriction.secondDiagonalTower R X Y f U V
  let : IsLocalization.Away r (AffineOpen.DeRhamTrace.targetRing R Y V) := hU.isLocalization_basicOpen r
  let : Module.Free (Localization.Away r)
      (Localization.Away r ⊗[AffineOpen.DeRhamTrace.targetRing R Y U] AffineOpen.DeRhamTrace.sourceRing R X Y f U) := hfree
  let e := IsLocalization.algEquiv (.powers r) (Localization.Away r) (AffineOpen.DeRhamTrace.targetRing R Y V)
  let : Module.Free (AffineOpen.DeRhamTrace.targetRing R Y V)
      (AffineOpen.DeRhamTrace.targetRing R Y V ⊗[AffineOpen.DeRhamTrace.targetRing R Y U] AffineOpen.DeRhamTrace.sourceRing R X Y f U) :=
    IntegralComparison.Free.TensorTransport.free (B := AffineOpen.DeRhamTrace.sourceRing R X Y f U) e
  let : Algebra.IsPushout (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.targetRing R Y V)
      (AffineOpen.DeRhamTrace.sourceRing R X Y f U) (AffineOpen.DeRhamTrace.sourceRing R X Y f V) :=
    AffineOpen.DeRhamTraceRestriction.sectionPushout R X Y f U V
  exact Module.Free.of_equiv (Algebra.IsPushout.equiv (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.targetRing R Y V)
    (AffineOpen.DeRhamTrace.sourceRing R X Y f U) (AffineOpen.DeRhamTrace.sourceRing R X Y f V)).toLinearEquiv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FreeNeighborhood
