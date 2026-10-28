import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.FixedLabels
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.PrefixBoundaryReindex
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.Composition

/-! # Fixed Label Composition -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Continuations with prescribed endpoint labels compose with the original actual prefix. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {b : ℕ} {X Y Z : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {h : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : Z.IdealSheafData}

def Smooth.ControlPrefix.Construction.SmoothControlPrefix.endpointLabelsEquivAtLength (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) (β : Type)
    (N : ℕ) (hN : P.stepCount = N) : P.endpointLabels β ≃ ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N β :=
  (P.endpointLabelsEquiv β).trans (Equiv.cast (congrArg (fun n => ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels n β) hN))

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.boundaryAtLength_equiv (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) {β : Type}
    (D : β → X.IdealSheafData) (N : ℕ) (hN : P.stepCount = N) (j : P.endpointLabels β) :
    P.boundaryAtLength D N hN (P.endpointLabelsEquivAtLength β N hN j) = P.endpointBoundary D j := by
  subst N
  exact congrArg (P.endpointBoundary D) ((P.endpointLabelsEquiv β).symm_apply_apply j)

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.uniformBoundaryCompatible_of_fixed_labels
    (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b Y g K Z h L)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (N : ℕ) (hN : P.stepCount = N)
    (hQ : Q.uniformBoundaryCompatible (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N β) (P.boundaryAtLength D N hN)) :
    Q.uniformBoundaryCompatible (P.endpointLabels β) (P.endpointBoundary D) := by
  have ht := Q.uniformBoundaryCompatible_reindex _ _ _ hQ (P.endpointLabelsEquivAtLength β N hN).toEmbedding
  have heq : (fun j => P.boundaryAtLength D N hN (P.endpointLabelsEquivAtLength β N hN j)) =
      P.endpointBoundary D := funext (P.boundaryAtLength_equiv D N hN)
  change Q.uniformBoundaryCompatible (P.endpointLabels β)
    (fun j => P.boundaryAtLength D N hN (P.endpointLabelsEquivAtLength β N hN j)) at ht
  rw [heq] at ht
  exact ht

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.append_uniformBoundaryCompatible_fixed_labels
    (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b Y g K Z h L)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (hP : P.uniformBoundaryCompatible β D)
    (N : ℕ) (hN : P.stepCount = N)
    (hQ : Q.uniformBoundaryCompatible (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N β) (P.boundaryAtLength D N hN)) :
    (P.append Q).uniformBoundaryCompatible β D :=
  P.append_uniformBoundaryCompatible Q D hP (P.uniformBoundaryCompatible_of_fixed_labels Q D N hN hQ)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
