import OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceTraceComposition

/-! # Incidence Trace Fixed Composition -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Incidence traces compose at a prescribed common length without depending on scheme-specific prefix types. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace.appendAtLength {β : Type} (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β)
    (N : ℕ) (hN : T.length = N) (U : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N β)) : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β := by
  subst N
  exact T.append U

theorem Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace.appendAtLength_length {β : Type} (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β)
    (N : ℕ) (hN : T.length = N) (U : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N β)) :
    (T.appendAtLength N hN U).length = N + U.length := by
  subst N
  exact T.append_length U

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.HasIncidenceTrace.appendAtLength
    {b : ℕ} {X Y Z : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : Z.IdealSheafData}
    (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b Y g K Z h L)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β)
    (hP : P.HasIncidenceTrace β D T) (N : ℕ) (hN : T.length = N)
    (U : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N β))
    (hQ : Q.HasIncidenceTrace (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N β)
      (P.boundaryAtLength D N ((hP.stepCount P D T).trans hN)) U) :
    (P.append Q).HasIncidenceTrace β D (T.appendAtLength N hN U) := by
  subst N
  exact hP.append P Q D T U hQ

end

end OAI.AlgebraicGeometry.Resolution.Blowups
