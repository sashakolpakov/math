import OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceTraceFixedComposition

/-! # Same Trace Composition -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A continuation expressed using an auxiliary prefix's fixed labels also composes with its residual prefix. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups.append_traceAtLength
    {a b : ℕ} {X Y Z : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J C : X.IdealSheafData} {K L : Y.IdealSheafData} {M : Z.IdealSheafData}
    (A : Smooth.ControlPrefix.Construction.SmoothControlPrefix a X f C Y g L) (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K)
    (R : Smooth.ControlPrefix.Construction.SmoothControlPrefix b Y g K Z h M) (same : Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups a b A P)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β)
    (hA : A.HasIncidenceTrace β D T) (N : ℕ) (hN : T.length = N)
    (U : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N β))
    (hR : R.HasIncidenceTrace (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N β)
      (A.boundaryAtLength D N ((hA.stepCount A D T).trans hN)) U) :
    (P.append R).HasIncidenceTrace β D (T.appendAtLength N hN U) := by
  have hP := same.hasIncidenceTrace D T hA
  have he := same.boundaryAtLength β D N ((hA.stepCount A D T).trans hN) ((hP.stepCount P D T).trans hN)
  apply hP.appendAtLength P R D T N hN U
  rw [← he]
  exact hR

end

end OAI.AlgebraicGeometry.Resolution.Blowups
