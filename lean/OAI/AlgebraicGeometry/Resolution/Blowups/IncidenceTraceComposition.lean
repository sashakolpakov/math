import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.IncidenceTrace
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.HomogenizedTransport

/-! # Incidence Trace Composition -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Exact incidence traces compose and survive a change of controlled ideal along the same blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem IncidenceTraceComposition.Construction.relabelBoundaryByLength_succ {n N : ℕ} {β T : Type} (h : n + 1 = N + 1)
    (u : ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels n (Option β) → T) :
    ControlPrefix.FixedLabels.Construction.relabelBoundaryByLength (β := β) h u = ControlPrefix.FixedLabels.Construction.relabelBoundaryByLength (Nat.add_right_cancel h) u := by
  have he : n = N := Nat.add_right_cancel h
  subst N
  rfl

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.HasIncidenceTrace.append
    {b : ℕ} {X Y Z : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : Z.IdealSheafData}
    (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b Y g K Z h L) :
    ∀ {β : Type} [Fintype β] (D : β → X.IdealSheafData) (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β)
      (hP : P.HasIncidenceTrace β D T) (U : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels T.length β)),
      Q.HasIncidenceTrace (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels T.length β)
        (P.boundaryAtLength D T.length (hP.stepCount P D T)) U →
      (P.append Q).HasIncidenceTrace β D (T.append U) := by
  induction P with
  | stop =>
      intro β _ D T hP U hQ
      cases T with
      | stop => exact hQ
      | step => exact False.elim hP
  | blowup I hI hb hp hs hbl tail ih =>
      intro β _ D T hP U hQ
      cases T with
      | stop => exact False.elim hP
      | step F rest =>
          change Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels rest.length (Option β)) at U
          have htail : tail.HasIncidenceTrace (Option β) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) rest := hP.2
          have he : (Smooth.ControlPrefix.Construction.SmoothControlPrefix.blowup I hI hb hp hs hbl tail).boundaryAtLength D (rest.length + 1)
              (hP.stepCount _ D (.step F rest)) =
              tail.boundaryAtLength (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) rest.length
                (htail.stepCount tail _ rest) :=
            IncidenceTraceComposition.Construction.relabelBoundaryByLength_succ (hP.stepCount _ D (.step F rest))
              (tail.canonicalBoundary (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D))
          have hQ' : Q.HasIncidenceTrace (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels rest.length (Option β))
              (tail.boundaryAtLength (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) rest.length
                (htail.stepCount tail _ rest)) U := by
            rw [← he]
            exact hQ
          exact ⟨hP.1, ih Q (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) rest htail U hQ'⟩

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups.hasIncidenceTrace
    {b c : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J L : X.IdealSheafData} {K M : Y.IdealSheafData}
    {P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K} {Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix c X f L Y g M}
    (h : Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups b c P Q) :
    ∀ {β : Type} [Fintype β] (D : β → X.IdealSheafData) (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β),
      P.HasIncidenceTrace β D T → Q.HasIncidenceTrace β D T := by
  induction h with
  | stop => intro β _ D T hP; exact hP
  | blowup I hI hb hc hp hq hs hbl tail ih =>
      intro β _ D T hP
      cases T with
      | stop => exact False.elim hP
      | step F rest => exact ⟨hP.1, ih (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) rest hP.2⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
