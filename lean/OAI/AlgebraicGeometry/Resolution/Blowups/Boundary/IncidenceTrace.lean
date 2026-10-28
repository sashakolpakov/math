import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.FixedLabelComposition

/-! # Incidence Trace -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A pure incidence trace fixes the containing boundary labels at every blowup, including identity steps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

inductive Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace : Type → Type 1
  | stop (β : Type) : BoundaryIncidenceTrace β
  | step {β : Type} (F : Finset β) (tail : BoundaryIncidenceTrace (Option β)) : BoundaryIncidenceTrace β

def Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace.length {β : Type} (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β) : ℕ := by
  induction T with
  | stop => exact 0
  | step F tail ih => exact ih + 1

def Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace.append {β : Type} (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β) :
    Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels T.length β) → Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β := by
  induction T with
  | stop => exact id
  | step F tail ih => exact fun U => .step F (ih U)

theorem Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace.append_length {β : Type} (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β)
    (U : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels T.length β)) : (T.append U).length = T.length + U.length := by
  induction T with
  | stop => exact (Nat.zero_add _).symm
  | @step β F tail ih =>
      change Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels tail.length (Option β)) at U
      change (tail.append U).length + 1 = (tail.length + 1) + U.length
      rw [ih]
      omega

def Boundary.IncidenceTrace.Construction.disjointBoundaryIncidenceTrace {β : Type} : List (Finset β) → Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β
  | [] => .stop β
  | F :: L => .step F (disjointBoundaryIncidenceTrace (L.map (fun G => G.map Function.Embedding.some)))
termination_by L => L.length
decreasing_by simp

theorem Boundary.IncidenceTrace.Construction.disjointBoundaryIncidenceTrace_length {β : Type} (L : List (Finset β)) :
    (Boundary.IncidenceTrace.Construction.disjointBoundaryIncidenceTrace L).length = L.length := by
  have aux (N : ℕ) : ∀ (β : Type) (L : List (Finset β)), L.length ≤ N →
      (Boundary.IncidenceTrace.Construction.disjointBoundaryIncidenceTrace L).length = L.length := by
    induction N using Nat.strong_induction_on with
    | h N ih =>
        intro β L hL
        cases L with
        | nil => rw [Boundary.IncidenceTrace.Construction.disjointBoundaryIncidenceTrace]; rfl
        | cons F L =>
            rw [Boundary.IncidenceTrace.Construction.disjointBoundaryIncidenceTrace]
            change (Boundary.IncidenceTrace.Construction.disjointBoundaryIncidenceTrace (L.map (fun G => G.map Function.Embedding.some))).length + 1 = L.length + 1
            have ht := ih L.length (by simpa only [List.length_cons] using Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hL)
              (Option β) (L.map (fun G => G.map Function.Embedding.some)) (by simp)
            rw [ht, List.length_map]
  exact aux L.length β L le_rfl

def Smooth.ControlPrefix.Construction.SmoothControlPrefix.HasIncidenceTrace
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ (β : Type) [Fintype β], (β → X.IdealSheafData) → Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β → Prop := by
  induction P with
  | @stop X f hf J =>
      intro β _ D T
      cases T with
      | stop => exact Nonempty (Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ])
      | step => exact False
  | @blowup X hX hNX f J I hI hb hp hs hbl Y g K tail ih =>
      intro β _ D T
      cases T with
      | stop => exact False
      | step F rest =>
          exact (∃ A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D, ∀ i, A.divided i = F) ∧
            ih (Option β) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) rest

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.HasIncidenceTrace.uniformBoundaryCompatible
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ {β : Type} [Fintype β] (D : β → X.IdealSheafData) (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β),
      P.HasIncidenceTrace β D T → P.uniformBoundaryCompatible β D := by
  induction P with
  | stop =>
      intro β _ D T h
      cases T with
      | stop => exact h
      | step => exact False.elim h
  | blowup I hI hb hp hs hbl tail ih =>
      intro β _ D T h
      cases T with
      | stop => exact False.elim h
      | step F rest =>
          obtain ⟨A, hA⟩ := h.1
          exact ⟨⟨A, F, hA⟩, ih _ rest h.2⟩

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.HasIncidenceTrace.stepCount
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ {β : Type} [Fintype β] (D : β → X.IdealSheafData) (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β),
      P.HasIncidenceTrace β D T → P.stepCount = T.length := by
  induction P with
  | stop =>
      intro β _ D T h
      cases T with
      | stop => rfl
      | step => exact False.elim h
  | blowup I hI hb hp hs hbl tail ih =>
      intro β _ D T h
      cases T with
      | stop => exact False.elim h
      | step F rest => exact congrArg (fun a : ℕ => a + 1) (ih (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) rest h.2)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
