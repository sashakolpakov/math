import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.IncidenceControlPrefix

/-! # Composition -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Actual prefixes compose while preserving the same geometric maps and uniform boundary-incidence witnesses. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {b : ℕ} {X Y Z : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : Z.IdealSheafData}

def Smooth.ControlPrefix.Construction.SmoothControlPrefix.append (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b Y g K Z h L) :
    Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Z h L := by
  induction P with
  | stop => exact Q
  | blowup I hI hb hp hs hbl tail ih => exact .blowup I hI hb hp hs hbl (ih Q)

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.append_toBase (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b Y g K Z h L) :
    (P.append Q).toBase = Q.toBase ≫ P.toBase := by
  induction P with
  | stop => exact (Category.comp_id _).symm
  | blowup I hI hb hp hs hbl tail ih =>
      change (tail.append Q).toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI = Q.toBase ≫ (tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI)
      rw [ih, Category.assoc]

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.append_stepCount (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b Y g K Z h L) :
    (P.append Q).stepCount = P.stepCount + Q.stepCount := by
  induction P with
  | stop => exact (Nat.zero_add _).symm
  | blowup I hI hb hp hs hbl tail ih =>
      change (tail.append Q).stepCount + 1 = (tail.stepCount + 1) + Q.stepCount
      rw [ih]
      omega

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.append_uniformBoundaryCompatible
    (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b Y g K Z h L)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (hP : P.uniformBoundaryCompatible β D)
    (hQ : Q.uniformBoundaryCompatible (P.endpointLabels β) (P.endpointBoundary D)) :
    (P.append Q).uniformBoundaryCompatible β D := by
  induction P generalizing β with
  | stop => exact hQ
  | blowup I hI hb hp hs hbl tail ih => exact ⟨hP.1, ih Q _ hP.2 hQ⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
