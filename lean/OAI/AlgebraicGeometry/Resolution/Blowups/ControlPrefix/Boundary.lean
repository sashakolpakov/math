import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ControlPrefix
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.SequenceCompatibility

/-! # Boundary -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Native labelled boundaries and their compatibility along actual finite blowup prefixes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData}

def Smooth.ControlPrefix.Construction.SmoothControlPrefix.endpointLabels (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) (β : Type) : Type := by
  induction P generalizing β with
  | stop => exact β
  | blowup _ _ _ _ _ _ _ ih => exact ih (Option β)

instance Smooth.ControlPrefix.Construction.SmoothControlPrefix.endpointLabels_fintype (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) (β : Type) [Fintype β] :
    Fintype (P.endpointLabels β) := by
  induction P generalizing β with
  | stop => exact inferInstanceAs (Fintype β)
  | blowup _ _ _ _ _ _ _ ih => exact ih (Option β)

def Smooth.ControlPrefix.Construction.SmoothControlPrefix.endpointBoundary (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) {β : Type}
    (D : β → X.IdealSheafData) : P.endpointLabels β → Y.IdealSheafData := by
  induction P generalizing β with
  | stop => exact D
  | blowup I hI _ _ _ _ _ ih => exact ih (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D)

def Smooth.ControlPrefix.Construction.SmoothControlPrefix.boundaryCompatible (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) (β : Type) [Fintype β]
    (D : β → X.IdealSheafData) : Prop := by
  induction P generalizing β with
  | @stop X f hf J => exact Nonempty (Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ])
  | @blowup X _ _ f _ I hI _ _ _ _ _ _ _ tail ih =>
      exact Nonempty (Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) ∧ ih (Option β) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D)

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.endpointBoundary_atlas (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (hP : P.boundaryCompatible β D) :
    Nonempty (Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas g (P.endpointBoundary D) [Finset.univ]) := by
  induction P generalizing β with
  | stop => exact hP
  | blowup I hI hb hp hs hbl tail ih => exact ih _ hP.2

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.attach_boundaryCompatible (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K)
    (S : Global.MonomialSequence.Construction.SmoothFixedControlSequence b Y g K) {β : Type} [Fintype β]
    (D : β → X.IdealSheafData) (hP : P.boundaryCompatible β D)
    (hS : S.boundaryCompatible (P.endpointLabels β) (P.endpointBoundary D)) :
    (P.attach S).boundaryCompatible β D := by
  induction P generalizing β with
  | stop => exact hS
  | blowup I hI hb hp hs hbl tail ih => exact ⟨hP.1, ih S _ hP.2 hS⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
