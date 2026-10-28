import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.Boundary
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.UniformIncidenceTransform

/-! # Incidence Control Prefix -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Actual prefixes whose centers have one global boundary-incidence set at every step. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData}

def Smooth.ControlPrefix.Construction.SmoothControlPrefix.uniformBoundaryCompatible (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K)
    (β : Type) [Fintype β] (D : β → X.IdealSheafData) : Prop := by
  induction P generalizing β with
  | @stop X f hf J => exact Nonempty (Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ])
  | @blowup X _ _ f _ I hI _ _ _ _ _ _ _ tail ih =>
      exact (∃ (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) (F : Finset β), ∀ i, A.divided i = F) ∧
        ih (Option β) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D)

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.uniformBoundaryCompatible.boundaryCompatible
    (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) {β : Type} [Fintype β]
    (D : β → X.IdealSheafData) (hP : P.uniformBoundaryCompatible β D) : P.boundaryCompatible β D := by
  induction P generalizing β with
  | stop => exact hP
  | blowup I hI hb hp hs hbl tail ih =>
      obtain ⟨A, F, hF⟩ := hP.1
      exact ⟨⟨A⟩, ih _ hP.2⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
