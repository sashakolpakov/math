import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.RefinementNeighborhood

/-! # Refinement Atlas -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Disjoint native boundary refinements preserve normal-crossing and common-center atlases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.refineDisjointBoundary
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData}
    {β γ : Type} [Fintype γ] {r : γ → β}
    {D : β → X.IdealSheafData} {E : γ → X.IdealSheafData}
    (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) (B : Disjoint.BoundaryRefinement.Construction.DisjointBoundaryRefinement r D E) :
    Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I E := by
  let O (x : X) := Boundary.RefinementNeighborhood.Construction.boundaryRefinementNeighborhood E x
  let C : X.OpenCover := Scheme.Cover.mkOfCovers X (fun x => O x) (fun x => (O x).ι)
    (fun x => ⟨x, ⟨⟨x, Boundary.RefinementNeighborhood.Construction.mem_boundaryRefinementNeighborhood E x⟩, rfl⟩⟩) (fun _ => inferInstance)
  apply Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.ofOpenCover f I E C
  intro x
  change X at x
  exact (A.comapOpen f (O x).ι).pullbackLabels (Boundary.RefinementNeighborhood.Construction.boundaryRefinementPartialLabel r E x)
    (B.partialLabel_injective x) (fun j => (E j).comap (O x).ι) (B.local_label_eq x)

def Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.refineDisjointBoundary
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β γ : Type} [Fintype γ]
    {D : β → X.IdealSheafData} {E : γ → X.IdealSheafData} {r : γ → β} {L : List (Finset β)}
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L) (B : Disjoint.BoundaryRefinement.Construction.DisjointBoundaryRefinement r D E) :
    Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f E [Finset.univ] :=
  (A.unitCenter.refineDisjointBoundary B).boundaryAtlas

theorem Global.MonomialSequence.Construction.SmoothFixedControlSequence.boundaryCompatible_refine
    {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f J) {β γ : Type} [Fintype β] [Fintype γ]
    {D : β → X.IdealSheafData} {E : γ → X.IdealSheafData} (r : γ → β)
    (hT : T.boundaryCompatible β D) (B : Disjoint.BoundaryRefinement.Construction.DisjointBoundaryRefinement r D E) :
    T.boundaryCompatible γ E := by
  induction T generalizing β γ with
  | terminal =>
      obtain ⟨A⟩ := hT
      exact ⟨A.refineDisjointBoundary B⟩
  | blowup I hI hb hp hs hbl tail ih =>
      obtain ⟨A⟩ := hT.1
      exact ⟨⟨A.refineDisjointBoundary B⟩,
        ih (Option.map r) hT.2 (B.blowup I hI)⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
