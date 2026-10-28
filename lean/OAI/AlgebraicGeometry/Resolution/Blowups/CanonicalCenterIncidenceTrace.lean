import OAI.AlgebraicGeometry.Resolution.Blowups.OrderedIncidenceTrace
import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.IncidenceCenters
import OAI.AlgebraicGeometry.Resolution.Blowups.Component.IncidenceCenters

/-! # Canonical Center Incidence Trace -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Canonical component and surface refinements have a trace determined only by their initial boundary labels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

def CanonicalCenterIncidenceTrace.Construction.canonicalCenterIncidenceTrace (β : Type) [Fintype β] : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β := by
  classical
  exact Boundary.IncidenceTrace.Construction.disjointBoundaryIncidenceTrace (List.ofFn (Fintype.equivFin (Finset β)).symm)

theorem CanonicalCenterIncidenceTrace.Construction.canonicalCenterIncidenceTrace_length (β : Type) [Fintype β] :
    (CanonicalCenterIncidenceTrace.Construction.canonicalCenterIncidenceTrace β).length = Fintype.card (Finset β) := by
  classical
  rw [CanonicalCenterIncidenceTrace.Construction.canonicalCenterIncidenceTrace, Boundary.IncidenceTrace.Construction.disjointBoundaryIncidenceTrace_length, List.length_ofFn]

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.componentIncidenceCenters_hasTrace
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData)
    (AM : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f (A.center) D)
    {b : ℕ} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K)
    (hP : P.followsCenters (A.componentIncidenceCenters D)) :
    P.HasIncidenceTrace β D (CanonicalCenterIncidenceTrace.Construction.canonicalCenterIncidenceTrace β) := by
  classical
  let I := A.center
  let : Smooth (I.subschemeι ≫ f) := A.center_smooth
  let : IsNoetherian X := ⟨⟩
  let : NoetherianSpace I.subscheme := I.subschemeι.isClosedEmbedding.isInducing.noetherianSpace
  let : Fintype (irreducibleComponents I.subscheme) := Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentFintype I
  exact P.hasIncidenceTrace_of_incidence_centers f I J (A.center_ne_bot) D AM
    (Fintype.equivFin (Finset β)).symm hP

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceIncidenceCenters_hasTrace
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (ℓ : ℕ)
    (hb : ∀ i, (A.choice i).HasBound (ℓ + 1)) (hd : ∀ i, ringKrullDim (A.rings i) ≤ 2)
    (hlevel : (n + 1).factorial ≤ ℓ + 1)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData)
    (AM : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f (A.surfaceCenter ℓ hb hd hlevel) D)
    {b : ℕ} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K)
    (hP : P.followsCenters (A.surfaceIncidenceCenters ℓ hb hd hlevel D)) :
    P.HasIncidenceTrace β D (CanonicalCenterIncidenceTrace.Construction.canonicalCenterIncidenceTrace β) := by
  classical
  let I := A.surfaceCenter ℓ hb hd hlevel
  let : Smooth (I.subschemeι ≫ f) := A.surfaceCenter_isSmooth ℓ hb hd hlevel
  let : IsNoetherian X := ⟨⟩
  let : NoetherianSpace I.subscheme := I.subschemeι.isClosedEmbedding.isInducing.noetherianSpace
  let : Fintype (irreducibleComponents I.subscheme) := Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentFintype I
  exact P.hasIncidenceTrace_of_incidence_centers f I J (A.surfaceCenter_nonzero ℓ hb hd hlevel) D AM
    (Fintype.equivFin (Finset β)).symm hP

end

end OAI.AlgebraicGeometry.Resolution.Blowups
