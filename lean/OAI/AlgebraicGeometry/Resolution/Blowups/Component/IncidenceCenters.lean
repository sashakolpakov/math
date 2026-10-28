import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.IncidenceCenters
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.EtaleNaturality

/-! # Incidence Centers -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Canonical ordered boundary-incidence factors for the initial component-clearing phase. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

def GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.componentIncidenceCenters
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) {β : Type} [Fintype β] (D : β → X.IdealSheafData) :
    List X.IdealSheafData := by
  classical
  let I := A.center
  let : Smooth (I.subschemeι ≫ f) := A.center_smooth
  let : IsNoetherian X := ⟨⟩
  let : NoetherianSpace I.subscheme := I.subschemeι.isClosedEmbedding.isInducing.noetherianSpace
  let : Fintype (irreducibleComponents I.subscheme) := Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentFintype I
  exact List.ofFn (fun i => Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D ((Fintype.equivFin (Finset β)).symm i))

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.componentIncidenceCenters_length
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) {β : Type} [Fintype β] (D : β → X.IdealSheafData) :
    (A.componentIncidenceCenters D).length = Fintype.card (Finset β) := by
  classical
  exact List.length_ofFn

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.componentIncidenceCenters_comap_etale
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) {β : Type} [Fintype β] (D : β → X.IdealSheafData)
    (AM : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f (A.center) D)
    (q : Y ⟶ X) [Etale q] (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
    (B : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas g K n)
    (E : β → Y.IdealSheafData) (BM : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas g (B.center) E)
    (hstructure : q ≫ f = g) (hJ : J.comap q = K) (hD : ∀ l, (D l).comap q = E l) :
    (A.componentIncidenceCenters D).map (fun C => C.comap q) =
      B.componentIncidenceCenters E := by
  classical
  subst g
  subst K
  let I := A.center
  let C := B.center
  let : Smooth (I.subschemeι ≫ f) := A.center_smooth
  let : Smooth (C.subschemeι ≫ (q ≫ f)) := B.center_smooth
  let : IsNoetherian X := ⟨⟩
  let : IsNoetherian Y := ⟨⟩
  let : NoetherianSpace I.subscheme := I.subschemeι.isClosedEmbedding.isInducing.noetherianSpace
  let : NoetherianSpace C.subscheme := C.subschemeι.isClosedEmbedding.isInducing.noetherianSpace
  let : Fintype (irreducibleComponents I.subscheme) := Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentFintype I
  let : Fintype (irreducibleComponents C.subscheme) := Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentFintype C
  have hC : I.comap q = C := A.center_comap_etale q B
  unfold GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.componentIncidenceCenters
  rw [List.map_ofFn]
  congr 1
  funext i
  exact AM.incidenceCenter_comap_flat_to f I D q (q ≫ f) C E BM hC hD _

end

end OAI.AlgebraicGeometry.Resolution.Blowups
