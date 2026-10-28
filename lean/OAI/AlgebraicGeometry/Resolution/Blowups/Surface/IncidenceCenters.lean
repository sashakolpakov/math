import OAI.AlgebraicGeometry.Resolution.Blowups.OrderedUniformIncidencePrefix
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalSurface.CenterNaturality

/-! # Incidence Centers -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The prescribed list of boundary-incidence factors of a fixed-level surface center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.incidenceCenter_comap_flat_to
    {X Y : Scheme} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData)
    [Smooth (I.subschemeι ≫ f)] [Fintype (irreducibleComponents I.subscheme)]
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    (q : Y ⟶ X) [Flat q] (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (C : Y.IdealSheafData)
    [Smooth (C.subschemeι ≫ g)] [Fintype (irreducibleComponents C.subscheme)]
    (E : β → Y.IdealSheafData) (B : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas g C E)
    (hC : I.comap q = C) (hD : ∀ l, (D l).comap q = E l) (F : Finset β) :
    (Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D F).comap q = Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter g C E F := by
  classical
  subst C
  have he : (fun l => (D l).comap q) = E := funext hD
  subst E
  exact A.incidenceCenter_comap_flat f I D q g B F

def GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceIncidenceCenters
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (ℓ : ℕ)
    (hb : ∀ i, (A.choice i).HasBound (ℓ + 1)) (hd : ∀ i, ringKrullDim (A.rings i) ≤ 2)
    (hlevel : (n + 1).factorial ≤ ℓ + 1) {β : Type} [Fintype β] (D : β → X.IdealSheafData) :
    List X.IdealSheafData := by
  classical
  let I := A.surfaceCenter ℓ hb hd hlevel
  let : Smooth (I.subschemeι ≫ f) := A.surfaceCenter_isSmooth ℓ hb hd hlevel
  let : IsNoetherian X := ⟨⟩
  let : NoetherianSpace I.subscheme := I.subschemeι.isClosedEmbedding.isInducing.noetherianSpace
  let : Fintype (irreducibleComponents I.subscheme) := Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentFintype I
  exact List.ofFn (fun i => Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D ((Fintype.equivFin (Finset β)).symm i))

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceIncidenceCenters_length
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (ℓ : ℕ)
    (hb : ∀ i, (A.choice i).HasBound (ℓ + 1)) (hd : ∀ i, ringKrullDim (A.rings i) ≤ 2)
    (hlevel : (n + 1).factorial ≤ ℓ + 1) {β : Type} [Fintype β] (D : β → X.IdealSheafData) :
    (A.surfaceIncidenceCenters ℓ hb hd hlevel D).length = Fintype.card (Finset β) := by
  classical
  exact List.length_ofFn

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceIncidenceCenters_comap_etale
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (ℓ : ℕ)
    (ha : ∀ i, (A.choice i).HasBound (ℓ + 1)) (hdA : ∀ i, ringKrullDim (A.rings i) ≤ 2)
    (hlevel : (n + 1).factorial ≤ ℓ + 1) {β : Type} [Fintype β] (D : β → X.IdealSheafData)
    (AM : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f (A.surfaceCenter ℓ ha hdA hlevel) D)
    (q : Y ⟶ X) [Etale q] (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
    (B : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas g K n)
    (hb : ∀ i, (B.choice i).HasBound (ℓ + 1)) (hdB : ∀ i, ringKrullDim (B.rings i) ≤ 2)
    (E : β → Y.IdealSheafData) (BM : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas g (B.surfaceCenter ℓ hb hdB hlevel) E)
    (hstructure : q ≫ f = g) (hJ : J.comap q = K) (hD : ∀ l, (D l).comap q = E l) :
    (A.surfaceIncidenceCenters ℓ ha hdA hlevel D).map (fun C => C.comap q) =
      B.surfaceIncidenceCenters ℓ hb hdB hlevel E := by
  classical
  subst g
  subst K
  let I := A.surfaceCenter ℓ ha hdA hlevel
  let C := B.surfaceCenter ℓ hb hdB hlevel
  let : Smooth (I.subschemeι ≫ f) := A.surfaceCenter_isSmooth ℓ ha hdA hlevel
  let : Smooth (C.subschemeι ≫ (q ≫ f)) := B.surfaceCenter_isSmooth ℓ hb hdB hlevel
  let : IsNoetherian X := ⟨⟩
  let : IsNoetherian Y := ⟨⟩
  let : NoetherianSpace I.subscheme := I.subschemeι.isClosedEmbedding.isInducing.noetherianSpace
  let : NoetherianSpace C.subscheme := C.subschemeι.isClosedEmbedding.isInducing.noetherianSpace
  let : Fintype (irreducibleComponents I.subscheme) := Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentFintype I
  let : Fintype (irreducibleComponents C.subscheme) := Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentFintype C
  have hC : I.comap q = C := A.surfaceCenter_comap_etale ℓ ha hdA hlevel q B hb hdB
  unfold GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceIncidenceCenters
  rw [List.map_ofFn]
  congr 1
  funext i
  exact AM.incidenceCenter_comap_flat_to f I D q (q ≫ f) C E BM hC hD _

end

end OAI.AlgebraicGeometry.Resolution.Blowups
