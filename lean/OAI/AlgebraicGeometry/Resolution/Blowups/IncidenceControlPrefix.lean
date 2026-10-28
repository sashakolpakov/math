import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.DisjointControlPrefix
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.BinaryIncidence

/-! # Incidence Control Prefix -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceControlPrefix.Construction

noncomputable section

/-! The constructed boundary-incidence partition supplies an actual finite refinement of a permissible blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem exists_ordered_incidence_control_prefix
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I J : X.IdealSheafData) (hI : I ≠ ⊥)
    [Smooth (I.subschemeι ≫ f)] [Fintype (irreducibleComponents I.subscheme)]
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    (N : ℕ) (order : Fin N ≃ Finset β) (b : ℕ) (hb : 0 < b) (hp : J ≤ I ^ b) :
    ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L : Y.IdealSheafData)
      (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g L) (e : Y ≅ GlobalBlowup.Data.Construction.globalBlowup I hI),
      P.followsCenters (List.ofFn (fun i => Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D (order i))) ∧
        P.stepCount = N ∧ e.hom ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI = P.toBase ∧
          (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b).comap e.hom = L := by
  classical
  let : Smooth f := A.ambient_smooth
  let K (i : Fin N) := Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D (order i)
  have hprod : I = ∏ i, K i := by
    change I = ∏ i, Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D (order i)
    rw [order.prod_comp, Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter_product]
  exact Finite.DisjointControlPrefix.Construction.exists_finite_disjoint_control_prefix N X f J b hb I hI K
    (fun i => Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter_ne_bot f I D hI (order i))
    (fun i => Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter_smooth f I D (order i))
    (fun i j hij => Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter_pairwise f I D (order i) (order j) (fun h => hij (order.injective h)))
    hprod A.center_smooth hp

theorem exists_incidence_control_prefix
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I J : X.IdealSheafData) (hI : I ≠ ⊥)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    (b : ℕ) (hb : 0 < b) (hp : J ≤ I ^ b) :
    ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L : Y.IdealSheafData)
      (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g L) (e : Y ≅ GlobalBlowup.Data.Construction.globalBlowup I hI),
      P.stepCount = 2 ^ Fintype.card β ∧ e.hom ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI = P.toBase ∧
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b).comap e.hom = L := by
  classical
  let : Smooth f := A.ambient_smooth
  let : Smooth (I.subschemeι ≫ f) := A.center_smooth
  let : IsNoetherian X := ⟨⟩
  let : NoetherianSpace I.subscheme := I.subschemeι.isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
  let : Fintype (irreducibleComponents I.subscheme) := Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentFintype I
  let eF := (Fintype.equivFin (Finset β)).symm
  let K (i : Fin (Fintype.card (Finset β))) := Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D (eF i)
  have hprod : I = ∏ i, K i := by
    change I = ∏ i, Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D (eF i)
    rw [eF.prod_comp, Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter_product]
  obtain ⟨Y, g, L, P, e, _, hn, he, hL⟩ := Finite.DisjointControlPrefix.Construction.exists_finite_disjoint_control_prefix _ X f J b hb I hI K
    (fun i => Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter_ne_bot f I D hI (eF i))
    (fun i => Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter_smooth f I D (eF i))
    (fun i j hij => Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter_pairwise f I D (eF i) (eF j) (fun h => hij (eF.injective h)))
    hprod A.center_smooth hp
  exact ⟨Y, g, L, P, e, hn.trans Fintype.card_finset, he, hL⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceControlPrefix.Construction
