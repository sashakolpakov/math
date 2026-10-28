import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.UniformIncidencePrefix
import OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceControlPrefix

/-! # Ordered Uniform Incidence Prefix -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The canonical ordered incidence partition gives an actual refinement with constant incidence at every stage. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.uniformBoundaryCompatible_of_incidence_centers
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I J : X.IdealSheafData) (hI : I ≠ ⊥)
    [Smooth (I.subschemeι ≫ f)] [Fintype (irreducibleComponents I.subscheme)]
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    {b N : ℕ} (order : Fin N ≃ Finset β) {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {L : Y.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g L)
    (hP : P.followsCenters (List.ofFn (fun i => Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D (order i)))) :
    P.uniformBoundaryCompatible β D := by
  classical
  let K (i : Fin N) := Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D (order i)
  have hprod : I = ∏ i, K i := by
    change I = ∏ i, Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D (order i)
    rw [order.prod_comp, Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter_product]
  exact Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.uniformBoundaryCompatible_of_finite_disjoint_centers N P I K
    (fun i => Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter_ne_bot f I D hI (order i))
    (fun i j hij => Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter_pairwise f I D (order i) (order j) (fun h => hij (order.injective h)))
    hprod β D A (fun i => order i) (fun j i hp => A.subunion_incidence f I D (order j) i hp) hP

theorem OrderedUniformIncidencePrefix.Construction.exists_ordered_uniform_incidence_control_prefix
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I J : X.IdealSheafData) (hI : I ≠ ⊥)
    [Smooth (I.subschemeι ≫ f)] [Fintype (irreducibleComponents I.subscheme)]
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    (N : ℕ) (order : Fin N ≃ Finset β) (b : ℕ) (hb : 0 < b) (hp : J ≤ I ^ b) :
    ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L : Y.IdealSheafData)
      (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g L) (e : Y ≅ GlobalBlowup.Data.Construction.globalBlowup I hI),
      P.followsCenters (List.ofFn (fun i => Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D (order i))) ∧
        P.uniformBoundaryCompatible β D ∧ P.stepCount = N ∧
          e.hom ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI = P.toBase ∧
            (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b).comap e.hom = L := by
  obtain ⟨Y, g, L, P, e, hP, hn, he, hL⟩ := IncidenceControlPrefix.Construction.exists_ordered_incidence_control_prefix f I J hI D A N order b hb hp
  exact ⟨Y, g, L, P, e, hP, P.uniformBoundaryCompatible_of_incidence_centers f I J hI D A order hP, hn, he, hL⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
