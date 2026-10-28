import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.DisjointIncidenceTrace
import OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceControlPrefix

/-! # Ordered Incidence Trace -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The canonical ordered incidence partition gives an actual refinement with constant incidence at every stage. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.hasIncidenceTrace_of_incidence_centers
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I J : X.IdealSheafData) (hI : I ≠ ⊥)
    [Smooth (I.subschemeι ≫ f)] [Fintype (irreducibleComponents I.subscheme)]
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    {b N : ℕ} (order : Fin N ≃ Finset β) {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {L : Y.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g L)
    (hP : P.followsCenters (List.ofFn (fun i => Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D (order i)))) :
    P.HasIncidenceTrace β D (Boundary.IncidenceTrace.Construction.disjointBoundaryIncidenceTrace (List.ofFn order)) := by
  classical
  let K (i : Fin N) := Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D (order i)
  have hprod : I = ∏ i, K i := by
    change I = ∏ i, Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D (order i)
    rw [order.prod_comp, Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter_product]
  exact Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.hasIncidenceTrace_of_finite_disjoint_centers N P I K
    (fun i => Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter_ne_bot f I D hI (order i))
    (fun i j hij => Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter_pairwise f I D (order i) (order j) (fun h => hij (order.injective h)))
    hprod β D A (fun i => order i) (fun j i hp => A.subunion_incidence f I D (order j) i hp) hP

end

end OAI.AlgebraicGeometry.Resolution.Blowups
