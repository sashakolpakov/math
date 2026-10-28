import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.OpenControlPrefixGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.EndpointOpenCover
import OAI.AlgebraicGeometry.Resolution.Blowups.TraceOpenCoverDescent

/-! # Open Program Gluing -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

section

/-! Complete compatible local programs construct one complete global program with the same exact trace. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_complete_of_finite_open_compatible
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (b : ℕ)
    {ι : Type} [Finite ι] (U : ι → Scheme) (j : ∀ i, U i ⟶ X)
    [∀ i, IsIntegral (U i)] [∀ i, IsLocallyNoetherian (U i)]
    [∀ i, IsOpenImmersion (j i)] [∀ i, QuasiCompact (j i)]
    (hcover : ∀ x : X, ∃ i y, j i y = x)
    (V : ι → Scheme) (g : ∀ i, V i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : ∀ i, (V i).IdealSheafData)
    (P : ∀ i, Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (U i) (j i ≫ f) (J.comap (j i)) (V i) (g i) (K i))
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β)
    (htrace : ∀ i, (P i).HasIncidenceTrace β (fun l => (D l).comap (j i)) T)
    (hcompat : ∀ i a, (P i).OpenCompatible (P a) (j i) (j a))
    (ht : ∀ i, letI : Smooth (g i) := (P i).endpoint_smooth
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (g i) (K i) (b - 1) = ⊤) :
    ∃ (Y : Scheme) (h : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L : Y.IdealSheafData)
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y h L) (r : ∀ i, V i ⟶ Y),
      letI : Smooth h := Q.endpoint_smooth
      Q.HasIncidenceTrace β D T ∧ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf h L (b - 1) = ⊤ ∧
        ∀ i, Q.EtaleComparison (P i) (j i) (r i) := by
  have hN := fun i => (htrace i).stepCount (P i) (fun l => (D l).comap (j i)) T
  obtain ⟨Y, h, L, Q, r, hr⟩ := Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_of_finite_open_compatible b T.length X f J ι U j hcover
    (fun i => j i ≫ f) (fun i => J.comap (j i)) (fun _ => rfl) (fun _ => rfl)
    V g K P hN hcompat
  let : Smooth h := Q.endpoint_smooth
  refine ⟨Y, h, L, Q, r, ?_, ?_, hr⟩
  · exact Q.hasIncidenceTrace_of_open_comparisons ι U j hcover
      (fun i => j i ≫ f) (fun i => J.comap (j i)) V g K P r hr β D T htrace
  · exact Q.terminal_order_of_open_comparisons U j hcover
      (fun i => j i ≫ f) (fun i => J.comap (j i)) V g K P r hr (b - 1) ht

end

/-! Complete finite open gluing retains independently named local structures and ideals. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_complete_of_finite_open_compatible_named
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (b : ℕ)
    {ι : Type} [Finite ι] (U : ι → Scheme) (j : ∀ i, U i ⟶ X)
    [∀ i, IsIntegral (U i)] [∀ i, IsLocallyNoetherian (U i)]
    [∀ i, IsOpenImmersion (j i)] [∀ i, QuasiCompact (j i)]
    (hcover : ∀ x : X, ∃ i y, j i y = x)
    (g0 : ∀ i, U i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L0 : ∀ i, (U i).IdealSheafData)
    (hg0 : ∀ i, j i ≫ f = g0 i) (hL0 : ∀ i, J.comap (j i) = L0 i)
    (V : ι → Scheme) (g : ∀ i, V i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : ∀ i, (V i).IdealSheafData)
    (P : ∀ i, Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (U i) (g0 i) (L0 i) (V i) (g i) (K i))
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β)
    (htrace : ∀ i, (P i).HasIncidenceTrace β (fun l => (D l).comap (j i)) T)
    (hcompat : ∀ i a, (P i).OpenCompatible (P a) (j i) (j a))
    (ht : ∀ i, letI : Smooth (g i) := (P i).endpoint_smooth
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (g i) (K i) (b - 1) = ⊤) :
    ∃ (Y : Scheme) (h : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L : Y.IdealSheafData)
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y h L) (r : ∀ i, V i ⟶ Y),
      letI : Smooth h := Q.endpoint_smooth
      Q.HasIncidenceTrace β D T ∧ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf h L (b - 1) = ⊤ ∧
        ∀ i, Q.EtaleComparison (P i) (j i) (r i) := by
  have hN := fun i => (htrace i).stepCount (P i) (fun l => (D l).comap (j i)) T
  obtain ⟨Y, h, L, Q, r, hr⟩ := Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_of_finite_open_compatible b T.length X f J ι U j hcover
    g0 L0 hg0 hL0 V g K P hN hcompat
  let : Smooth h := Q.endpoint_smooth
  exact ⟨Y, h, L, Q, r,
    Q.hasIncidenceTrace_of_open_comparisons ι U j hcover g0 L0 V g K P r hr β D T htrace,
    Q.terminal_order_of_open_comparisons U j hcover g0 L0 V g K P r hr (b - 1) ht, hr⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
