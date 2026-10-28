import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.OpenProgramGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.Open.CompatibilityTargetRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.Open.FamilyUnion
import OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceTraceOpenDescent
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ResidualNeighborhoodBoundary

/-! # Order Cover Program Gluing -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Compatible programs on a finite order cover glue with their exact trace and every original comparison map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_complete_of_finite_order_cover
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (hJ : J ≠ ⊥) (b : ℕ)
    {ι : Type} [Finite ι] [Nonempty ι] (U : ι → Scheme) (j : ∀ i, U i ⟶ X)
    [∀ i, IsIntegral (U i)] [∀ i, IsLocallyNoetherian (U i)] [∀ i, CompactSpace (U i)]
    [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (b - 1)).support, ∃ i y, j i y = x)
    (g0 : ∀ i, U i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L0 : ∀ i, (U i).IdealSheafData)
    (hg0 : ∀ i, j i ≫ f = g0 i) (hL0 : ∀ i, J.comap (j i) = L0 i)
    (V : ι → Scheme) (g : ∀ i, V i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : ∀ i, (V i).IdealSheafData)
    (P : ∀ i, Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (U i) (g0 i) (L0 i) (V i) (g i) (K i))
    {β : Type} [Fintype β] (D : β → X.IdealSheafData)
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ]) (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β)
    (htrace : ∀ i, (P i).HasIncidenceTrace β (fun l => (D l).comap (j i)) T)
    (hcompat : ∀ i a, (P i).OpenCompatible (P a) (j i) (j a))
    (ht : ∀ i, letI : Smooth (g i) := (P i).endpoint_smooth
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (g i) (K i) (b - 1) = ⊤) :
    ∃ (Y : Scheme) (h : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L : Y.IdealSheafData)
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y h L) (r : ∀ i, V i ⟶ Y),
      letI : Smooth h := Q.endpoint_smooth
      Q.HasIncidenceTrace β D T ∧ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf h L (b - 1) = ⊤ ∧
        ∀ i, Q.EtaleComparison (P i) (j i) (r i) := by
  classical
  let O := Open.FamilyUnion.Construction.openFamilyUnion U j
  let j0 (i : ι) := Open.FamilyUnion.Construction.openFamilyUnionMap U j i
  let : Nonempty O.toScheme := by
    let i : ι := Classical.arbitrary ι
    let x : U i := Classical.arbitrary (U i)
    exact ⟨j0 i x⟩
  let : IsIntegral O.toScheme := isIntegral_of_isOpenImmersion O.ι
  let : IsLocallyNoetherian O.toScheme := LocallyOfFiniteType.isLocallyNoetherian O.ι
  let : IsNoetherian X := ⟨⟩
  let : NoetherianSpace O.toScheme := O.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : ∀ i, QuasiCompact (j0 i) := fun _ => inferInstance
  have hground (i : ι) : j0 i ≫ (O.ι ≫ f) = g0 i := by
    rw [← Category.assoc, Open.FamilyUnion.Construction.openFamilyUnionMap_over]
    exact hg0 i
  have hlocal (i : ι) : (J.comap O.ι).comap (j0 i) = L0 i := by
    rw [← Scheme.IdealSheafData.comap_comp, Open.FamilyUnion.Construction.openFamilyUnionMap_over]
    exact hL0 i
  have hD (i : ι) : (fun l => ((D l).comap O.ι).comap (j0 i)) =
      (fun l => (D l).comap (j i)) := by
    funext l
    rw [← Scheme.IdealSheafData.comap_comp, Open.FamilyUnion.Construction.openFamilyUnionMap_over]
  have htrace0 (i : ι) : (P i).HasIncidenceTrace β (fun l => ((D l).comap O.ι).comap (j0 i)) T := by
    rw [hD]
    exact htrace i
  have hcompat0 (i a : ι) : (P i).OpenCompatible (P a) (j0 i) (j0 a) := by
    apply Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.OpenCompatible.of_postcomp (j0 i) (j0 a) O.ι
    simpa only [j0, O, Open.FamilyUnion.Construction.openFamilyUnionMap_over] using hcompat i a
  obtain ⟨W, k, M, R, r, hR, hterminal, hr⟩ :=
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_complete_of_finite_open_compatible_named (O.ι ≫ f) (J.comap O.ι) b U j0
      (Open.FamilyUnion.Construction.openFamilyUnionMap_covers U j) g0 L0 hground hlocal V g K P
      (fun l => (D l).comap O.ι) T htrace0 hcompat0 ht
  have hOrder : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (b - 1)).support : Set X) ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]
    intro x hx
    obtain ⟨i, y, hy⟩ := hcover x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, y, hy⟩
  obtain ⟨Y, h, L, Q, s, _, hc, _, hremaining⟩ := R.exists_uniform_extension_from_order_neighborhood
    X f J hJ O.ι rfl rfl hOrder β D A (hR.uniformBoundaryCompatible R _ T)
  let : Smooth h := Q.endpoint_smooth
  refine ⟨Y, h, L, Q, fun i => r i ≫ s, ?_, ?_, ?_⟩
  · exact Q.hasIncidenceTrace_of_order_neighborhood R O.ι s hc hOrder β D A T hR
  · exact hc.terminal_order_of_endpoint_cover Q R O.ι s (b - 1) hremaining hterminal
  · intro i
    have hcomp := hc.comp Q R O.ι s (P i) (j0 i) (r i) (hr i)
    simpa only [j0, O, Open.FamilyUnion.Construction.openFamilyUnionMap_over] using hcomp

end

end OAI.AlgebraicGeometry.Resolution.Blowups
