import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.LogarithmicFiniteFamily

/-! # Bounded Component -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.BoundedComponent.Construction

noncomputable section

/-! Canonical component clearing produces a bounded coefficient problem with its complete labelled prefix retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

structure BoundedComponentPrefix {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (J : X.IdealSheafData) (n : ℕ) {β : Type} [Fintype β]
    (D : β → X.IdealSheafData) where
  initialAtlas : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n
  centerAtlas : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f initialAtlas.center D
  endpoint : Scheme
  structureMap : endpoint ⟶ Foundations.Scheme.ProjectiveSpace.complexBase
  ideal : endpoint.IdealSheafData
  program : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J endpoint structureMap ideal
  centers : program.followsCenters (initialAtlas.componentIncidenceCenters D)
  count : program.stepCount = Fintype.card (Finset β)
  uniform : program.uniformBoundaryCompatible β D
  boundaryAtlas : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas structureMap (program.boundaryAtLength D _ count) [Finset.univ]
  model : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas structureMap (program.boundaryAtLength D _ count)
  logarithmic : model.logarithmicIdeal ideal (n + 1) = ⊤
  coefficientAtlas : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas structureMap ideal n
  bound : ℕ
  coefficientBound : ∀ a, (coefficientAtlas.choice a).HasBound bound

theorem exists_bounded_component_prefix
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (n : ℕ) {β : Type} [Fintype β]
    (D : β → X.IdealSheafData) (E : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ])
    (G : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (hlog : G.logarithmicIdeal J (n + 1) = ⊤) :
    Nonempty (BoundedComponentPrefix f J n D) := by
  classical
  have hbound : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (n + 1) = ⊤ :=
    top_le_iff.mp (hlog ▸ G.logarithmicIdeal_le_ordinary J (n + 1))
  obtain ⟨A⟩ := GlobalComponent.ChoiceAtlas.Construction.exists_global_component_choice_atlas f J n hbound
  let I := A.center
  let hI : I ≠ ⊥ := A.center_ne_bot
  let : Smooth (I.subschemeι ≫ f) := A.center_smooth
  let : IsNoetherian X := ⟨⟩
  let : NoetherianSpace I.subscheme := I.subschemeι.isClosedEmbedding.isInducing.noetherianSpace
  let : Fintype (irreducibleComponents I.subscheme) := Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentFintype I
  let AM := A.componentBoundaryAtlas_of_log_bound D E G hlog
  let order := (Fintype.equivFin (Finset β)).symm
  obtain ⟨Y, g, K, P, e, hcenters, hP, hcount, he, hK⟩ := OrderedUniformIncidencePrefix.Construction.exists_ordered_uniform_incidence_control_prefix
    f I J hI D AM _ order (n + 1) (Nat.succ_pos n) A.center_permissible
  let : Smooth g := P.endpoint_smooth
  let : IsIntegral Y := P.endpoint_integral
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace P.toBase
  have hPB := Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.uniformBoundaryCompatible.boundaryCompatible P D hP
  obtain ⟨E'⟩ := P.boundaryAtLength_atlas D hPB _ hcount
  obtain ⟨G', hlog'⟩ := P.exists_fixed_length_logarithmic_bound D hPB G hlog _ hcount
  have hbound' : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K (n + 1) = ⊤ :=
    top_le_iff.mp (hlog' ▸ G'.logarithmicIdeal_le_ordinary K (n + 1))
  obtain ⟨B⟩ := GlobalComponent.ChoiceAtlas.Construction.exists_global_component_choice_atlas g K n hbound'
  have hg : e.hom ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) = g := by
    rw [← Category.assoc, he, P.over]
  obtain ⟨m, hB⟩ := A.refined_componentCenter_has_bound hbound e hg hK B
  exact ⟨⟨A, AM, Y, g, K, P, hcenters, hcount, hP, E', G', hlog', B, m, hB⟩⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.BoundedComponent.Construction
