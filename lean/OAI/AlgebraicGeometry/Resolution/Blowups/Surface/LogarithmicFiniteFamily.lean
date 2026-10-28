import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.LogarithmicProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.IncidenceSurfaceExistence

/-! # Logarithmic Finite Family -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface.LogarithmicFiniteFamily.Construction

noncomputable section

section

/-! Every logarithmic surface problem admits a recorded program for all sufficiently large common coefficient levels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem exists_surface_logarithmic_program_threshold
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (n : ℕ)
    (hd : topologicalKrullDim X ≤ 2) {β : Type} [Fintype β]
    (D : β → X.IdealSheafData) (E : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ])
    (G : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (hlog : G.logarithmicIdeal J (n + 1) = ⊤) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
        (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K),
        LogarithmicProgram.Construction.SurfaceLogarithmicProgram n m β X f J D Y g K P := by
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
  obtain ⟨m₀, hB⟩ := A.refined_componentCenter_has_bound hbound e hg hK B
  refine ⟨m₀, ?_⟩
  intro m hm
  have hBm : ∀ i, (B.choice i).HasBound m := fun i => (B.choice i).hasBound_mono (hB i) hm
  obtain ⟨Z, h, L, Q, hQ⟩ := Uniform.IncidenceSurfaceExistence.Construction.exists_uniform_incidence_surface_program m
    Y g K n B hBm (P.endpoint_dimension_le 2 hd) (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels (Fintype.card (Finset β)) β) (P.boundaryAtLength D _ hcount) E' G' hlog'
  exact ⟨Z, h, L, P.append Q, .component A AM P hcenters hcount hP Q hQ⟩

end

/-! A finite family of logarithmic surface problems admits programs with one common coefficient level and common label types. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_finite_surface_logarithmic_programs
    {ι β : Type} [Fintype ι] [Fintype β] (n : ℕ)
    (X : ι → Scheme) [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, CompactSpace (X i)]
    (f : ∀ i, X i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [∀ i, Smooth (f i)] (J : ∀ i, (X i).IdealSheafData)
    (hd : ∀ i, topologicalKrullDim (X i) ≤ 2)
    (D : ∀ i, β → (X i).IdealSheafData)
    (E : ∀ i, Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (f i) (D i) [Finset.univ])
    (G : ∀ i, GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas (f i) (D i))
    (hlog : ∀ i, (G i).logarithmicIdeal (J i) (n + 1) = ⊤) :
    ∃ (m : ℕ) (Y : ι → Scheme) (g : ∀ i, Y i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : ∀ i, (Y i).IdealSheafData)
      (P : ∀ i, Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (X i) (f i) (J i) (Y i) (g i) (K i)),
      ∀ i, LogarithmicProgram.Construction.SurfaceLogarithmicProgram n m β (X i) (f i) (J i) (D i) (Y i) (g i) (K i) (P i) := by
  classical
  choose t ht using fun i => exists_surface_logarithmic_program_threshold
    (f i) (J i) n (hd i) (D i) (E i) (G i) (hlog i)
  let m := Finset.univ.sup t
  have hm : ∀ i, t i ≤ m := fun i => Finset.le_sup (Finset.mem_univ i)
  choose Y g K P T using fun i => ht i m (hm i)
  exact ⟨m, Y, g, K, P, T⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface.LogarithmicFiniteFamily.Construction
