import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.IncidenceSurfaceProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.Bounds
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.Composition
import OAI.AlgebraicGeometry.Resolution.Blowups.RefinedSurfaceCoefficientBound
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.LogarithmicCenterBoundary

/-! # Incidence Surface Existence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.IncidenceSurfaceExistence.Construction

noncomputable section

/-! Surface logarithmic order reduction by actual prefixes with constant boundary incidence at every center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem exists_uniform_incidence_surface_program (m : ℕ) :
    ∀ (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
      (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (n : ℕ)
      (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n),
      (∀ i, (A.choice i).HasBound m) → topologicalKrullDim X ≤ 2 →
      ∀ (β : Type) [Fintype β] (D : β → X.IdealSheafData)
        (_E : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ]) (G : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D),
      G.logarithmicIdeal J (n + 1) = ⊤ →
      ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
        (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K),
        IncidenceSurfaceProgram.Construction.UniformIncidenceSurfaceProgram n m β X f J D Y g K P := by
  induction m with
  | zero =>
      intro X _ _ _ f _ J n A hb _ β _ D E _ _
      exact ⟨X, f, J, .stop, .terminal (Nat.factorial_pos _) E (A.terminal_of_uniform_bound_lt_factorial hb (Nat.factorial_pos _))⟩
  | succ m ih =>
      intro X _ _ _ f _ J n A hb hd β _ D E G hlog
      classical
      by_cases hlevel : (n + 1).factorial ≤ m + 1
      · have hbound : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (n + 1) = ⊤ :=
          top_le_iff.mp (hlog ▸ G.logarithmicIdeal_le_ordinary J (n + 1))
        let hdA := A.chart_dimension_le 2 hd
        let I := A.surfaceCenter m hb hdA hlevel
        let hI : I ≠ ⊥ := A.surfaceCenter_nonzero m hb hdA hlevel
        let : Smooth (I.subschemeι ≫ f) := A.surfaceCenter_isSmooth m hb hdA hlevel
        let : IsNoetherian X := ⟨⟩
        let : NoetherianSpace I.subscheme := I.subschemeι.isClosedEmbedding.isInducing.noetherianSpace
        let : Fintype (irreducibleComponents I.subscheme) := Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentFintype I
        let AM := A.surfaceBoundaryAtlas_of_log_bound m hb hd hlevel D E G hlog
        let order := (Fintype.equivFin (Finset β)).symm
        obtain ⟨Y, g, K, P, e, hcenters, hP, hcount, he, hK⟩ := OrderedUniformIncidencePrefix.Construction.exists_ordered_uniform_incidence_control_prefix
          f I J hI D AM _ order (n + 1) (Nat.succ_pos n) (A.surfaceCenter_isPermissible m hb hdA hlevel)
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
        have hB := A.refined_surfaceCenter_bound m hb hdA hlevel hbound e hg hK B
        obtain ⟨Z, h, L, Q, hQ⟩ := ih Y g K n B hB (P.endpoint_dimension_le 2 hd)
          (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels (Fintype.card (Finset β)) β) (P.boundaryAtLength D _ hcount) E' G' hlog'
        exact ⟨Z, h, L, P.append Q, .refine A hb hdA hlevel AM P hcenters hcount hP Q hQ⟩
      · exact ⟨X, f, J, .stop, .terminal (Nat.lt_of_not_ge hlevel) E
          (A.terminal_of_uniform_bound_lt_factorial hb (Nat.lt_of_not_ge hlevel))⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.IncidenceSurfaceExistence.Construction
