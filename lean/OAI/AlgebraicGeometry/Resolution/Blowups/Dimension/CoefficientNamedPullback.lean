import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.CoefficientProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.UniformAtlasEtalePullback
import OAI.AlgebraicGeometry.Resolution.Blowups.SameEtalePullbackExistence
import OAI.AlgebraicGeometry.Resolution.Blowups.SameSymmetry

/-! # Coefficient Named Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Dimension

noncomputable section

section

/-! Actual étale restrictions retain complete dimension-indexed coefficient phases and their homogeneous witnesses. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem CoefficientProgram.Construction.DimensionCoefficientProgram.of_etale_comparison
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : 𝒮.Schedule (n + 1).factorial β}
    {X Y V W : Scheme} [CompactSpace V] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData}
    {D : β → X.IdealSheafData} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {K : Y.IdealSheafData} {M : W.IdealSheafData} {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (A : CoefficientProgram.Construction.DimensionCoefficientProgram 𝒮 schedule f J D P) (q : V ⟶ X) [Etale q]
    (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) V (q ≫ f) (J.comap q) W k M)
    (r : W ⟶ Y) (hc : P.EtaleComparison Q q r) :
    CoefficientProgram.Construction.DimensionCoefficientProgram 𝒮 schedule (q ≫ f) (J.comap q) (fun l => (D l).comap q) Q := by
  classical
  refine ⟨hc.hasIncidenceTrace P Q q r β D (𝒮.incidenceTrace schedule) A.trace,
    hc.endpoint_order_bound P Q q r n A.terminal, ?_⟩
  by_cases ht : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (q ≫ f) (J.comap q) n = ⊤
  · exact Or.inl ht
  rcases A.witness with hstart | ⟨L, R, ⟨AR⟩, same⟩
  · apply False.elim
    apply ht
    rw [← Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothDifferentialIdealSheaf_comap_etale, hstart, Scheme.IdealSheafData.comap_top]
  · obtain ⟨L', R', same', hR'⟩ := same.symm.exists_etale_pullback_transport Q q r hc
      (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf (q ≫ f) (J.comap q) n) (Global.HomogenizationEtalePullback.Construction.smoothHomogenizedIdealSheaf_comap_etale f J n q)
    obtain ⟨AR'⟩ := AR.exists_on_etale_comparison q R' r hR' ht
    exact Or.inr ⟨L', R', ⟨AR'⟩, same'.symm⟩

theorem CoefficientProgram.Construction.DimensionCoefficientProgram.exists_etaleComparison
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : 𝒮.Schedule (n + 1).factorial β}
    {X Y V W : Scheme} [IsIntegral V] [IsLocallyNoetherian V] [CompactSpace V]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth h]
    {J : X.IdealSheafData} {L : V.IdealSheafData} {D : β → X.IdealSheafData} {E : β → V.IdealSheafData}
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData} {M : W.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K} {Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) V h L W k M}
    (A : CoefficientProgram.Construction.DimensionCoefficientProgram 𝒮 schedule f J D P) (B : CoefficientProgram.Construction.DimensionCoefficientProgram 𝒮 schedule h L E Q)
    (q : V ⟶ X) [Etale q] (hf : q ≫ f = h) (hJ : J.comap q = L) (hD : ∀ l, (D l).comap q = E l) :
    ∃ r : W ⟶ Y, P.EtaleComparison Q q r := by
  subst h
  subst L
  have he : (fun l => (D l).comap q) = E := funext hD
  subst E
  obtain ⟨Z, z, N, R, r, hr⟩ := P.exists_etale_pullback V (q ≫ f) (J.comap q) q rfl rfl
  have AR := A.of_etale_comparison q R r hr
  obtain ⟨e, he, _⟩ := AR.exists_endpointIso B
  refine ⟨e.hom ≫ r, ?_⟩
  simpa only [Category.id_comp] using hr.comp P R q r Q (𝟙 V) e.hom he

end

/-! Coefficient programs have actual pullbacks with independently named structure maps, ideals, and labelled boundaries. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem CoefficientProgram.Construction.DimensionCoefficientProgram.exists_etale_pullback
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : 𝒮.Schedule (n + 1).factorial β}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (A : CoefficientProgram.Construction.DimensionCoefficientProgram 𝒮 schedule f J D P)
    (V : Scheme) [IsIntegral V] [IsLocallyNoetherian V] [CompactSpace V]
    (h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth h] (L : V.IdealSheafData) (E : β → V.IdealSheafData)
    (q : V ⟶ X) [Etale q] (hf : q ≫ f = h) (hJ : J.comap q = L) (hD : ∀ l, (D l).comap q = E l) :
    ∃ (W : Scheme) (k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (M : W.IdealSheafData)
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) V h L W k M) (r : W ⟶ Y),
      CoefficientProgram.Construction.DimensionCoefficientProgram 𝒮 schedule h L E Q ∧ P.EtaleComparison Q q r := by
  subst h
  subst L
  have he : (fun l => (D l).comap q) = E := funext hD
  subst E
  obtain ⟨W, k, M, Q, r, hc⟩ := P.exists_etale_pullback V (q ≫ f) (J.comap q) q rfl rfl
  exact ⟨W, k, M, Q, r, A.of_etale_comparison q Q r hc, hc⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Dimension
